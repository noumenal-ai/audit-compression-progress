"""Measure L_B(theta_0): the initial audit level of the C1 run on the sealed panel B.

The C1 shards (`results_data/c1_seed<S>.json`) report only the TERMINAL audit level
`final_fresh_floored_ce` = L_B(theta_T). The signed gain

    G = L_B(theta_0) - L_B(theta_T)

therefore needs the INITIAL level as well, and that is what this script measures: the
floored cross-entropy of the freshly initialised, untrained network on the same sealed
panel B, for each of the 20 camera-ready seeds.

Why this is a fixed-model measurement
-------------------------------------
Panel B (`panel(seed + 2000, ...)`, PROTOCOL 8.3) is scored exactly ONCE per run, after
the last training step, at `cp_experiments.run_c1` line ~171. It never enters the reward
loop: the per-step audit-CP reward reads the disjoint probe panel A (`seed + 1000`), and
C1 has no early stopping, no checkpoint selection, and no hyperparameter or data selection
driven by any panel-B score. Panel B produced no signal that influenced training, so the
fixed-panel slack route applies with a declared candidate count of N = 1 rather than the
transcript-bit route.

theta_0 is well defined and policy-independent: `run_c1` calls `torch.manual_seed(cfg.seed)`
immediately before `make_model` for every policy, so all seven C1 policies start from the
same initial weights for a given seed. This script reproduces exactly that prefix of
`run_c1` -- same Cfg, same panel construction, same model constructor, same loss -- and
stops before the first optimiser step.

The independent audit unit is the EXAMPLE (one padded 30x30 ARC-TGI grid), not the cell.
Cells inside one grid are dependent, so n = 12288 examples is the conservative count.

What the archived level is, and what prices it
----------------------------------------------
`audit_panel_loss` returns `floored_ce` = (total floored CE over every content cell of the
panel) / (total content cells). That is a CONTENT-CELL-WEIGHTED ratio, sum_i w_i m_i with
w_i = c_i / sum_j c_j; ARC-TGI grids run from 1x1 to 30x30, so the weights vary. Hoeffding for
a weighted mean of n bounded terms gives radius R*sqrt(sum_i w_i^2 * ln(2N/delta) / 2), which is
the unweighted radius R*sqrt(ln(2N/delta)/(2n)) inflated by sqrt(n/n_eff) with

    n_eff = 1 / sum_i w_i^2 = (sum_i c_i)^2 / sum_i c_i^2 <= n     (Cauchy-Schwarz).

The slack in this record is therefore priced at n_eff, not at n. The unweighted radius is kept
under `aggregate.unweighted_reference` for comparison only; it prices nothing here.

The cell counts are recoverable exactly: panel B is a deterministic function of the seed
(`panel(seed + 2000, ...)`), and a re-measure reproduces the archived L0 to the last bit, which
is the proof that the regenerated panel is the panel the archived levels were scored on. Every
row therefore carries `sum_cells`, `sum_cells_sq` and `n_effective`, and the aggregate refuses
to run on a row that lacks them. `L0_unweighted`, the unweighted mean of per-record means, is
stored beside `L0` for reference; the C1 shards hold no unweighted terminal level, so the
unweighted five numbers cannot be formed from this record and are not reported.

Headline convention: the aggregate slack is the single-panel slack at the mean n_eff over seeds,
and each per-seed lower bound is priced at that seed's own n_eff. Neither is a simultaneous
statement across seeds.


Usage
-----
    export ARC_TGI_ROOT=/path/to/simon-arc-lab      # pinned commit d8a2621, see README
    python3 c1_panelB_initial_loss.py               # measure all 20 seeds, then aggregate
    python3 c1_panelB_initial_loss.py --seeds 0,1   # measure a subset (resumes; keeps the rest)
    python3 c1_panelB_initial_loss.py --aggregate-only   # recompute the aggregate block only

Writes `results_data/c1_panelB_initial_loss.json`, saving after every seed so an
interrupted run resumes.

The terminal levels L_B(theta_T) are read back from the C1 shards in
`results_data/c1_seed<S>.json`.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import traceback
from pathlib import Path
from typing import Dict, List, Optional

HERE = Path(__file__).resolve().parent
RESULTS_DIR = HERE / "results_data"
OUT_JSON = RESULTS_DIR / "c1_panelB_initial_loss.json"

sys.path.insert(0, str(HERE))

SEEDS = list(range(20))

# Slack route (c): fixed panel, declared finite candidate set.
EPS = 0.01                      # probability floor of the audit loss
R = -math.log(EPS)              # loss range, 4.605170185988091 nats
DELTA = 0.05                    # confidence parameter
CARD_A = 1                      # N: declared candidate count (one pre-declared endpoint pair)
N_EXPECTED = 12288              # independent audit units (examples, not cells)

# The paper's reported values, asserted at the end of every run.
VALIDATION_TARGET = {
    "n_effective": 6521.8,
    "Delta": 0.077445,
    "slack_Gamma": 0.154891,
    "mean_L0": 2.4841,
    "mean_LT": 1.7476,
    "mean_G": 0.7366,
    "lower_bound_on_improvement": 0.5817,
    "discrimination_ratio": 4.76,
    "per_seed_lower_bound_min": 0.4844,
    "per_seed_lower_bound_max": 0.6561,
    "per_seed_positive_count": 20,
}


# -----------------------------------------------------------------------------
# terminal levels L_B(theta_T), read back from the C1 shards
# -----------------------------------------------------------------------------

def load_LT(seed: int) -> float:
    """Terminal audit level of the audit_cp policy on panel B, from the C1 shard."""
    loose = RESULTS_DIR / f"c1_seed{seed}.json"
    if not loose.exists():
        raise FileNotFoundError(f"no C1 shard for seed {seed}: expected {loose}")
    shard = json.loads(loose.read_text())
    return float(shard["c1"]["by_policy"]["audit_cp"]["final_fresh_floored_ce"])


# -----------------------------------------------------------------------------
# initial levels L_B(theta_0), measured
# -----------------------------------------------------------------------------

def measure_L0(seed: int) -> Dict:
    """Reproduce the run_c1 prefix for `seed` and score theta_0 on the sealed panel B."""
    import torch
    import cp_experiments as X
    import cp_models as M

    cfg = X.Cfg.from_scale("full", seed=seed)
    learn = X.crt.LEARNABLE_TASKS

    B = X.panel(cfg.seed + 2000, cfg.audit_per_family, cfg.grid, learn)   # sealed panel
    n_panel = int(B[0].shape[0])

    torch.manual_seed(cfg.seed)                                           # exactly as run_c1
    model = X.make_model(cfg.model, len(X.crt.TASKS), cfg.grid)           # theta_0, untrained

    ap = M.audit_panel_loss(model, B, X.DEV, eps=EPS)
    L0 = float(ap["floored_ce"])                    # the archived, cell-weighted level
    LT = load_LT(seed)
    # No timings in the record: the schema is exactly the measurement, so a re-run on any
    # machine reproduces this file rather than producing a diff of wall-clock noise.
    row = {
        "status": "ok", "seed": seed, "n_panel": n_panel,
        "L0": L0, "LT": LT, "G": L0 - LT,
        "cfg": {"grid": cfg.grid, "audit_per_family": cfg.audit_per_family,
                "steps": cfg.steps, "batch": cfg.batch, "model": cfg.model},
    }
    # The unweighted level (reference) and the effective sample size that prices the weighted one.
    if "floored_ce_per_example" in ap:
        row["L0_unweighted"] = float(ap["floored_ce_per_example"])
    for key in ("sum_cells", "sum_cells_sq", "n_effective"):
        if key in ap:
            row[key] = float(ap[key])
    return row


# -----------------------------------------------------------------------------
# aggregate: route (c) slack, lower bound on improvement, discrimination ratio
# -----------------------------------------------------------------------------

def _mean(xs: List[float]) -> float:
    return sum(xs) / len(xs)


def _sd(xs: List[float]) -> float:
    """Sample standard deviation, ddof=1."""
    if len(xs) < 2:
        return 0.0
    m = _mean(xs)
    return math.sqrt(sum((x - m) ** 2 for x in xs) / (len(xs) - 1))


def route_c_slack(n: int, card_A: int = CARD_A, eps: float = EPS,
                  delta: float = DELTA) -> Dict[str, float]:
    """Fixed-panel slack. Uses the repo's own audited formula when importable.

        Delta = R * sqrt( ln(2N/delta) / (2n) ),   Gamma = 2 * Delta

    The factor of two is two-sided over the endpoints: an upper deviation at theta_0 and a
    lower one at theta_T.
    """
    try:
        import cp_models as M
        Delta = float(M.delta_n(card_A, n, eps=eps, delta=delta))
    except Exception:                                     # torch-free fallback
        Delta = (-math.log(eps)) * math.sqrt(math.log(2.0 * card_A / delta) / (2.0 * n))
    return {"Delta": Delta, "slack_Gamma": 2.0 * Delta}


def route_c_slack_at(n_priced: float, card_A: int = CARD_A, eps: float = EPS,
                     delta: float = DELTA) -> Dict[str, float]:
    """Fixed-panel slack priced at `n_priced` bounded terms.

        Delta = R * sqrt( ln(2N/delta) / (2 n_priced) ),   Gamma = 2 * Delta

    For an unweighted mean n_priced is the record count n. For the archived cell-weighted
    ratio it is n_eff = (sum_i c_i)^2 / sum_i c_i^2, Hoeffding's sample size for a weighted mean.
    """
    Delta = (-math.log(eps)) * math.sqrt(math.log(2.0 * card_A / delta) / (2.0 * n_priced))
    return {"Delta": Delta, "slack_Gamma": 2.0 * Delta}


def aggregate(per_seed: Dict[str, Dict]) -> Dict:
    seeds = sorted(int(k) for k in per_seed)
    rows = [per_seed[str(s)] for s in seeds]

    n_panels = sorted({int(r["n_panel"]) for r in rows})
    if len(n_panels) != 1:
        raise ValueError(f"seeds disagree on panel size: {n_panels}")
    n = n_panels[0]
    if n != N_EXPECTED:
        print(f"WARNING: panel size {n} != the camera-ready {N_EXPECTED}", file=sys.stderr)

    missing = [r["seed"] for r in rows if "n_effective" not in r]
    if missing:
        raise ValueError(
            "rows without n_effective: %s. The archived level is a cell-weighted ratio and is "
            "priced at n_eff; re-measure these seeds with "
            "`python3 c1_panelB_initial_loss.py --force --seeds %s`."
            % (missing, ",".join(str(s) for s in missing)))

    L0 = [r["L0"] for r in rows]
    LT = [r["LT"] for r in rows]
    G = [r["G"] for r in rows]
    n_eff_rows = [float(r["n_effective"]) for r in rows]
    n_eff = _mean(n_eff_rows)

    # Headline: the single-panel slack at the mean effective size.
    sl = route_c_slack_at(n_eff)
    Gamma = sl["slack_Gamma"]
    mean_G = _mean(G)

    # Per seed: each panel is its own draw and is priced at its own n_eff.
    per_seed_slack = [route_c_slack_at(x)["slack_Gamma"] for x in n_eff_rows]
    per_seed_lb = [g - s for g, s in zip(G, per_seed_slack)]
    per_seed_ratio = [g / s for g, s in zip(G, per_seed_slack)]

    # Reference only: the radius the same panel would give an unweighted mean of n records.
    sl_unw = route_c_slack(n)

    # The n_eff below which the sign of the headline bound would go.
    n_eff_needed = int(math.ceil(2.0 * R * R * math.log(2.0 * CARD_A / DELTA) / (mean_G ** 2)))

    L0_unw = [float(r["L0_unweighted"]) for r in rows if "L0_unweighted" in r]

    return {
        "n_seeds": len(seeds),
        "seeds": seeds,
        "n_independent_audit_units": n,
        "independent_unit": "example (one padded 30x30 ARC-TGI grid); NOT the cell",
        "estimator": "content_cell_weighted_ratio",
        "delta": DELTA,
        "candidate_set_size_N": CARD_A,
        "loss_range_R": R,
        "slack_route": "c",
        "n_effective": n_eff,
        "n_effective_per_seed": {"min": min(n_eff_rows), "max": max(n_eff_rows),
                                 "mean": n_eff, "sd": _sd(n_eff_rows),
                                 "values": {str(s): x for s, x in zip(seeds, n_eff_rows)}},
        "n_effective_definition": "(sum_i c_i)^2 / sum_i c_i^2 over the content-cell counts c_i of the panel's n records",
        "priced_at": ("n_effective: the headline Delta and slack are the single-panel values at the "
                      "mean n_eff over seeds; per-seed bounds are priced at each seed's own n_eff"),
        "Delta": sl["Delta"],
        "slack_Gamma": Gamma,
        "unweighted_reference": {
            "Delta": sl_unw["Delta"], "slack_Gamma": sl_unw["slack_Gamma"],
            "note": ("the radius of an unweighted mean of n records, for comparison only; it is "
                     "not the radius of the archived estimator and prices nothing in this record")},
        "L0": {"mean": _mean(L0), "sd": _sd(L0), "min": min(L0), "max": max(L0)},
        "LT": {"mean": _mean(LT), "sd": _sd(LT), "min": min(LT), "max": max(LT)},
        "G": {"mean": mean_G, "sd": _sd(G), "min": min(G), "max": max(G)},
        "L0_unweighted": ({"mean": _mean(L0_unw), "sd": _sd(L0_unw), "min": min(L0_unw),
                           "max": max(L0_unw),
                           "note": ("unweighted mean of per-record means at theta_0, for reference; "
                                    "no unweighted terminal level exists in the C1 shards, so no "
                                    "unweighted gain or bound is formed")}
                          if len(L0_unw) == len(rows) else None),
        "lower_bound_on_improvement": mean_G - Gamma,
        "discrimination_ratio": mean_G / Gamma,
        "bound_reading": (
            "mean gain over seeds less the single-panel slack at the mean n_eff; positive, so the "
            "run has improved on the sealed panel by at least this much at confidence 1 - delta"),
        "n_effective_required_for_positive_bound": n_eff_needed,
        "n_effective_required_note": (
            "the headline bound is positive for every n_eff above this; the measured n_eff is "
            "%.1f, %.0f times the threshold" % (n_eff, n_eff / max(n_eff_needed, 1))),
        "per_seed_slack": {"min": min(per_seed_slack), "max": max(per_seed_slack)},
        "per_seed_lower_bound": {
            "min": min(per_seed_lb),
            "max": max(per_seed_lb),
            "positive_count": sum(1 for v in per_seed_lb if v > 0),
            "values": {str(s): v for s, v in zip(seeds, per_seed_lb)},
            "note": ("each seed draws its own independent panel B and is priced at its own n_eff; "
                     "this is the single-seed statement at delta=0.05 applied seed by seed, not a "
                     "simultaneous 95% statement across all 20 seeds"),
        },
        "per_seed_discrimination_ratio": {"min": min(per_seed_ratio), "max": max(per_seed_ratio)},
    }


def check_validation_target(agg: Dict) -> bool:
    """Assert the aggregate reproduces the values reported in the paper."""
    got = {
        "n_effective": agg["n_effective"],
        "Delta": agg["Delta"],
        "slack_Gamma": agg["slack_Gamma"],
        "mean_L0": agg["L0"]["mean"],
        "mean_LT": agg["LT"]["mean"],
        "mean_G": agg["G"]["mean"],
        "lower_bound_on_improvement": agg["lower_bound_on_improvement"],
        "discrimination_ratio": agg["discrimination_ratio"],
        "per_seed_lower_bound_min": agg["per_seed_lower_bound"]["min"],
        "per_seed_lower_bound_max": agg["per_seed_lower_bound"]["max"],
        "per_seed_positive_count": agg["per_seed_lower_bound"]["positive_count"],
    }
    ok = True
    print("\n--- validation against the reported values ---")
    for k, want in VALIDATION_TARGET.items():
        have = got[k]
        if k == "per_seed_positive_count":
            hit = int(have) == int(want)
            print(f"  {k:34s} want {want}  got {have}   {'OK' if hit else 'MISMATCH'}")
        else:
            # the target is quoted rounded; compare at the quoted precision
            ndp = len(str(want).split(".")[1])
            hit = round(have, ndp) == want
            print(f"  {k:34s} want {want}  got {round(have, ndp)}"
                  f"   {'OK' if hit else 'MISMATCH'}")
        ok = ok and hit
    print("--- ALL VALUES REPRODUCE ---" if ok else
          "--- MISMATCH: the aggregate does NOT reproduce the reported values ---")
    return ok


# -----------------------------------------------------------------------------

def load_existing() -> Dict[str, Dict]:
    if OUT_JSON.exists():
        try:
            return json.loads(OUT_JSON.read_text()).get("per_seed", {})
        except Exception:
            return {}
    return {}


def write_out(per_seed: Dict[str, Dict], agg: Optional[Dict]) -> None:
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    doc = {
        "measurement": "L_B(theta_0): audit level of the untrained model on the sealed panel B",
        "experiment": "c1",
        "policy": "audit_cp",
        "scale": "full",
        "loss": {
            "name": "floored cross-entropy, content cells only (pad token excluded)",
            "units": "nats",
            "eps": EPS,
            "range_R": R,
            "estimator": "content_cell_weighted_ratio",
            "estimator_definition": (
                "sum over panel content cells of the floored CE, divided by the total content-cell "
                "count: a weighted mean of the per-example means with weights proportional to each "
                "example's content-cell count, not their unweighted mean"),
            "n_effective": (agg["n_effective"] if agg is not None else None),
            "priced_at": "n_effective; see aggregate.priced_at",
        },
        "panel": {
            "name": "B",
            "construction": "panel(seed + 2000, audit_per_family=512, grid=30, LEARNABLE_TASKS)",
            "sealed": True,
            "scored_during_training": False,
            "why_fixed_model": (
                "Panel B is scored once, after the final training step. The per-step "
                "audit-CP reward reads the disjoint probe panel A (seed + 1000); C1 has no "
                "early stopping, no checkpoint selection, and no hyperparameter or data "
                "selection driven by a panel-B score. The panel produced no signal that "
                "influenced training, so the fixed-panel route applies with N = 1 and the "
                "reused-panel transcript-bit route is not needed."),
        },
        "theta_0": (
            "freshly initialised network, zero optimiser steps; run_c1 re-seeds torch "
            "immediately before make_model, so all seven C1 policies share theta_0 at a "
            "given seed"),
        "theta_T": (
            "the audit_cp policy after 5000 steps; L_B(theta_T) is read back from "
            "results_data/c1_seed<S>.json -> c1.by_policy.audit_cp.final_fresh_floored_ce"),
        "fields": {
            "L0": "L_B(theta_0), the initial audit level, content-cell-weighted",
            "LT": "L_B(theta_T), the terminal audit level, content-cell-weighted",
            "G": "signed gain L0 - LT",
            "n_panel": "independent audit units in panel B (examples, not cells)",
            "L0_unweighted": ("L_B(theta_0) as the unweighted mean of per-example means, for "
                              "reference; the C1 shards hold no unweighted terminal level"),
            "sum_cells": "sum_i c_i, content cells in panel B",
            "sum_cells_sq": "sum_i c_i^2",
            "n_effective": "(sum_i c_i)^2 / sum_i c_i^2; the sample size the slack is priced at",
        },
        "generated_by": "experiments/c1_panelB_initial_loss.py",
        "per_seed": {str(s): per_seed[str(s)] for s in sorted(int(k) for k in per_seed)},
    }
    if agg is not None:
        doc["aggregate"] = agg
    OUT_JSON.write_text(json.dumps(doc, indent=2) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--seeds", default=None,
                    help="comma list of seeds to (re)measure; default all 20")
    ap.add_argument("--aggregate-only", action="store_true",
                    help="recompute the aggregate block from the stored per-seed values")
    ap.add_argument("--force", action="store_true",
                    help="re-measure seeds already present instead of skipping them")
    args = ap.parse_args()

    per_seed = load_existing()

    if not args.aggregate_only:
        want = SEEDS if args.seeds is None else [int(x) for x in args.seeds.split(",")]
        for s in want:
            key = str(s)
            if not args.force and per_seed.get(key, {}).get("status") == "ok":
                r = per_seed[key]
                print(f"[seed {s}] already measured, skipping "
                      f"(L0={r['L0']:.6f} LT={r['LT']:.6f} G={r['G']:.6f})", flush=True)
                continue
            try:
                rec = measure_L0(s)
                per_seed[key] = rec
                print(f"[seed {s}] OK  n_panel={rec['n_panel']}  L0={rec['L0']:.6f}  "
                      f"LT={rec['LT']:.6f}  G={rec['G']:.6f}", flush=True)
            except Exception as e:
                per_seed[key] = {"status": "error", "seed": s, "error": str(e),
                                 "traceback": traceback.format_exc()}
                print(f"[seed {s}] ERROR: {e}", flush=True)
                traceback.print_exc()
            write_out(per_seed, None)                 # persist after every seed

    ok_rows = {k: v for k, v in per_seed.items() if v.get("status") == "ok"}
    if not ok_rows:
        print("no completed seeds; nothing to aggregate", file=sys.stderr)
        return 1
    if len(ok_rows) < len(SEEDS):
        print(f"WARNING: aggregating over {len(ok_rows)}/{len(SEEDS)} seeds", file=sys.stderr)

    agg = aggregate(ok_rows)
    write_out(per_seed, agg)

    print(f"\nwrote {OUT_JSON}")
    print(f"  n = {agg['n_independent_audit_units']} independent audit units, "
          f"R = {agg['loss_range_R']:.9f}, delta = {agg['delta']}, N = {agg['candidate_set_size_N']}")
    print(f"  n_eff = {agg['n_effective']:.1f} (per seed {agg['n_effective_per_seed']['min']:.1f}"
          f" .. {agg['n_effective_per_seed']['max']:.1f})")
    print(f"  Delta = {agg['Delta']:.6f}   slack Gamma = {agg['slack_Gamma']:.6f}   "
          f"(unweighted reference {agg['unweighted_reference']['slack_Gamma']:.6f})")
    print(f"  mean L0 = {agg['L0']['mean']:.4f} (sd {agg['L0']['sd']:.4f})")
    print(f"  mean LT = {agg['LT']['mean']:.4f} (sd {agg['LT']['sd']:.4f})")
    print(f"  mean G  = {agg['G']['mean']:.4f} (sd {agg['G']['sd']:.4f})")
    print(f"  lower bound on improvement = {agg['lower_bound_on_improvement']:.4f}")
    print(f"  discrimination ratio       = {agg['discrimination_ratio']:.2f}")
    print(f"  per-seed lower bounds {agg['per_seed_lower_bound']['min']:.4f} .. "
          f"{agg['per_seed_lower_bound']['max']:.4f}, positive in "
          f"{agg['per_seed_lower_bound']['positive_count']}/{agg['n_seeds']} seeds")

    return 0 if check_validation_target(agg) else 2


if __name__ == "__main__":
    raise SystemExit(main())
