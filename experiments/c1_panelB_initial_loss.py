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

What the archived level is, and what route (c) prices
-----------------------------------------------------
`audit_panel_loss` returns `floored_ce` = (total floored CE over every content cell of the
panel) / (total content cells). That is a CONTENT-CELL-WEIGHTED ratio, sum_i w_i m_i with
w_i = c_i / sum_j c_j; it computes no per-example value, and ARC-TGI grids run from 1x1 to
30x30, so the weights vary. Route (c)'s radius Delta = R*sqrt(ln(2N/delta)/(2n)) is Hoeffding
for the UNWEIGHTED mean of n bounded terms. For the weighted level the radius is
Delta*sqrt(n/n_eff) with n_eff = (sum_i c_i)^2 / sum_i c_i^2 <= n, so the published Delta is
too small for it, always in the same direction.

The archived L0/LT values in this file are the cell-weighted level, measured before
`audit_panel_loss` reported anything else, and no cell counts were stored, so n_eff cannot be
recovered from the record. What the record does fix is the threshold: the reported gain stays
above the corrected slack for every n_eff above 2*R^2*ln(2N/delta)/G^2, which the aggregate
block below computes and stores as `n_effective_required_for_positive_bound`.

A re-run of this script now measures both levels and n_eff: `audit_panel_loss` returns
`floored_ce_per_example` (the unweighted mean of per-example means, which route (c) prices
exactly) and `sum_cells`, `sum_cells_sq`, `n_effective` beside the archived `floored_ce`.
Both are recorded per seed so the two can be compared directly.

Usage
-----
    export ARC_TGI_ROOT=/path/to/simon-arc-lab      # pinned commit d8a2621, see README
    python3 c1_panelB_initial_loss.py               # measure all 20 seeds, then aggregate
    python3 c1_panelB_initial_loss.py --seeds 0,1   # measure a subset (resumes; keeps the rest)
    python3 c1_panelB_initial_loss.py --aggregate-only   # recompute the aggregate block only

Writes `results_data/c1_panelB_initial_loss.json`, saving after every seed so an
interrupted run resumes.

The terminal levels L_B(theta_T) are read back from the C1 shards. On a clean checkout
those live inside `dist/auditcp_experiments.zip`, which this script reads directly; if you
have already unpacked them into `results_data/`, those files win.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import traceback
import zipfile
from pathlib import Path
from typing import Dict, List, Optional

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
RESULTS_DIR = HERE / "results_data"
DIST_ZIP = REPO / "dist" / "auditcp_experiments.zip"
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
    "Delta": 0.056421,
    "slack_Gamma": 0.112841,
    "mean_L0": 2.4841,
    "mean_LT": 1.7476,
    "mean_G": 0.7366,
    "lower_bound_on_improvement": 0.6237,
    "discrimination_ratio": 6.53,
    "per_seed_lower_bound_min": 0.5266,
    "per_seed_lower_bound_max": 0.6981,
    "per_seed_positive_count": 20,
}


# -----------------------------------------------------------------------------
# terminal levels L_B(theta_T), read back from the C1 shards
# -----------------------------------------------------------------------------

def load_LT(seed: int) -> float:
    """Terminal audit level of the audit_cp policy on panel B, from the C1 shard."""
    loose = RESULTS_DIR / f"c1_seed{seed}.json"
    if loose.exists():
        shard = json.loads(loose.read_text())
    elif DIST_ZIP.exists():
        with zipfile.ZipFile(DIST_ZIP) as z:
            shard = json.loads(z.read(f"auditcp_experiments/results_data/c1_seed{seed}.json"))
    else:
        raise FileNotFoundError(
            f"no C1 shard for seed {seed}: expected {loose} or {DIST_ZIP}")
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
    # Measured only on a re-run: the unweighted level route (c) actually prices, and the
    # effective sample size of the weighted one. Absent from the archived rows.
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


def aggregate(per_seed: Dict[str, Dict]) -> Dict:
    seeds = sorted(int(k) for k in per_seed)
    rows = [per_seed[str(s)] for s in seeds]

    n_panels = sorted({int(r["n_panel"]) for r in rows})
    if len(n_panels) != 1:
        raise ValueError(f"seeds disagree on panel size: {n_panels}")
    n = n_panels[0]
    if n != N_EXPECTED:
        print(f"WARNING: panel size {n} != the camera-ready {N_EXPECTED}", file=sys.stderr)

    L0 = [r["L0"] for r in rows]
    LT = [r["LT"] for r in rows]
    G = [r["G"] for r in rows]

    sl = route_c_slack(n)
    Gamma = sl["slack_Gamma"]
    mean_G = _mean(G)
    per_seed_lb = [g - Gamma for g in G]

    # n_eff, when a re-run measured it. The archived rows do not carry the cell counts.
    n_eff_rows = [float(r["n_effective"]) for r in rows if "n_effective" in r]
    n_eff = _mean(n_eff_rows) if n_eff_rows else None
    # The threshold the record does fix: the corrected slack Gamma*sqrt(n/n_eff) stays below the
    # reported gain exactly while n_eff exceeds this.
    n_eff_needed = int(math.ceil(2.0 * R * R * math.log(2.0 * CARD_A / DELTA) / (mean_G ** 2)))

    return {
        "n_seeds": len(seeds),
        "seeds": seeds,
        "n_independent_audit_units": n,
        "independent_unit": "example (one padded 30x30 ARC-TGI grid); NOT the cell",
        "estimator": "content_cell_weighted_ratio",
        "estimator_note": (
            "L0 and LT are audit_panel_loss's floored_ce: total floored CE over every content "
            "cell of the panel divided by the total content-cell count. That is sum_i w_i m_i "
            "with w_i = c_i / sum_j c_j, not the unweighted mean of n per-example losses, and "
            "route (c)'s Delta is the radius of the unweighted mean. The corrected radius is "
            "Delta*sqrt(n/n_eff) with n_eff = (sum_i c_i)^2 / sum_i c_i^2 <= n, so Delta below "
            "is too small for this estimator whenever the grids differ in size, which they do."),
        "n_effective": n_eff,
        "n_effective_note": (
            ("mean over the %d seeds that carry per-example content-cell counts; the corrected "
             "radius is Delta*sqrt(n/n_eff)." % len(n_eff_rows)) if n_eff_rows else
            ("null: the archived measurement stored no per-example content-cell counts, so n_eff "
             "is not recoverable from this record. A re-run of c1_panelB_initial_loss.py stores "
             "sum_cells, sum_cells_sq and n_effective per seed, and L0_unweighted beside L0.")),
        "n_effective_required_for_positive_bound": n_eff_needed,
        "n_effective_required_note": (
            "2*R^2*ln(2N/delta)/G^2 at the mean gain: the corrected lower bound stays positive "
            "for every n_eff above this, out of n = %d records. Since n_eff >= n*mean(c)/max(c) "
            "and max(c) <= 900 on a 30x30 canvas, a mean above %.1f content cells per example is "
            "sufficient on its own. Neither quantity is settled by this record."
            % (n, 900.0 * n_eff_needed / n)),
        "loss_range_R": R,
        "delta": DELTA,
        "candidate_set_size_N": CARD_A,
        "slack_route": "c",
        "Delta": sl["Delta"],
        "slack_Gamma": Gamma,
        "L0": {"mean": _mean(L0), "sd": _sd(L0), "min": min(L0), "max": max(L0)},
        "LT": {"mean": _mean(LT), "sd": _sd(LT), "min": min(LT), "max": max(LT)},
        "G": {"mean": mean_G, "sd": _sd(G), "min": min(G), "max": max(G)},
        "lower_bound_on_improvement": mean_G - Gamma,
        "discrimination_ratio": mean_G / Gamma,
        "bound_reading": (
            "the lower bound and the ratio above are the published route (c) arithmetic and are "
            "exact for an unweighted mean of n per-example losses. The archived level is the "
            "cell-weighted ratio, so under that estimator the supported statement is conditional: "
            "the bound is positive exactly while n_eff > %d." % n_eff_needed),
        "per_seed_lower_bound": {
            "min": min(per_seed_lb),
            "max": max(per_seed_lb),
            "positive_count": sum(1 for v in per_seed_lb if v > 0),
            "note": ("each seed draws its own independent panel B, so this is the "
                     "single-seed statement at delta=0.05 applied seed by seed; it is not "
                     "a simultaneous 95% statement across all 20 seeds, which would need a "
                     "union bound over seeds"),
        },
    }


def check_validation_target(agg: Dict) -> bool:
    """Assert the aggregate reproduces the values reported in the paper."""
    got = {
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
            "n_effective": None,
            "priced_by_route_c_delta": False,
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
            "L0_unweighted": ("L_B(theta_0) as the unweighted mean of per-example means, which is "
                              "what route (c)'s Delta prices; present only on rows re-measured "
                              "after cp_models.audit_panel_loss began returning it"),
            "sum_cells": "sum_i c_i, content cells in panel B; re-measured rows only",
            "sum_cells_sq": "sum_i c_i^2; re-measured rows only",
            "n_effective": "(sum_i c_i)^2 / sum_i c_i^2; re-measured rows only",
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
    print(f"  Delta = {agg['Delta']:.6f}   slack Gamma = {agg['slack_Gamma']:.6f}")
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
