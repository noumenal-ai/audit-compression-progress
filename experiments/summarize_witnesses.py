#!/usr/bin/env python3
"""Recompute the reported experimental numbers from the archived records.

Every value printed in the paper's experiment section is recomputed here from the JSON
records in `results_data/` and compared with the paper's figure at the precision the paper
prints. Uncertainties are standard deviations across seeds (ddof = 1).

Records read (20 seeds each unless noted):
  c1_seed<S>.json               reward-signal ablation
  e1_seed<S>.json               stream scoring against a sealed audit
  e3_seed<S>.json               signed against clipped progress on a relearning cycle
  e4a_seed<S>.json              training on the reusable panel (memorization)
  e5_seed<S>.json               uniform deviation of a finite family against panel size
  e6_seed<S>.json               temperature-calibration probe
  e7_multiseed_summary.json     holdout attack, 20-seed aggregate written by e7_multiseed.py
  e7cal_seed0.json, e7scal_seed0.json
                                holdout attack, the seed-0 records the aggregate reproduces
  c1_panelB_initial_loss.json   initial and terminal sealed-panel levels of the ablation run

The holdout-attack aggregate is read as archived: e7_multiseed.py writes only the aggregate,
so per-seed records exist for seed 0 alone. The script checks that the aggregate's seed-0
entry equals the archived seed-0 record.

Usage:
    python3 summarize_witnesses.py               # read ./results_data
    python3 summarize_witnesses.py --data DIR    # read the records from DIR

Exit status: 0 if every value reproduces, 1 if any value does not, 2 if a record is missing
or malformed. Python 3 standard library only.
"""
from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from pathlib import Path
from typing import Dict, List, Sequence

N_SEEDS = 20
SEEDS = list(range(N_SEEDS))
DEFAULT_DATA = Path(__file__).resolve().parent / "results_data"

# Constants of the sealed-panel report (the loss floor fixes the range R = -ln eps).
EPS = 0.01
R = -math.log(EPS)
DELTA = 0.05


class RecordError(Exception):
    """A record is missing, or does not have the expected structure."""


# -----------------------------------------------------------------------------------------
# loading and statistics
# -----------------------------------------------------------------------------------------

def read_json(path: Path) -> Dict:
    if not path.is_file():
        raise RecordError(f"missing record: {path}")
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise RecordError(f"malformed JSON in {path}: {exc}") from exc


def load_seeds(data: Path, exp: str) -> List[Dict]:
    """The per-seed driver results of experiment `exp`, seeds 0..19 in order."""
    rows = []
    for s in SEEDS:
        blob = read_json(data / f"{exp}_seed{s}.json")
        if exp not in blob:
            raise RecordError(f"{exp}_seed{s}.json has no top-level key {exp!r}")
        rows.append(blob[exp])
    return rows


def mean(xs: Sequence[float]) -> float:
    return statistics.fmean(xs)


def sd(xs: Sequence[float]) -> float:
    """Sample standard deviation across seeds, ddof = 1."""
    return statistics.stdev(xs)


def welch_t(a: Sequence[float], b: Sequence[float]) -> float:
    return (mean(a) - mean(b)) / math.sqrt(sd(a) ** 2 / len(a) + sd(b) ** 2 / len(b))


def finite_class_slack(n: float, n_candidates: int, loss_range: float = R,
                       delta: float = DELTA) -> float:
    """Two-endpoint slack 2 * R * sqrt(ln(2N / delta) / (2n)) of a fixed panel."""
    return 2.0 * loss_range * math.sqrt(math.log(2.0 * n_candidates / delta) / (2.0 * n))


# -----------------------------------------------------------------------------------------
# comparison against the printed values
# -----------------------------------------------------------------------------------------

def fmt(value: float, ndp: int) -> str:
    s = f"{value:.{ndp}f}"
    if s.startswith("-") and set(s[1:]) <= set("0."):
        s = s[1:]                       # a rounded negative zero prints as zero
    return s


class Ledger:
    def __init__(self) -> None:
        self.n_ok = 0
        self.failures: List[str] = []

    def _record(self, ok: bool, line: str) -> None:
        print(("  OK    " if ok else "  FAIL  ") + line)
        if ok:
            self.n_ok += 1
        else:
            self.failures.append(line)

    def value(self, label: str, x: float, printed: str, spread: float = None) -> None:
        """`x` must round to `printed` at the number of decimals `printed` carries."""
        ndp = len(printed.split(".")[1]) if "." in printed else 0
        got = fmt(x, ndp)
        extra = f"  (SD {spread:.4g})" if spread is not None else ""
        self._record(got == printed,
                     f"{label:64s} paper {printed:>9s}   computed {x:.6g}{extra}")

    def exact(self, label: str, got, want) -> None:
        self._record(got == want, f"{label:64s} paper {str(want):>9s}   computed {got}")

    def at_least(self, label: str, x: float, bound: float) -> None:
        self._record(x >= bound, f"{label:64s} paper >= {bound:<6g}  computed {x:.6g}")

    def below(self, label: str, x: float, bound: float) -> None:
        self._record(x < bound, f"{label:64s} must be < {bound:.6g}   computed {x:.6g}")


def section(title: str) -> None:
    print(f"\n{title}")


# -----------------------------------------------------------------------------------------
# the experiments
# -----------------------------------------------------------------------------------------

def reward_ablation(data: Path, L: Ledger, extra: bool) -> Dict[str, List[float]]:
    c1 = load_seeds(data, "c1")
    pol = lambda p, k: [r["by_policy"][p][k] for r in c1]          # noqa: E731
    acc = {p: pol(p, "final_active_cell_acc") for p in
           ("audit_cp", "prediction_error", "rnd", "icm", "uniform", "oracle_learnable")}
    dis = {p: pol(p, "distractor_fraction") for p in
           ("audit_cp", "prediction_error", "rnd", "icm", "uniform")}
    if not extra:
        section("Reward-signal ablation (c1_seed*.json, 20 seeds)")
        for p, printed in (("audit_cp", "0.387"), ("prediction_error", "0.338"), ("rnd", "0.371"),
                           ("icm", "0.347"), ("uniform", "0.376"), ("oracle_learnable", "0.391")):
            L.value(f"final active-cell accuracy, {p}", mean(acc[p]), printed, sd(acc[p]))
        for p, printed in (("audit_cp", "0.219"), ("prediction_error", "0.504"), ("rnd", "0.251"),
                           ("icm", "0.179"), ("uniform", "0.250")):
            L.value(f"distractor fraction, {p}", mean(dis[p]), printed, sd(dis[p]))
        L.exact("seeds with ICM distractor fraction below audit_cp",
                sum(i < a for i, a in zip(dis["icm"], dis["audit_cp"])), 16)
        L.exact("seeds with audit_cp accuracy above rnd",
                sum(a > b for a, b in zip(acc["audit_cp"], acc["rnd"])), 17)
    else:
        section("Reward-signal ablation, further values quoted in the paper")
        L.value("audit_cp accuracy, SD across seeds", sd(acc["audit_cp"]), "0.014")
        L.value("Welch t, audit_cp against ICM accuracy", welch_t(acc["audit_cp"], acc["icm"]), "7.1")
        for p, printed in (("prediction_error", "50.4"), ("uniform", "25.0"),
                           ("audit_cp", "21.9"), ("icm", "17.9")):
            L.value(f"distractor share in percent, {p}", 100.0 * mean(dis[p]), printed)
    return {p: pol(p, "final_fresh_floored_ce")
            for p in ("audit_cp", "uniform", "rnd", "prediction_error", "icm")}


def stream_vs_audit(data: Path, L: Ledger, extra: bool) -> None:
    e1 = load_seeds(data, "e1")
    by_k = {}
    for i, k in enumerate((0.0, 0.5, 1.0)):
        ks = {r["by_k"][i]["k"] for r in e1}
        if ks != {k}:
            raise RecordError(f"e1 by_k[{i}] holds k = {sorted(ks)}, expected {k}")
        by_k[k] = ([r["by_k"][i]["cum_stream_cp"] for r in e1],
                   [r["by_k"][i]["cum_fresh_audit_cp"] for r in e1])
    (s0, f0), (s5, f5), (s1, f1) = by_k[0.0], by_k[0.5], by_k[1.0]
    if not extra:
        section("Stream scoring against a sealed audit (e1_seed*.json, 20 seeds)")
        L.value("cumulative stream progress, k = 0", mean(s0), "28.96", sd(s0))
        L.value("cumulative stream progress, k = 0.5", mean(s5), "29.95", sd(s5))
        L.value("cumulative sealed-audit progress, k = 0", mean(f0), "0.741", sd(f0))
        L.value("cumulative sealed-audit progress, k = 0.5", mean(f5), "0.715", sd(f5))
        L.value("cumulative sealed-audit progress, k = 1", mean(f1), "-0.031", sd(f1))
        L.value("  its SD across seeds", sd(f1), "0.318")
    else:
        section("Stream scoring, further values quoted in the paper")
        L.value("stream progress SD, k = 0", sd(s0), "1.82")
        L.value("stream progress SD, k = 0.5", sd(s5), "2.47")
        L.value("sealed progress SD, k = 0", sd(f0), "0.104")
        L.value("sealed progress SD, k = 0.5", sd(f5), "0.102")
        L.value("cumulative stream progress, k = 1", mean(s1), "10.6")
        L.value("cumulative sealed-audit progress, k = 1", mean(f1), "-0.03")
        L.value("  its SD across seeds", sd(f1), "0.32")
        L.value("ratio of stream to sealed progress, k = 0", mean(s0) / mean(f0), "39")
        L.at_least("bridge terms: stream progress less R, k = 0", mean(s0) - R, 24.3)


def signed_vs_clipped(data: Path, L: Ledger, extra: bool) -> None:
    e3 = load_seeds(data, "e3")
    cl = [r["cum_clipped"] for r in e3]
    sg = [r["cum_signed"] for r in e3]
    gp = [r["exploit_gap"] for r in e3]
    if not extra:
        section("Signed against clipped progress (e3_seed*.json, 20 seeds)")
        L.value("cumulative clipped reward", mean(cl), "1.4175", sd(cl))
        L.value("cumulative signed progress", mean(sg), "-0.0721", sd(sg))
        L.value("exploit gap, clipped minus signed", mean(gp), "1.4896", sd(gp))
        L.value("  its SD across seeds", sd(gp), "0.163")
        L.exact("seeds whose exploit gap equals clipped minus signed exactly",
                sum(g == c - s for g, c, s in zip(gp, cl, sg)), N_SEEDS)
        L.exact("seeds with a positive exploit gap", sum(g > 0 for g in gp), 20)
        L.exact("seeds where signed progress equals the endpoint change exactly",
                sum(r["cum_signed"] == r["endpoint_improvement"] for r in e3), 20)
    else:
        section("Signed against clipped progress, further values quoted in the paper")
        L.value("cumulative clipped reward", mean(cl), "1.42")
        L.value("  its SD across seeds", sd(cl), "0.20")
        L.value("cumulative signed progress", mean(sg), "-0.072")
        L.value("  its SD across seeds", sd(sg), "0.095")
        L.value("exploit gap", mean(gp), "1.49")
        L.value("  its SD across seeds", sd(gp), "0.16")


def memorization(data: Path, L: Ledger, extra: bool) -> None:
    e4 = load_seeds(data, "e4a")
    by_n = {}
    for i, n in enumerate((24, 144)):
        ns = {r["by_n"][i]["n_total"] for r in e4}
        if ns != {n}:
            raise RecordError(f"e4a by_n[{i}] holds n_total = {sorted(ns)}, expected {n}")
        by_n[n] = {k: [r["by_n"][i][k] for r in e4]
                   for k in ("empirical_progress", "true_progress", "false_positive_excess")}
    a, b = by_n[24], by_n[144]
    if not extra:
        section("Training on the reusable panel (e4a_seed*.json, 20 seeds)")
        for n, d in ((24, a), (144, b)):
            L.exact(f"seeds whose excess equals apparent minus true progress, n_total = {n}",
                    sum(x == e - t for x, e, t in zip(d["false_positive_excess"],
                                                       d["empirical_progress"],
                                                       d["true_progress"])), N_SEEDS)
        L.value("apparent (panel) progress, n_total = 24", mean(a["empirical_progress"]), "2.386",
                sd(a["empirical_progress"]))
        L.value("true (fresh) progress, n_total = 24", mean(a["true_progress"]), "-1.497",
                sd(a["true_progress"]))
        L.value("false-positive excess, n_total = 24", mean(a["false_positive_excess"]), "3.883",
                sd(a["false_positive_excess"]))
        L.value("  its SD across seeds", sd(a["false_positive_excess"]), "0.202")
        L.value("false-positive excess, n_total = 144", mean(b["false_positive_excess"]), "3.527",
                sd(b["false_positive_excess"]))
    else:
        section("Training on the reusable panel, further values quoted in the paper")
        L.value("apparent progress, n_total = 24", mean(a["empirical_progress"]), "2.39")
        L.value("  its SD across seeds", sd(a["empirical_progress"]), "0.13")
        L.value("true progress, n_total = 24", mean(a["true_progress"]), "-1.50")
        L.value("  its SD across seeds", sd(a["true_progress"]), "0.21")
        L.value("false-positive excess, n_total = 24", mean(a["false_positive_excess"]), "3.88")
        L.value("  its SD across seeds", sd(a["false_positive_excess"]), "0.20")
        L.value("false-positive excess, n_total = 144", mean(b["false_positive_excess"]), "3.53")
        L.value("  its SD across seeds", sd(b["false_positive_excess"]), "0.17")


def concentration(data: Path, L: Ledger, extra: bool) -> None:
    e5 = load_seeds(data, "e5")
    sl = [r["loglog_slope"] for r in e5]
    if not extra:
        section("Uniform deviation against panel size (e5_seed*.json, 20 seeds)")
        L.value("log-log slope of the uniform deviation", mean(sl), "-0.526", sd(sl))
        L.value("  its SD across seeds", sd(sl), "0.047")
    else:
        section("Uniform deviation, further values quoted in the paper")
        sizes = {tuple(o["n"] for o in r["by_n"]) for r in e5}
        L.exact("panel sizes in every seed", " ".join(map(str, sizes.pop())) if len(sizes) == 1
                else "differ across seeds", "16 64 256")


def calibration(data: Path, L: Ledger, extra: bool) -> None:
    e6 = load_seeds(data, "e6")
    if not extra:
        section("Temperature-calibration probe (e6_seed*.json, 20 seeds)")
        L.exact("seeds with accuracy change exactly 0", sum(r["delta_acc"] == 0 for r in e6), 20)
    else:
        section("Temperature-calibration probe, further values quoted in the paper")
        T = [r["temperature"] for r in e6]
        L.value("fitted temperature", mean(T), "0.986", sd(T))
        L.value("  its SD across seeds", sd(T), "0.072")


def holdout_attack(data: Path, L: Ledger, extra: bool) -> None:
    summ = read_json(data / "e7_multiseed_summary.json")
    cal0 = read_json(data / "e7cal_seed0.json")["e7cal"]
    scal0 = read_json(data / "e7scal_seed0.json")["e7scal"]
    if summ.get("nseeds") != N_SEEDS or summ.get("seeds") != SEEDS:
        raise RecordError("e7_multiseed_summary.json does not cover seeds 0..19")
    naive = {row["Q"]: row for row in summ["calibration_naive"]}
    defs = {row["defense"]: row for row in summ["calibration_defenses_maxQ"]}
    scal = {row["n"]: row for row in summ["scaling_curve"]}
    q8 = naive[8000]
    if not extra:
        section("Holdout attack (e7_multiseed_summary.json, 20 seeds; seed-0 records)")
        L.exact("aggregate seed-0 gap equals the seed-0 record at Q = 8000",
                summ["seed0_gap_Q8000"] == cal0["naive_sweep"][-1]["gap"], True)
        L.exact("query budget of the calibration", max(naive), 8000)
        L.exact("reusable panel size of the calibration", cal0["n"], 200)
        L.value("naive release: gap at Q = 8000", q8["gap_mean"], "3.241", q8["gap_sd"])
        L.value("  its SD across seeds", q8["gap_sd"], "0.070")
        L.value("finite-class threshold 2 Delta_n at Q = 8000, n = 200", q8["threshold"], "1.6396")
        L.value("  recomputed from R, delta, n and the stored candidate count",
                finite_class_slack(cal0["n"], cal0["naive_sweep"][-1]["card_A"]), "1.6396")
        L.exact("seeds in which the attacker crosses the threshold", q8["wins"], 20)
        for d, printed in (("fresh_subsample", "1.368"), ("ladder", "0.000"),
                           ("rounded", "0.000"), ("one_shot", "0.000")):
            L.value(f"{d} release: gap at Q = 8000", defs[d]["gap_mean"], printed,
                    defs[d]["gap_sd"])
        for n, gap, thr in ((50, "4.181", "3.279"), (200, "3.242", "1.640"),
                            (800, "0.906", "0.842"), (3200, "0.226", "0.442"),
                            (12800, "0.0564", "0.231")):
            L.value(f"panel-size sweep: gap at n = {n}", scal[n]["gap_mean"], gap,
                    scal[n]["gap_sd"])
            L.value(f"panel-size sweep: threshold at n = {n}", scal[n]["threshold"], thr)
        seed0_thr = {o["n"]: o["threshold_2delta"] for o in scal0["by_n"]}
        L.exact("sweep thresholds agree with the seed-0 record to 1e-12",
                all(abs(seed0_thr[n] - scal[n]["threshold"]) < 1e-12 for n in scal), True)
    else:
        section("Holdout attack, further values quoted in the paper")
        L.value("naive release: gap at Q = 8000", q8["gap_mean"], "3.24")
        L.value("  its SD across seeds", q8["gap_sd"], "0.07")
        L.value("threshold at Q = 8000", q8["threshold"], "1.64")
        L.value("fresh-subsample release: gap", defs["fresh_subsample"]["gap_mean"], "1.37")
        L.exact("seeds crossing under any non-naive release",
                sum(defs[d]["wins"] for d in defs if d != "naive"), 0)
        for n, gap, thr, crosses in ((200, "3.24", "1.64", 20), (800, "0.91", "0.84", 20),
                                     (3200, "0.23", "0.44", 0), (12800, "0.06", "0.23", 0)):
            L.value(f"panel-size sweep: gap at n = {n}", scal[n]["gap_mean"], gap)
            L.value(f"panel-size sweep: threshold at n = {n}", scal[n]["threshold"], thr)
            L.exact(f"panel-size sweep: seeds crossing at n = {n}", scal[n]["crosses"], crosses)
        L.exact("panel-size sweep: seeds crossing at n = 50", scal[50]["crosses"], 20)


def sealed_panel_report(data: Path, L: Ledger, extra: bool,
                        terminal: Dict[str, List[float]]) -> None:
    rec = read_json(data / "c1_panelB_initial_loss.json")
    rows = [rec["per_seed"][str(s)] for s in SEEDS]
    if any(r.get("status") != "ok" for r in rows):
        raise RecordError("c1_panelB_initial_loss.json has a seed whose status is not ok")
    G = [r["L0"] - r["LT"] for r in rows]
    n_eff_rows = [r["sum_cells"] ** 2 / r["sum_cells_sq"] for r in rows]
    n_eff = mean(n_eff_rows)
    slack = finite_class_slack(n_eff, 1)
    lower = mean(G) - slack
    ratio = mean(G) / slack
    if not extra:
        section("Five-number report of the audit_cp run on the sealed panel "
                "(c1_panelB_initial_loss.json)")
        L.exact("seeds whose terminal level equals the c1 record exactly",
                sum(r["LT"] == t for r, t in zip(rows, terminal["audit_cp"])), N_SEEDS)
        L.exact("seeds whose stored gain equals L0 - LT exactly",
                sum(r["G"] == g for r, g in zip(rows, G)), N_SEEDS)
        L.value("mean signed gain L0 - LT (nats)", mean(G), "0.7366", sd(G))
        L.value("  its SD across seeds", sd(G), "0.0468")
        L.value("slack at the mean effective panel size, N = 1, delta = 0.05", slack, "0.1549")
        L.value("lower bound on improvement", lower, "0.5817")
        L.value("discrimination ratio, gain over slack", ratio, "4.76")
    else:
        section("Five-number report, further values quoted in the paper")
        L.value("effective panel size", n_eff, "6522")
        L.value("mean signed gain", mean(G), "0.737")
        L.value("  its SD across seeds", sd(G), "0.047")
        L.value("minimum signed gain over seeds", min(G), "0.639")
        L.value("slack", slack, "0.155")
        L.value("lower bound on improvement", lower, "0.582")
        L.value("discrimination ratio", ratio, "4.8")
        L.value("slack with all seven policies declared, N = 7", finite_class_slack(n_eff, 7), "0.19")
        for p in ("uniform", "rnd"):
            L.below(f"terminal-level difference, audit_cp against {p}",
                    abs(mean(terminal[p]) - mean(terminal["audit_cp"])), slack)


def main(argv: Sequence[str] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--data", type=Path, default=DEFAULT_DATA,
                    help="directory holding the archived records (default: %(default)s)")
    args = ap.parse_args(argv)
    L = Ledger()
    print(f"records: {args.data}")
    try:
        for extra in (False, True):
            if extra:
                print("\n" + "-" * 96 + "\nFurther values quoted in the paper's text and tables")
            terminal = reward_ablation(args.data, L, extra)
            stream_vs_audit(args.data, L, extra)
            signed_vs_clipped(args.data, L, extra)
            memorization(args.data, L, extra)
            concentration(args.data, L, extra)
            calibration(args.data, L, extra)
            holdout_attack(args.data, L, extra)
            sealed_panel_report(args.data, L, extra, terminal)
    except (RecordError, KeyError, IndexError, TypeError) as exc:
        print(f"\nERROR: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2
    print()
    if L.failures:
        print(f"{len(L.failures)} of {L.n_ok + len(L.failures)} values do NOT reproduce:")
        for line in L.failures:
            print("  " + line)
        return 1
    print(f"All {L.n_ok} values reproduce.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
