#!/usr/bin/env python3
"""Turn the per-item losses in raw/ into audit compression progress reports.

Every number below is produced by the functions in notebooks/audit_cp_report.ipynb. The notebook's
core cells (Sections 1 to 8) are executed into this module's namespace, so declare_panel,
compute_slack, five_numbers, audit_cp_report, reconcile_increments, check_independent_units,
resolution_before_run and panel_size_for_resolution are the notebook's own definitions.

Run:  python3 report.py            # writes report.json and prints the tables
"""

import io
import json
import math
import contextlib
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
NOTEBOOK = REPO / "notebooks" / "audit_cp_report.ipynb"
DECL = json.loads((HERE / "panel_declaration.json").read_text())


# --------------------------------------------------------------------------- notebook core
def load_notebook_core():
    """Execute the notebook's Sections 1-8 code cells and return their namespace."""
    nb = json.loads(NOTEBOOK.read_text())
    cells = nb["cells"]
    stop = next(i for i, c in enumerate(cells)
                if c["cell_type"] == "markdown" and "".join(c["source"]).lstrip().startswith("## 9."))
    ns = {"__name__": "audit_cp_core"}
    with contextlib.redirect_stdout(io.StringIO()):
        for c in cells[:stop]:
            if c["cell_type"] == "code":
                exec(compile("".join(c["source"]), "<audit_cp_report.ipynb>", "exec"), ns)
    for required in ("declare_panel", "compute_slack", "five_numbers", "audit_cp_report",
                     "reconcile_increments", "check_independent_units", "resolution_before_run",
                     "panel_size_for_resolution", "PanelSteeredError"):
        assert required in ns, "notebook core is missing %s" % required
    return ns


NB = load_notebook_core()
declare_panel = NB["declare_panel"]
compute_slack = NB["compute_slack"]
five_numbers = NB["five_numbers"]
audit_cp_report = NB["audit_cp_report"]
reconcile_increments = NB["reconcile_increments"]
check_independent_units = NB["check_independent_units"]
resolution_before_run = NB["resolution_before_run"]
panel_size_for_resolution = NB["panel_size_for_resolution"]
PanelSteeredError = NB["PanelSteeredError"]


def transcript_budget_for_gain(*, gain, n, R, delta):
    """Largest route (d) transcript budget B, in bits, that still leaves a positive lower bound.

    Same formula as the notebook's helper of this name (Section 10).
    """
    return (n * (gain / R) ** 2 / 2.0 - math.log(1.0 / delta)) / math.log(2.0)


# --------------------------------------------------------------------------- data
def load_raw():
    blocks, meta = {}, None
    for path in sorted((HERE / "raw").glob("*.npz")):
        z = np.load(path, allow_pickle=False)
        m = json.loads(str(z["meta"]))
        if meta is None:
            meta = {k: m[k] for k in ("panel_sha256", "panel_repo", "panel_revision", "panel_file",
                                      "n_units", "declaration_sha256", "torch", "device")}
            meta["states"] = []
        else:
            assert meta["panel_sha256"] == m["panel_sha256"], "parts scored different panels"
            assert meta["declaration_sha256"] == m["declaration_sha256"], "parts used different declarations"
        meta["states"].extend(m["states"])
        for k in z.files:
            if k == "meta":
                continue
            blocks[k] = z[k]
    assert meta is not None, "no npz parts in raw/; run score_states.py first"
    return blocks, meta


DELTA = float(DECL["slack"]["delta"])
ALPHA = float(DECL["quote_construction"]["alpha"])
BLOCKS, META = load_raw()
N_UNITS = int(META["n_units"])
STATE_META = {s["state"]: s for s in META["states"]}


def arr(state, field):
    return BLOCKS["%s/%s" % (state, field)]


# --------------------------------------------------------------------------- provenance
GPT2_PANEL = declare_panel(
    "LAMBADA-OpenAI test, scored under the GPT-2 release",
    reward=False,
    early_stopping=False,
    checkpoint_selection=False,
    hyperparameter_selection=False,
    data_selection=False,
    note=("Radford et al. (2019) train GPT-2 on WebText with a language-modelling objective and "
          "evaluate LAMBADA zero-shot with no task-specific fine-tuning; the four sizes are fixed "
          "in advance and the released checkpoints are not described as selected by any downstream "
          "score. The declaration rests on that account and is not independently verifiable from "
          "the released artifacts, so a route (d) sensitivity is reported alongside."),
)

PYTHIA_PANEL = declare_panel(
    "LAMBADA-OpenAI test, scored under the Pythia-160m released revisions",
    reward=False,
    early_stopping=False,
    checkpoint_selection=False,
    hyperparameter_selection=False,
    data_selection=False,
    note=("Biderman et al. (2023) fix the data order and the step budget in advance, save "
          "checkpoints at fixed step intervals rather than at selected ones, and release every "
          "checkpoint, so no downstream score can have chosen which state is reported."),
)

TARGETS = [
    dict(id="Q1", family="gpt2", metric="loss_target", panel=GPT2_PANEL,
         states=["gpt2", "gpt2-medium"], p0="gpt2", pT="gpt2-medium",
         label="LAMBADA final word, GPT-2 BPE, mean floored token log loss per passage"),
    dict(id="Q2", family="gpt2", metric="loss_passage", panel=GPT2_PANEL,
         states=["gpt2", "gpt2-medium"], p0="gpt2", pT="gpt2-medium",
         label="LAMBADA whole passage, GPT-2 BPE, mean floored token log loss per passage"),
    dict(id="Q3", family="pythia", metric="loss_target", panel=PYTHIA_PANEL,
         states=["pythia-160m@1k", "pythia-160m@16k", "pythia-160m@64k", "pythia-160m@143k"],
         p0="pythia-160m@1k", pT="pythia-160m@143k",
         label="LAMBADA final word, NeoX BPE, mean floored token log loss per passage"),
    dict(id="Q4", family="pythia", metric="loss_passage", panel=PYTHIA_PANEL,
         states=["pythia-160m@1k", "pythia-160m@16k", "pythia-160m@64k", "pythia-160m@143k"],
         p0="pythia-160m@1k", pT="pythia-160m@143k",
         label="LAMBADA whole passage, NeoX BPE, mean floored token log loss per passage"),
]


def build_target(t):
    present = [s for s in t["states"] if "%s/%s" % (s, t["metric"]) in BLOCKS]
    if t["p0"] not in present or t["pT"] not in present:
        return None
    N = len(present)                                    # states actually scored on this panel
    R = max(STATE_META[s]["R"] for s in present)        # widest declared loss range in the set
    V = STATE_META[t["pT"]]["V"]
    L_ref_per_unit = math.log(V)                        # uniform code over the same label set
    loss_ref = np.full(N_UNITS, L_ref_per_unit)
    slack = compute_slack("c", provenance=t["panel"], n=N_UNITS, R=R, delta=DELTA, N=N)
    l0, lT = arr(t["p0"], t["metric"]), arr(t["pT"], t["metric"])
    fn = five_numbers(loss_ref, l0, lT, slack, R=R)

    rep = audit_cp_report(
        loss_ref, l0, lT, slack,
        target_version="lambada-openai/%s/%s/alpha0.01/v1" % (t["family"], t["metric"]),
        reference_version="uniform-over-%d-token-vocabulary/v1" % V,
        masking_policy_version=("lambada-openai/final-word-only/v1" if t["metric"] == "loss_target"
                                else "lambada-openai/passage-positions-1..T-1/v1"),
        audit_unit=("one LAMBADA-OpenAI passage; loss is the mean over the scored tokens of that "
                    "passage of -ln((1-0.01)p + 0.01/%d)" % V),
        n_independent_units=N_UNITS,
        R=R,
        commitment_record={
            "state_commitment": "hf revisions %s -> %s" % (
                DECL_STATE(t["p0"])["revision"], DECL_STATE(t["pT"])["revision"]),
            "committed_at": "published model revisions, pinned by commit sha before scoring",
            "challenge_drawn_after_commitment": True,
            "panel_declaration_sha256": META["declaration_sha256"],
            "panel_file_sha256": META["panel_sha256"],
            "note": ("the two states are immutable published revisions and the panel is an "
                     "immutable published file; both hashes predate this report"),
        },
        component_notes=[
            "route (c) with N = %d, the number of model states scored on this target's panel" % N,
            "panel: %s @ %s, %s" % (META["panel_repo"], META["panel_revision"][:10], META["panel_file"]),
        ],
    )
    empirical_paired_sd = float((l0 - lT).std(ddof=1))
    out = {
        "id": t["id"], "label": t["label"], "family": t["family"], "metric": t["metric"],
        "p_0": t["p0"], "p_T": t["pT"], "N_candidate_states": N, "R": R, "V": V,
        "n": N_UNITS, "delta": DELTA,
        "radius_Delta": slack.params["Delta"],
        "five_numbers": {
            "terminal_level_B": fn.terminal_level,
            "signed_gain_G": fn.signed_gain,
            "slack_Gamma": fn.slack,
            "lower_bound_on_improvement": fn.lower_bound,
            "discrimination_ratio": fn.discrimination_ratio,
        },
        "levels": {"L_reference": fn.level_ref, "L_initial": fn.level_initial,
                   "L_terminal": fn.level_terminal},
        "positive": bool(fn.lower_bound > 0.0),
        "report_object": rep,
        "diagnostics_not_part_of_the_bound": {
            "empirical_paired_sd_of_per_unit_gain": empirical_paired_sd,
            "normal_approximation_paired_halfwidth_95pct": 1.959964 * empirical_paired_sd / math.sqrt(N_UNITS),
            "worst_case_slack_over_normal_halfwidth": fn.slack / (1.959964 * empirical_paired_sd / math.sqrt(N_UNITS)),
            "note": ("the normal-approximation half-width is reported only to show how much the "
                     "worst-case route (c) slack costs; it is not a worst-case bound and no claim "
                     "rests on it"),
        },
        "route_d_sensitivity": {
            "question": "how many bits of audit-derived transcript could have reached training before the bound is erased",
            "max_transcript_bits_keeping_bound_positive": (
                transcript_budget_for_gain(gain=fn.signed_gain, n=N_UNITS, R=R, delta=DELTA)),
        },
        "resolution": {
            "smallest_improvement_this_panel_can_demonstrate_nats": fn.slack,
            "n_needed_for_0.10_nats": panel_size_for_resolution(gamma_target=0.10, R=R, delta=DELTA, N=N),
            "n_needed_for_0.25_nats": panel_size_for_resolution(gamma_target=0.25, R=R, delta=DELTA, N=N),
            "n_needed_for_half_the_observed_gain": (
                panel_size_for_resolution(gamma_target=max(fn.signed_gain, 1e-9) / 2.0, R=R,
                                          delta=DELTA, N=N) if fn.signed_gain > 0 else None),
        },
        "per_state_levels": {s: float(arr(s, t["metric"]).mean()) for s in present},
    }
    return out


def DECL_STATE(sid):
    return next(s for s in DECL["states"] if s["id"] == sid)


# --------------------------------------------------------------------------- published claim
PUBLISHED_CLAIM = {
    "paper": "Alec Radford, Jeffrey Wu, Rewon Child, David Luan, Dario Amodei, Ilya Sutskever. "
             "Language Models are Unsupervised Multitask Learners. OpenAI technical report, 2019.",
    "table": "Table 3, zero-shot results. Caption: no training or fine-tuning was performed for any of these results.",
    "rows": {
        "117M": {"lambada_ppl": 35.13, "lambada_acc_percent": 45.99},
        "345M": {"lambada_ppl": 15.60, "lambada_acc_percent": 55.48},
        "762M": {"lambada_ppl": 10.87, "lambada_acc_percent": 60.12},
        "1542M": {"lambada_ppl": 8.63, "lambada_acc_percent": 63.24},
    },
    "reported_uncertainty": "none; Table 3 carries no interval, no seed spread and no resolution statement",
    "known_preprocessing_gaps": [
        "Section 3.1 reports the use of invertible de-tokenizers worth 2.5 to 5 perplexity points, "
        "which are not part of the released lambada_test.jsonl panel",
        "Section 3.3 states that the LAMBADA accuracy column adds a stop-word filter, which raises "
        "the 1542M accuracy from 52.66 to 63.24 percent; the filter is not released",
    ],
    "pythia_paper": "Stella Biderman et al. Pythia: A Suite for Analyzing Large Language Models "
                    "Across Training and Scaling. ICML 2023, arXiv:2304.01373. 154 checkpoints per "
                    "model at fixed step intervals, identical data order across models.",
}


def wrong_unit_demo(targets):
    """What substituting the token count for n would have done to each headline number.

    Tokens inside one passage are dependent. n is the passage count. This block exists so the
    cost of getting that wrong is on the record as a number rather than as a warning.
    """
    rows = []
    for t in targets:
        state = t["p_T"]
        field = "n_pass_tok" if t["metric"] == "loss_passage" else "n_tgt_tok"
        n_tokens = int(arr(state, field).sum())
        Delta = t["R"] * math.sqrt(math.log(2.0 * t["N_candidate_states"] / DELTA) / (2.0 * n_tokens))
        gamma = 2.0 * Delta
        G = t["five_numbers"]["signed_gain_G"]
        rows.append({
            "id": t["id"], "n_correct_units": N_UNITS, "n_tokens_wrong": n_tokens,
            "sub_units_per_record": n_tokens / float(N_UNITS),
            "slack_if_tokens_used": gamma, "lower_bound_if_tokens_used": G - gamma,
            "correct_lower_bound": t["five_numbers"]["lower_bound_on_improvement"],
            "would_flip_a_negative_to_positive": bool(
                t["five_numbers"]["lower_bound_on_improvement"] <= 0 < G - gamma),
        })
    return rows


def union_sensitivity(targets):
    """Every number in this report shares one panel. This prices a union over all of them.

    The per-target N counts only the states scored on that target. A reader who wants one
    confidence statement covering everything reported here needs N = the total number of
    (state, target) quotes scored on the panel.
    """
    n_quotes = sum(t["N_candidate_states"] for t in targets)
    out = {"N_union": n_quotes,
           "reason": "total number of (model state, target) quotes scored on this one panel",
           "per_target": []}
    for t in targets:
        Delta = t["R"] * math.sqrt(math.log(2.0 * n_quotes / DELTA) / (2.0 * N_UNITS))
        gamma = 2.0 * Delta
        G = t["five_numbers"]["signed_gain_G"]
        out["per_target"].append({
            "id": t["id"], "slack_Gamma_union": gamma, "lower_bound_union": G - gamma,
            "positive_under_union": bool(G - gamma > 0),
            "flips_to_non_positive": bool(t["positive"] and (G - gamma) <= 0),
        })
    return out


# --------------------------------------------------------------------------- published metrics
def published_metrics(state):
    """The benchmark's own published quantities: per-word LAMBADA perplexity and accuracy."""
    return {
        "lambada_perplexity_per_word": float(math.exp(-arr(state, "sum_logp_target").mean())),
        "lambada_accuracy": float(arr(state, "greedy_ok").mean()),
        "mean_target_word_nll_nats": float(-arr(state, "sum_logp_target").mean()),
    }


def accuracy_comparison(p0, pT, label):
    a0, aT = arr(p0, "greedy_ok").astype(np.float64), arr(pT, "greedy_ok").astype(np.float64)
    d = aT - a0                                              # paired difference in {-1, 0, +1}
    n = d.size
    # worst-case paired radius: Hoeffding for a mean of n independent variables of range 2
    radius = 2.0 * math.sqrt(math.log(2.0 / DELTA) / (2.0 * n))
    emp_sd = float(d.std(ddof=1))
    return {
        "comparison": label,
        "accuracy_initial": float(a0.mean()),
        "accuracy_terminal": float(aT.mean()),
        "accuracy_delta": float(d.mean()),
        "worst_case_paired_radius_at_delta_0.05": radius,
        "delta_exceeds_its_worst_case_paired_radius": bool(abs(d.mean()) > radius),
        "discordant_pairs_up": int(((aT - a0) > 0).sum()),
        "discordant_pairs_down": int(((aT - a0) < 0).sum()),
        "diagnostics_not_part_of_the_bound": {
            "empirical_paired_sd": emp_sd,
            "normal_approximation_halfwidth_95pct": 1.959964 * emp_sd / math.sqrt(n),
        },
    }


# --------------------------------------------------------------------------- main
def main():
    print("panel: %s @ %s / %s" % (META["panel_repo"], META["panel_revision"][:10], META["panel_file"]))
    print("panel file sha256: %s" % META["panel_sha256"])
    print("declaration sha256: %s" % META["declaration_sha256"])
    print()
    check_independent_units(N_UNITS, "example", n_records=N_UNITS)
    print()

    targets = [b for b in (build_target(t) for t in TARGETS) if b is not None]

    print("%-4s %-58s %8s %8s %9s %9s %7s" %
          ("id", "target", "L_0", "L_T", "G", "G-Gamma", "G/Gam"))
    for b in targets:
        f = b["five_numbers"]
        print("%-4s %-58s %8.4f %8.4f %9.4f %9.4f %7.2f" %
              (b["id"], b["label"][:58], b["levels"]["L_initial"], b["levels"]["L_terminal"],
               f["signed_gain_G"], f["lower_bound_on_improvement"], f["discrimination_ratio"]))
    print()
    for b in targets:
        f = b["five_numbers"]
        verdict = ("improved by at least %.4f nats" % f["lower_bound_on_improvement"]
                   if b["positive"] else "no improvement demonstrated at this resolution")
        print("%s  Gamma=%.4f (R=%.4f, N=%d)  ->  %s" %
              (b["id"], f["slack_Gamma"], b["R"], b["N_candidate_states"], verdict))

    # ---- the Pythia revision ladder: increments telescope to the endpoints
    ladders = {}
    for metric, tid in (("loss_passage", "Q4"), ("loss_target", "Q3")):
        states = [s for s in ["pythia-160m@1k", "pythia-160m@16k", "pythia-160m@64k",
                              "pythia-160m@143k"] if "%s/%s" % (s, metric) in BLOCKS]
        if len(states) < 3:
            continue
        V = STATE_META[states[-1]]["V"]
        L_ref = math.log(V)
        levels = [float(arr(s, metric).mean()) for s in states]
        B = [L_ref - L for L in levels]                     # audit level against the reference
        incr = [B[i + 1] - B[i] for i in range(len(B) - 1)]
        print("\n%s revision ladder (%s):" % (tid, metric))
        with contextlib.redirect_stdout(io.StringIO()) as buf:
            rec = reconcile_increments(np.array(incr), level_initial=B[0], level_terminal=B[-1])
        for s, L, lev in zip(states, levels, B):
            print("   %-18s L = %7.4f   B = %+7.4f" % (s, L, lev))
        print("   increments: " + ", ".join("%+.4f" % r for r in incr))
        print("   " + buf.getvalue().strip())
        gamma_here = next(b["five_numbers"]["slack_Gamma"] for b in targets if b["id"] == tid)
        legs = [{"from": states[i], "to": states[i + 1], "increment": incr[i],
                 "sign": "gain" if incr[i] > 0 else "regression",
                 "exceeds_slack": bool(abs(incr[i]) > gamma_here)}
                for i in range(len(incr))]
        for lg in legs:
            if not lg["exceeds_slack"]:
                print("   leg %s -> %s: |%+.4f| does not exceed Gamma = %.4f, so that leg is "
                      "inside the panel's resolution" % (lg["from"], lg["to"], lg["increment"],
                                                         gamma_here))
        ladders[tid] = {"metric": metric, "states": states, "levels": levels,
                        "audit_levels_B": B, "increments": incr, "legs": legs,
                        "reconciliation": rec,
                        "negative_increments": int(sum(1 for r in incr if r < 0))}

    # ---- the benchmark's own published quantities
    pub = {s: published_metrics(s) for s in sorted(STATE_META)}
    print("\npublished-metric reproduction (per-word LAMBADA perplexity and accuracy):")
    for s in sorted(pub):
        print("   %-18s ppl %8.3f   acc %.4f" % (s, pub[s]["lambada_perplexity_per_word"],
                                                 pub[s]["lambada_accuracy"]))

    accs = []
    for p0, pT, lab in (("gpt2", "gpt2-medium", "GPT-2 124M -> GPT-2 355M"),
                        ("pythia-160m@1k", "pythia-160m@143k", "Pythia-160m step 1k -> step 143k")):
        if all("%s/greedy_ok" % s in BLOCKS for s in (p0, pT)):
            accs.append(accuracy_comparison(p0, pT, lab))
    us = union_sensitivity(targets)
    print("\nunion over every quote scored on this one panel (N = %d):" % us["N_union"])
    for row in us["per_target"]:
        print("   %-3s Gamma_union %.4f  lower bound %+.4f  %s" %
              (row["id"], row["slack_Gamma_union"], row["lower_bound_union"],
               "FLIPS to non-positive" if row["flips_to_non_positive"]
               else ("positive" if row["positive_under_union"] else "still non-positive")))

    print("\nwhat the token count would have done (tokens inside a passage are dependent):")
    for row in wrong_unit_demo(targets):
        print("   %-3s n=%d units -> %d tokens (%.1f per record): Gamma %.4f -> %.4f, "
              "lower bound %+.4f -> %+.4f%s"
              % (row["id"], row["n_correct_units"], row["n_tokens_wrong"],
                 row["sub_units_per_record"],
                 next(t["five_numbers"]["slack_Gamma"] for t in targets if t["id"] == row["id"]),
                 row["slack_if_tokens_used"], row["correct_lower_bound"],
                 row["lower_bound_if_tokens_used"],
                 "   <- flips a non-positive result to positive" if row["would_flip_a_negative_to_positive"] else ""))

    print("\naccuracy delta against its worst-case paired radius:")
    for a in accs:
        print("   %-36s %+.4f  vs radius %.4f  ->  %s" %
              (a["comparison"], a["accuracy_delta"], a["worst_case_paired_radius_at_delta_0.05"],
               "exceeds" if a["delta_exceeds_its_worst_case_paired_radius"] else "DOES NOT exceed"))

    out = {
        "unit": "nats",
        "vocabulary": {"slack": "Gamma", "headline": "lower bound on improvement = G - Gamma"},
        "panel": {k: META[k] for k in ("panel_repo", "panel_revision", "panel_file",
                                       "panel_sha256", "n_units")},
        "declaration_sha256": META["declaration_sha256"],
        "environment": {"torch": META["torch"], "device": META["device"]},
        "states_scored": META["states"],
        "targets": targets,
        "union_sensitivity": union_sensitivity(targets),
        "anti_conservative_unit_demo": wrong_unit_demo(targets),
        "published_claim": PUBLISHED_CLAIM,
        "revision_ladders": ladders,
        "published_metric_reproduction": pub,
        "accuracy_comparisons": accs,
    }
    (HERE / "report.json").write_text(json.dumps(out, indent=2, default=float))
    print("\nwrote", HERE / "report.json")


if __name__ == "__main__":
    main()
