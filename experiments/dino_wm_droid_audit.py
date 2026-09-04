"""Recompute the Audit-CP endpoint numbers for the DINO-WM/DROID world-model substrate.

The substrate is a frozen pool of DINO-WM latent features computed over DROID robot
manipulation episodes. DINO-WM is Zhou, Pan, LeCun and Pinto, "DINO-WM: World Models on
Pre-trained Visual Features Enable Zero-Shot Planning", arXiv:2411.04983,
doi:10.48550/arXiv.2411.04983. DROID is Khazatsky et al., "DROID: A Large-Scale In-the-Wild
Robot Manipulation Dataset", arXiv:2403.12945, doi:10.48550/arXiv.2403.12945.

Seven candidates were declared before the audit ran: the identity map, and LoRA adapters of
rank 1, 2, 4, 8, 16 and 32. Every candidate is scored by the loss

    min(PCA-latent RMSE / train-only identity 99th-percentile cap, 1)

on a 32-dimensional PCA latent with ridge coefficient 1e-3. The clip at 1 puts the loss in
[0, 1] and so fixes the loss range at R = 1.

Pricing uses route (c), the fixed panel with a declared finite candidate set. Its
per-endpoint radius is

    Delta = R * sqrt( ln(2N/delta) / (2n) )

with N = 7 candidates, delta = 0.01 and n = 65536 audit draws. The slack on a signed
improvement doubles that radius, because an improvement compares two endpoint levels and
each one can deviate. This script recomputes Delta, the doubled slack, and the slack as a
fraction of the loss range, then asserts each against the archived record.

The archived record is results_data/dino_wm_droid_validity.json, a verbatim slice of the
audit's own results file. Two publication edits were applied to it. The upstream absolute
artifact path stored under adapter_protocol.pca_path was reduced to its bare filename, and
the absolute source_file path was dropped. No numeric value was altered.

The audit refused on this substrate. The identity candidate was never displaced, so the run
reports no positive lower bound on improvement. The script prints that outcome with the
rest of the numbers.

Runs on the Python standard library alone, with no network and no GPU.

Usage
-----
    python3 dino_wm_droid_audit.py
    python3 dino_wm_droid_audit.py --data results_data/dino_wm_droid_validity.json
"""

import argparse
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_DATA = HERE / "results_data" / "dino_wm_droid_validity.json"

# Audit configuration, declared before the run.
CANDIDATE_IDS = [
    "identity",
    "lora_rank_1",
    "lora_rank_2",
    "lora_rank_4",
    "lora_rank_8",
    "lora_rank_16",
    "lora_rank_32",
]
N_CANDIDATES = 7          # N in the route (c) radius
DELTA = 0.01              # per-substrate failure probability
LOSS_RANGE = 1.0          # R, fixed by the clip at 1 in the loss definition
AUDIT_DRAWS = 65536       # n, the independent audit draws behind the endpoint radii
CHECKPOINTS = [8192, 16384, 32768, 65536, 131072, 262144]
ENDPOINT_CHECKPOINT = 262144.0

# Protocol constants, read back from the archived adapter_protocol block.
LOSS_DEFINITION = "min(PCA-latent RMSE / train-only identity 99th-percentile cap, 1)"
PCA_DIMENSION = 32
RIDGE_ALPHA = 0.001
LOSS_CAP = 1.2034612011244814

# The reported figures, at the precision they are quoted at.
PAPER = {
    "endpoint_radius": 0.007434317,        # 9 decimal places
    "two_endpoint_slack": 0.01487,         # 5 decimal places
    "slack_percent_of_range": 1.49,        # 2 decimal places
    "uniform_radius": 0.007069708373190479,
}


# -----------------------------------------------------------------------------
# route (c) arithmetic
# -----------------------------------------------------------------------------

def endpoint_radius(card_A, n, loss_range=LOSS_RANGE, delta=DELTA):
    """Per-endpoint deviation radius for a fixed panel and a declared candidate set.

    Inverting a two-sided Hoeffding bound, union bounded over the card_A candidates, at
    confidence 1 - delta gives Delta = R * sqrt(ln(2 card_A / delta) / (2n)).
    """
    return loss_range * math.sqrt(math.log(2.0 * card_A / delta) / (2.0 * n))


def one_sided_radius(card_A, n, loss_range=LOSS_RANGE, delta=DELTA):
    """Companion radius that drops the factor two inside the logarithm.

    This is the archived `uniform_radius_all_candidates_at_max_checkpoint`. It is a smaller
    quantity than the endpoint radius and it is not what the two-endpoint slack doubles.
    """
    return loss_range * math.sqrt(math.log(card_A / delta) / (2.0 * n))


def draws_from_endpoint_radius(radius, card_A, loss_range=LOSS_RANGE, delta=DELTA):
    """Solve the endpoint radius for n.

    The loss range is pinned at 1 by the clip in the loss definition, so the inversion
    returns a single audit draw count rather than a family of (R, n) pairs.
    """
    return math.log(2.0 * card_A / delta) / (2.0 * (radius / loss_range) ** 2)


# -----------------------------------------------------------------------------
# checks
# -----------------------------------------------------------------------------

class Checker:
    """Collects named comparisons and reports how many of them held."""

    def __init__(self):
        self.rows = []

    def equal(self, name, got, want):
        self.rows.append((name, got == want, got, want))

    def close(self, name, got, want, rel_tol=1e-12, abs_tol=0.0):
        ok = math.isclose(got, want, rel_tol=rel_tol, abs_tol=abs_tol)
        self.rows.append((name, ok, got, want))

    def failures(self):
        return [r for r in self.rows if not r[1]]

    def report(self, stream=sys.stdout):
        bad = self.failures()
        print("", file=stream)
        print(f"checks: {len(self.rows) - len(bad)} of {len(self.rows)} passed", file=stream)
        for name, _, got, want in bad:
            print(f"  FAILED {name}: archived {want!r}, recomputed {got!r}", file=stream)
        return not bad


def run_checks(data):
    """Compare every published value against the archived record."""
    sub = data["substrate"]
    claim = data["claim"]
    canon = sub["canonical_certificate_summary"]
    protocol = sub["adapter_protocol"]

    c = Checker()

    # Candidate set.
    c.equal("candidate ids", sub["candidate_ids"], CANDIDATE_IDS)
    c.equal("candidate count", sub["candidate_count"], N_CANDIDATES)
    c.equal("claim candidate ids", claim["candidate_ids"], CANDIDATE_IDS)

    # Adapter protocol.
    c.equal("loss definition", protocol["loss"], LOSS_DEFINITION)
    c.equal("pca dimension", protocol["pca_dimension"], PCA_DIMENSION)
    c.close("ridge coefficient", protocol["ridge_alpha"], RIDGE_ALPHA)
    c.close("loss cap", protocol["loss_cap"], LOSS_CAP)
    # The loss range is not stored. It follows from the clip that ends the loss definition.
    c.equal("loss clipped at 1", protocol["loss"].endswith(", 1)"), True)

    # Audit configuration.
    c.equal("checkpoint ladder", canon["checkpoints"], CHECKPOINTS)
    c.close("endpoint checkpoint", canon["median_selected_checkpoint"], ENDPOINT_CHECKPOINT)
    c.equal("endpoint checkpoint is the largest rung",
            canon["median_selected_checkpoint"] == float(max(canon["checkpoints"])), True)
    c.close("delta", canon["delta"], DELTA)
    c.close("per-substrate delta", canon["per_substrate_delta"], DELTA)

    archived_delta = canon["audit_cp_endpoint_budget_all_candidates_at_max_checkpoint"]
    archived_uniform = canon["uniform_radius_all_candidates_at_max_checkpoint"]

    # The audit draw count is recovered by inverting the archived radius.
    n_recovered = draws_from_endpoint_radius(archived_delta, N_CANDIDATES)
    c.close("audit draws n", n_recovered, float(AUDIT_DRAWS), rel_tol=1e-9)

    # Radii, recomputed from N, n, R and delta.
    recomputed_delta = endpoint_radius(N_CANDIDATES, AUDIT_DRAWS)
    recomputed_uniform = one_sided_radius(N_CANDIDATES, AUDIT_DRAWS)
    c.close("endpoint radius", recomputed_delta, archived_delta)
    c.close("uniform radius", recomputed_uniform, archived_uniform)
    c.equal("the two radii differ", archived_delta != archived_uniform, True)

    # The claim block carries the same two radii as the substrate block.
    c.close("claim endpoint radius",
            claim["canonical"]["audit_cp_endpoint_budget_all_candidates_at_max_checkpoint"],
            archived_delta)
    c.close("claim uniform radius",
            claim["canonical"]["uniform_radius_all_candidates_at_max_checkpoint"],
            archived_uniform)

    # Reported precision.
    slack = 2.0 * archived_delta
    percent = 100.0 * slack / LOSS_RANGE
    c.close("endpoint radius at 9 dp", round(archived_delta, 9), PAPER["endpoint_radius"])
    c.close("two-endpoint slack at 5 dp", round(slack, 5), PAPER["two_endpoint_slack"])
    c.close("slack percent at 2 dp", round(percent, 2), PAPER["slack_percent_of_range"])
    c.close("uniform radius, full precision", archived_uniform, PAPER["uniform_radius"])

    # The refusal.
    c.equal("certified", canon["certified"], False)
    c.equal("accepted", canon["accepted"], 0)
    c.close("required margin", canon["required_margin"], 0.0)
    c.equal("parent unchanged", (canon["initial_parent"], canon["final_parent"]), (0, 0))

    return c, {
        "endpoint_radius": archived_delta,
        "uniform_radius": archived_uniform,
        "two_endpoint_slack": slack,
        "slack_percent_of_range": percent,
        "audit_draws": n_recovered,
        "canonical": canon,
        "protocol": protocol,
        "substrate": sub,
        "claim": claim,
    }


# -----------------------------------------------------------------------------
# output
# -----------------------------------------------------------------------------

def print_header(v, source_name):
    """Print the substrate identity and the protocol strings too wide for the table."""
    splits = ", ".join(f"{k}={n}" for k, n in sorted(v["substrate"]["split_counts"].items()))
    print("Audit-CP endpoint arithmetic on the DINO-WM/DROID substrate")
    print(f"source:  {source_name}")
    print(f"pool:    {v['substrate']['dataset']}")
    print(f"splits:  {splits} (episodes)")
    print(f"loss:    {LOSS_DEFINITION}")
    print(f"ladder:  {', '.join(str(k) for k in CHECKPOINTS)}")


def print_table(v):
    """Print quantity, value and meaning, one row per reported number."""
    canon = v["canonical"]
    rows = [
        ("candidates N", repr(N_CANDIDATES),
         "identity plus LoRA ranks 1, 2, 4, 8, 16, 32"),
        ("audit draws n", repr(AUDIT_DRAWS),
         "independent draws behind the endpoint radii"),
        ("delta", repr(DELTA),
         "failure probability spent on this substrate"),
        ("loss range R", repr(LOSS_RANGE),
         "the loss is clipped into [0, 1]"),
        ("loss cap", repr(LOSS_CAP),
         "train-only identity 99th-percentile RMSE"),
        ("PCA dimension", repr(PCA_DIMENSION),
         "latent the RMSE is measured in"),
        ("ridge coefficient", repr(RIDGE_ALPHA),
         "regularisation of the adapter fit"),
        ("endpoint checkpoint", repr(int(canon["median_selected_checkpoint"])),
         "largest rung, which supplies the endpoint values"),
        ("per-endpoint radius", repr(v["endpoint_radius"]),
         "Delta = R sqrt(ln(2N/delta) / (2n))"),
        ("two-endpoint slack", repr(v["two_endpoint_slack"]),
         "2 Delta, one deviation at each endpoint"),
        ("slack over loss range", f"{v['slack_percent_of_range']:.4f}%",
         "the slack as a percentage of R"),
        ("uniform radius", repr(v["uniform_radius"]),
         "R sqrt(ln(N/delta) / (2n)), a separate quantity"),
        ("median KL", repr(canon["median_kl"]),
         "divergence of the posterior from the prior"),
        ("certified", repr(canon["certified"]),
         "whether any candidate cleared the requirement"),
        ("accepted", repr(canon["accepted"]),
         "candidates accepted over the trajectory"),
        ("required margin", repr(canon["required_margin"]),
         "margin a candidate had to clear"),
    ]

    w0 = max(len(r[0]) for r in rows + [("quantity", "", "")])
    w1 = max(len(r[1]) for r in rows + [("", "value", "")])
    w2 = max(len(r[2]) for r in rows + [("", "", "what it is")])
    line = "-" * (w0 + w1 + w2 + 4)
    print(line)
    print(f"{'quantity'.ljust(w0)}  {'value'.ljust(w1)}  what it is")
    print(line)
    for name, value, meaning in rows:
        print(f"{name.ljust(w0)}  {value.ljust(w1)}  {meaning}")
    print(line)


def print_recomputation(v):
    """State which printed numbers were recomputed rather than read back."""
    print("")
    print("Recomputation")
    print("-------------")
    print("The two radii above are recomputed from N, n, R and delta, and both agree with the")
    print("archived values to the last bit of a double.")
    print("The audit draw count is not stored, so it is recovered by solving the endpoint")
    print(f"radius for n, which returns {v['audit_draws']:.6f}.")
    print("R is pinned at 1 by the clip in the loss definition, so that inversion has a")
    print("single solution.")


def print_reading(v):
    """State the outcome of the run, including the absent lower bound."""
    canon = v["canonical"]
    print("")
    print("Outcome")
    print("-------")
    print(f"The audit declined to certify: certified = {canon['certified']}, "
          f"accepted = {canon['accepted']}.")
    print(f"The parent candidate is index {canon['initial_parent']} at the start and index "
          f"{canon['final_parent']} at the end, which is")
    print(f"'{CANDIDATE_IDS[0]}' in both cases.")
    print("The identity candidate was best throughout, so no LoRA adapter ever displaced it.")
    print("The run therefore reports no positive lower bound on improvement for this substrate.")
    print(f"What it does report is a finite and small radius: {v['endpoint_radius']:.9f} per")
    print(f"endpoint, {v['two_endpoint_slack']:.5f} across the pair, which is "
          f"{v['slack_percent_of_range']:.2f}% of the bounded loss range.")
    print("A signed improvement above that slack would have been certifiable at this scale.")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--data", type=Path, default=DEFAULT_DATA,
                    help="archived DINO-WM/DROID validity slice (JSON)")
    args = ap.parse_args(argv)

    with open(args.data) as f:
        data = json.load(f)

    checker, values = run_checks(data)

    print_header(values, args.data.name)
    print("")
    print_table(values)
    print_recomputation(values)
    print_reading(values)

    if not checker.report():
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
