#!/usr/bin/env python3
"""Separation profile of the MMLU-ProX language battery under a simultaneous screen.

MMLU-ProX presents one question set in 29 languages, so the eight archived systems
are scored on 11,759 parallel question identities under 29 different presentations.
A benchmark comparison therefore has a presentation degree of freedom that a single
accuracy number hides. This script prices that degree of freedom two ways and prints
the result.

The first way is a finite-sample screen. A precommitted comparison between two named
systems on one named language carries a paired radius of 2.50 points. Reading all 28
system pairs on all 29 languages and reporting whichever comparison looks best is 812
comparisons, and the radius that covers all of them simultaneously is 4.20 points.
Gaps below the simultaneous radius are not separations.

The second way is the battery separation profile. Fix a target scale epsilon, keep the
system pairs whose mean absolute gap across the 29 presentations is at least epsilon,
and ask how much separation survives the simultaneous radius. Read one presentation at
a time and the answer at epsilon = 5 is zero for every one of the 29 languages. Read the
whole battery and the answer is 6.1966 points. The battery resolves a distinction that
none of its individual presentations resolves.

Aggregation across presentations takes the maximum gap. A battery transcript refines the
transcript of any sub-battery, so the profile has to be nondecreasing as presentations
are added. Total variation of a joint law is bounded below by the total variation of any
marginal, which makes the maximum the aggregator that inherits that monotonicity. Mean
aggregation is excluded because it does not inherit it, and `--check-aggregators` reruns
both aggregators under random nested subsets of the 29 presentations to show the
violation counts.

Data provenance
---------------
The accuracies in `results_data/mmluprox_scores.json` are reproduced from the MMLU-ProX
benchmark release and are not results of this repository. No model was run to produce
them. The citation is:

    Weihao Xuan, Rui Yang, Heli Qi, Qingcheng Zeng, Yunze Xiao, Aosong Feng,
    Dairui Liu, Yun Xing, Junjue Wang, Fan Gao and others. MMLU-ProX: A
    Multilingual Benchmark for Advanced Large Language Model Evaluation.
    Conference on Empirical Methods in Natural Language Processing,
    pages 1515-1546, 2025.

The archive holds the published aggregate accuracy per system and language, which is the
granularity the benchmark release reports and the only granularity these statistics need.
Per-question response records are not redistributed here.

Usage
-----
    python3 mmluprox_battery.py
    python3 mmluprox_battery.py --scores /path/to/mmluprox_scores.json
    python3 mmluprox_battery.py --check-aggregators

Runs offline on the Python 3 standard library. Every published value is recomputed from
the archived scores and asserted, so a nonzero exit means a reported number moved.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
from collections import Counter
from itertools import combinations

DELTA = 0.05
EPSILON_GRID = (2.5, 5.0, 7.5, 10.0)
DEFAULT_SCORES = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "results_data", "mmluprox_scores.json"
)


# -----------------------------------------------------------------------------
# Statistics
# -----------------------------------------------------------------------------


def paired_radius_pp(n, delta=DELTA):
    """Two-sided radius in points for a precommitted paired accuracy difference.

    The paired difference of two correctness indicators lies in [-1, 1], so Hoeffding
    gives sqrt(2 log(2 / delta) / n) on the [0, 1] scale. Passing delta / m returns the
    radius that covers m comparisons simultaneously by a union bound.
    """
    return 100.0 * math.sqrt(2.0 * math.log(2.0 / delta) / n)


def kendall_tau_b(x, y):
    """Kendall rank correlation with the tie correction, computed on raw scores.

    Ranking is monotone, so the coefficient is the same whether it is taken on the
    accuracies or on their ranks. Ties are broken by neither concordance nor
    discordance and are removed from the corresponding normaliser.
    """
    n = len(x)
    concordant = discordant = 0
    for i, j in combinations(range(n), 2):
        product = (x[i] - x[j]) * (y[i] - y[j])
        if product > 0.0:
            concordant += 1
        elif product < 0.0:
            discordant += 1
    n0 = n * (n - 1) // 2
    tied_x = sum(t * (t - 1) // 2 for t in Counter(x).values())
    tied_y = sum(t * (t - 1) // 2 for t in Counter(y).values())
    return (concordant - discordant) / math.sqrt((n0 - tied_x) * (n0 - tied_y))


def median(values):
    ordered = sorted(values)
    n = len(ordered)
    mid = n // 2
    if n % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


# -----------------------------------------------------------------------------
# Battery analysis
# -----------------------------------------------------------------------------


def load_scores(path):
    with open(path, "r", encoding="utf-8") as handle:
        payload = json.load(handle)
    systems = payload["systems"]
    languages = payload["languages"]
    table = payload["accuracy_pp"]
    for system in systems:
        missing = [lang for lang in languages if lang not in table[system]]
        if missing:
            raise ValueError("system %s is missing languages %s" % (system, missing))
    return payload, systems, languages, table


def battery_profile(gaps, qualifying, observed, radius):
    """Separation the battery retains at one target scale after the screen.

    The inner maximum reads a system pair across every observed presentation and keeps
    its widest gap. The outer minimum is the weakest qualifying pair, which is what the
    profile reports. Subtracting the radius and flooring at zero removes the part of the
    gap that the finite sample cannot resolve.
    """
    worst_pair = min(max(gaps[pair][lang] for lang in observed) for pair in qualifying)
    return max(0.0, worst_pair - radius)


def mean_aggregated_profile(gaps, qualifying, observed, radius):
    """The same profile with the presentation-level maximum replaced by a mean.

    Reported only by `--check-aggregators`, which shows that this aggregator decreases
    when presentations are added and so cannot carry the battery-refines-sub-battery
    claim.
    """
    worst_pair = min(
        sum(gaps[pair][lang] for lang in observed) / len(observed)
        for pair in qualifying
    )
    return max(0.0, worst_pair - radius)


def analyse(payload, systems, languages, table):
    n_questions = payload["questions_per_language"]
    pairs = list(combinations(systems, 2))
    comparisons = len(pairs) * len(languages)

    single_radius = paired_radius_pp(n_questions)
    simultaneous_radius = paired_radius_pp(n_questions, DELTA / comparisons)

    signed = {
        pair: {lang: table[pair[0]][lang] - table[pair[1]][lang] for lang in languages}
        for pair in pairs
    }
    gaps = {
        pair: {lang: abs(value) for lang, value in row.items()}
        for pair, row in signed.items()
    }

    # A pair reverses when one system leads on some presentation and trails on another.
    # It survives a screen when both leads exceed that screen's radius.
    reversals = screened_single = screened_simultaneous = 0
    for pair in pairs:
        lead_a = max(signed[pair].values())
        lead_b = max(-value for value in signed[pair].values())
        reverses = lead_a > 0.0 and lead_b > 0.0
        reversals += reverses
        screened_single += reverses and min(lead_a, lead_b) > single_radius
        screened_simultaneous += reverses and min(lead_a, lead_b) > simultaneous_radius

    # The target-side selection keeps pairs whose mean absolute gap over the whole
    # battery reaches the scale being asked about.
    mean_gap = {
        pair: sum(gaps[pair].values()) / len(languages) for pair in pairs
    }

    profile = []
    retention = {}
    for epsilon in EPSILON_GRID:
        qualifying = [pair for pair in pairs if mean_gap[pair] >= epsilon]
        if not qualifying:
            continue
        profile.append(
            {
                "epsilon_pp": epsilon,
                "qualifying_pairs": len(qualifying),
                "battery_pp": battery_profile(
                    gaps, qualifying, languages, simultaneous_radius
                ),
            }
        )

        # Per-presentation retention reads one language at a time. It lower-bounds the
        # battery value and carries no monotonicity claim of its own.
        per_language = {}
        leave_one_out = {}
        for lang in languages:
            observed = min(gaps[pair][lang] for pair in qualifying)
            per_language[lang] = max(0.0, observed - simultaneous_radius)

            # The selection criterion averages over all 29 presentations, so each
            # language contributes 1/29 of the criterion that then selects the pairs it
            # is scored on. Reselecting with the language dropped from the criterion
            # breaks that loop and measures how much of its retention came from it.
            held_out = [other for other in languages if other != lang]
            loo_qualifying = [
                pair
                for pair in pairs
                if sum(gaps[pair][other] for other in held_out) / len(held_out) >= epsilon
            ]
            if loo_qualifying:
                observed_loo = min(gaps[pair][lang] for pair in loo_qualifying)
                leave_one_out[lang] = max(0.0, observed_loo - simultaneous_radius)
            else:
                leave_one_out[lang] = 0.0

        shifts = {lang: abs(per_language[lang] - leave_one_out[lang]) for lang in languages}
        largest_shift = max(shifts, key=lambda lang: shifts[lang])
        best_language = max(per_language, key=lambda lang: per_language[lang])
        retention[epsilon] = {
            "per_language": per_language,
            "positive_languages": sum(1 for v in per_language.values() if v > 0.0),
            "median_pp": median(list(per_language.values())),
            "english_pp": per_language["EN"],
            "best_language": best_language,
            "best_pp": per_language[best_language],
            "loo_positive_languages": sum(1 for v in leave_one_out.values() if v > 0.0),
            "loo_median_pp": median(list(leave_one_out.values())),
            "loo_max_shift_pp": shifts[largest_shift],
            "loo_max_shift_language": largest_shift,
        }

    english = [table[system]["EN"] for system in systems]
    tau_to_english = {
        lang: kendall_tau_b(english, [table[system][lang] for system in systems])
        for lang in languages
    }
    non_english = [tau_to_english[lang] for lang in languages if lang != "EN"]
    weakest = min(tau_to_english, key=lambda lang: tau_to_english[lang])

    # Selecting on English alone and then being read in the worst language costs the
    # gap between the English winner and that language's own winner.
    english_winner = max(systems, key=lambda system: table[system]["EN"])
    regret = max(
        max(table[system][lang] for system in systems) - table[english_winner][lang]
        for lang in languages
    )

    return {
        "n_questions": n_questions,
        "n_systems": len(systems),
        "n_languages": len(languages),
        "n_pairs": len(pairs),
        "n_comparisons": comparisons,
        "single_radius_pp": single_radius,
        "simultaneous_radius_pp": simultaneous_radius,
        "reversals": reversals,
        "reversals_surviving_single": screened_single,
        "reversals_surviving_simultaneous": screened_simultaneous,
        "profile": profile,
        "retention": retention,
        "mean_tau_b_non_english": sum(non_english) / len(non_english),
        "min_tau_b": tau_to_english[weakest],
        "min_tau_b_language": weakest,
        "english_winner": english_winner,
        "english_selection_regret_pp": regret,
        "gaps": gaps,
        "mean_gap": mean_gap,
        "pairs": pairs,
        "languages": languages,
    }


def aggregator_monotonicity(result, trials=200, seed=20260812):
    """Count nested-subset orders on which each aggregator decreases.

    Dropping presentations from the observed set garbles the battery transcript without
    touching the target, so a profile that inherits Blackwell monotonicity cannot rise
    when a presentation is removed. Each trial draws a random order of the 29
    presentations and reads the profile off the growing prefix.
    """
    rng = random.Random(seed)
    languages = result["languages"]
    gaps = result["gaps"]
    radius = result["simultaneous_radius_pp"]
    report = {}
    for name, aggregator in (
        ("max", battery_profile),
        ("mean", mean_aggregated_profile),
    ):
        violating = total = 0
        for epsilon in (5.0, 7.5):
            qualifying = [
                pair for pair in result["pairs"] if result["mean_gap"][pair] >= epsilon
            ]
            if not qualifying:
                continue
            for _ in range(trials):
                order = list(languages)
                rng.shuffle(order)
                values = [
                    aggregator(gaps, qualifying, order[: k + 1], radius)
                    for k in range(len(order))
                ]
                total += 1
                if any(values[k + 1] < values[k] - 1e-9 for k in range(len(values) - 1)):
                    violating += 1
        report[name] = {"violating_orders": violating, "orders": total}
    return report


# -----------------------------------------------------------------------------
# Reporting
# -----------------------------------------------------------------------------


def report(result):
    print("MMLU-ProX language battery")
    print("=" * 74)
    print(
        "%d parallel question identities, %d language presentations, %d systems."
        % (result["n_questions"], result["n_languages"], result["n_systems"])
    )
    print(
        "Precommitted two-system paired radius: %.2f points."
        % result["single_radius_pp"]
    )
    print(
        "Simultaneous radius over %d x %d = %d model-pair-language comparisons: "
        "%.2f points."
        % (
            result["n_pairs"],
            result["n_languages"],
            result["n_comparisons"],
            result["simultaneous_radius_pp"],
        )
    )
    print(
        "Model-pair reversals: %d observed, %d survive the simultaneous radius."
        % (result["reversals"], result["reversals_surviving_simultaneous"])
    )
    print()

    print("Battery separation profile, maximum aggregation over presentations")
    print("-" * 74)
    print(
        "%8s  %10s  %12s  %10s  %10s"
        % ("epsilon", "pairs kept", "battery", "languages", "best")
    )
    print(
        "%8s  %10s  %12s  %10s  %10s"
        % ("(points)", "", "(points)", "positive", "single")
    )
    for row in result["profile"]:
        held = result["retention"][row["epsilon_pp"]]
        print(
            "%8.1f  %10d  %12.4f  %10d  %10.2f"
            % (
                row["epsilon_pp"],
                row["qualifying_pairs"],
                row["battery_pp"],
                held["positive_languages"],
                held["best_pp"],
            )
        )
    print()
    print(
        "The profile is nondecreasing in epsilon. Mean aggregation across presentations"
    )
    print(
        "is excluded because it does not inherit Blackwell monotonicity: it can fall as"
    )
    print(
        "presentations are added, which the battery-refines-sub-battery ordering forbids."
    )
    print("Run with --check-aggregators to see the violation counts for both.")
    print()

    held5 = result["retention"][5.0]
    held75 = result["retention"][7.5]
    print("At epsilon = 5 points")
    print("-" * 74)
    print(
        "Individual presentations retaining separation: %d of %d."
        % (held5["positive_languages"], result["n_languages"])
    )
    print("Battery retains %.4f points." % result["profile"][1]["battery_pp"])
    print()

    print("At epsilon = 7.5 points")
    print("-" * 74)
    print(
        "%d languages retain positive separation, median %.2f, English %.2f."
        % (held75["positive_languages"], held75["median_pp"], held75["english_pp"])
    )
    print(
        "Best single presentation %.2f (%s), battery %.2f."
        % (held75["best_pp"], held75["best_language"], result["profile"][2]["battery_pp"])
    )
    print()

    print("Leave-one-language-out selection at epsilon = 7.5 points")
    print("-" * 74)
    print(
        "Positive languages %d -> %d, median %.2f -> %.2f."
        % (
            held75["positive_languages"],
            held75["loo_positive_languages"],
            held75["median_pp"],
            held75["loo_median_pp"],
        )
    )
    print(
        "Largest shift %.2f points (%s)."
        % (held75["loo_max_shift_pp"], held75["loo_max_shift_language"])
    )
    print()

    print("Rank agreement with the English presentation")
    print("-" * 74)
    print(
        "Mean Kendall tau_b over the %d non-English presentations: %.3f."
        % (result["n_languages"] - 1, result["mean_tau_b_non_english"])
    )
    print(
        "Minimum tau_b: %.3f (%s)." % (result["min_tau_b"], result["min_tau_b_language"])
    )
    print(
        "Selecting on English alone (%s) incurs %.1f points of maximum "
        "language-specific regret."
        % (result["english_winner"], result["english_selection_regret_pp"])
    )


# -----------------------------------------------------------------------------
# Published values
# -----------------------------------------------------------------------------


def check_published(result):
    """Assert the values the paper reports for panel (c)."""
    assert result["n_questions"] == 11759, result["n_questions"]
    assert result["n_languages"] == 29, result["n_languages"]
    assert result["n_systems"] == 8, result["n_systems"]

    assert result["n_pairs"] == 28, result["n_pairs"]
    assert result["n_comparisons"] == 812, result["n_comparisons"]
    assert round(result["simultaneous_radius_pp"], 2) == 4.20, result[
        "simultaneous_radius_pp"
    ]
    assert round(result["single_radius_pp"], 2) == 2.50, result["single_radius_pp"]

    profile = [round(row["battery_pp"], 4) for row in result["profile"]]
    assert [row["epsilon_pp"] for row in result["profile"]] == list(EPSILON_GRID)
    assert profile == [6.1966, 6.1966, 10.2966, 30.7966], profile
    assert all(
        profile[i] <= profile[i + 1] for i in range(len(profile) - 1)
    ), profile

    held5 = result["retention"][5.0]
    assert held5["positive_languages"] == 0, held5["positive_languages"]

    held75 = result["retention"][7.5]
    assert held75["positive_languages"] == 21, held75["positive_languages"]
    assert round(held75["median_pp"], 2) == 1.90, held75["median_pp"]
    assert round(held75["english_pp"], 2) == 0.40, held75["english_pp"]
    assert round(held75["best_pp"], 2) == 9.90, held75["best_pp"]
    assert round(result["profile"][2]["battery_pp"], 2) == 10.30

    assert held75["loo_positive_languages"] == 18, held75["loo_positive_languages"]
    assert round(held75["loo_median_pp"], 2) == 0.80, held75["loo_median_pp"]
    assert round(held75["loo_max_shift_pp"], 2) == 3.90, held75["loo_max_shift_pp"]

    assert round(result["mean_tau_b_non_english"], 3) == 0.488, result[
        "mean_tau_b_non_english"
    ]
    assert round(result["min_tau_b"], 3) == 0.143, result["min_tau_b"]
    assert round(result["english_selection_regret_pp"], 1) == 21.7, result[
        "english_selection_regret_pp"
    ]

    assert result["reversals_surviving_simultaneous"] == 11, result[
        "reversals_surviving_simultaneous"
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--scores",
        default=DEFAULT_SCORES,
        help="path to the archived MMLU-ProX score table (default: %(default)s)",
    )
    parser.add_argument(
        "--check-aggregators",
        action="store_true",
        help="count nested-subset orders on which each aggregator decreases",
    )
    parser.add_argument(
        "--trials",
        type=int,
        default=200,
        help="random presentation orders per scale for --check-aggregators",
    )
    args = parser.parse_args()

    payload, systems, languages, table = load_scores(args.scores)
    result = analyse(payload, systems, languages, table)
    report(result)

    if args.check_aggregators:
        print()
        print("Aggregator monotonicity under nested presentation subsets")
        print("-" * 74)
        counts = aggregator_monotonicity(result, trials=args.trials)
        for name in ("max", "mean"):
            row = counts[name]
            print(
                "%-5s aggregation: %d of %d orders decrease when a presentation is added."
                % (name, row["violating_orders"], row["orders"])
            )
        assert counts["max"]["violating_orders"] == 0, counts["max"]
        assert counts["mean"]["violating_orders"] > 0, counts["mean"]

    check_published(result)
    print()
    print("All published values reproduced.")


if __name__ == "__main__":
    main()
