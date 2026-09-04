# Experiments

Each section below documents one script in this directory: what it computes, how to
run it, and where its inputs come from.

## MMLU-ProX language battery

`mmluprox_battery.py` recomputes the MMLU-ProX numbers behind the paper's
Blackwell-refinement panel and asserts each published value. It reads the archived
score table in `results_data/mmluprox_scores.json` and runs offline on the Python 3
standard library.

```
python3 mmluprox_battery.py                     # print the panel numbers and check them
python3 mmluprox_battery.py --check-aggregators # add the aggregator monotonicity counts
python3 mmluprox_battery.py --scores PATH       # read the score table from elsewhere
```

The script exits nonzero if any published value fails to reproduce.

### What it computes

MMLU-ProX presents one question set in 29 languages, so eight systems are scored on
11,759 parallel question identities under 29 presentations. The script prices the
resulting presentation degree of freedom two ways.

The first is a finite-sample screen. A precommitted comparison between two named
systems on one named language carries a paired radius of 2.50 points. Choosing the
system pair and the language after looking at the table spans 28 x 29 = 812
comparisons, and the radius covering all of them simultaneously is 4.20 points. Of the
23 model-pair reversals in the table, 11 survive that simultaneous radius.

The second is the battery separation profile. At a target scale epsilon the script keeps
the system pairs whose mean absolute gap across the 29 presentations is at least epsilon,
then reports how much separation survives the simultaneous radius. At epsilon = 5 points
every one of the 29 individual languages retains zero separation, while the 29-language
battery retains 6.1966 points. At epsilon = 7.5 points, 21 languages retain positive
separation with median 1.90, English retains 0.40, the best single language retains 9.90,
and the battery retains 10.30.

The printed table gives the battery profile at epsilon in {2.5, 5.0, 7.5, 10.0}, which is
6.1966, 6.1966, 10.2966 and 30.7966 points and is nondecreasing. Two further blocks
report a leave-one-language-out reselection at epsilon = 7.5, where the count of languages
with positive separation falls from 21 to 18, the median falls from 1.90 to 0.80, and the
largest single shift is 3.90 points; and the rank agreement with English, where the mean
Kendall tau_b over the 28 non-English presentations is 0.488 with a minimum of 0.143, and
selecting on English alone incurs 21.7 points of maximum language-specific regret.

Aggregation across presentations takes the maximum gap. Mean aggregation is excluded
because it does not inherit Blackwell monotonicity: the mean-aggregated profile can fall
when a presentation is added, which the ordering of a battery over its sub-batteries
forbids. Passing `--check-aggregators` draws random nested subsets of the 29
presentations and reports how many orders each aggregator decreases on.

### Data provenance

The accuracies in `results_data/mmluprox_scores.json` are reproduced from the MMLU-ProX
benchmark release and are not results of this repository. No model was run to produce
them. The archive holds the published aggregate accuracy per system and language, which
is the granularity the benchmark release reports and the only granularity these
statistics need. Per-question response records are not redistributed here.

> Weihao Xuan, Rui Yang, Heli Qi, Qingcheng Zeng, Yunze Xiao, Aosong Feng, Dairui Liu,
> Yun Xing, Junjue Wang, Fan Gao and others. MMLU-ProX: A Multilingual Benchmark for
> Advanced Large Language Model Evaluation. Conference on Empirical Methods in Natural
> Language Processing, pages 1515-1546, 2025.

The question count of 11,759 is the 11,829 MMLU-ProX test items less the 70 items
reserved as few-shot demonstrations. The 29 presentations translate a single question
set, so a question identity is the independent unit and language-question cells are not
counted separately.
