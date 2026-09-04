# Audit Compression Progress

A training run that reports progress against a metric it was optimized on cannot be
believed. If the panel the run was scored against also steered the run, the reported
number is unfalsifiable, and the gap between reported and real improvement has no bound.
This is Goodhart's law in its measurement form.

We fix a target distribution `Q` and a reference predictor, score the model's conditional
probability assignments on a panel that training never touched, and report the signed
difference of log losses between the initial and terminal states. Because the quantity is
a difference of a potential rather than a rectified sum of gains, a trajectory that leaves
a state and returns nets exactly zero, and the audited total depends only on its two
endpoints however long the run. Reported progress is therefore net of forgetting by
construction, and a run cannot accumulate credit by cycling.

The measurement licenses a bound rather than an estimate. On a panel of `n` independent
audit units with bounded loss range `R` and `N` candidates declared before scoring,
measured cumulative progress exceeds true progress by at most `2R sqrt(log(2N/delta) /
2n)` with probability at least `1 - delta`. That slack carries no term in the training
horizon and no term in the parameter count, so the same bound covers a longer run or a
larger model without change. Subtracting it from the measured gain gives a lower bound on
improvement that holds at any horizon.

A report is five numbers, not one: the terminal level against the reference, the signed
gain, the slack of the evidence route used, the lower bound on improvement, and the
discrimination ratio of gain to slack. The ratio is dimensionless and exceeds one exactly
when the lower bound is positive.

The measure specialises compression progress in the sense of Schmidhuber to a sealed
target. The ledger identity is the potential-difference construction of Ng, Harada and
Russell. The finite-panel term is Hoeffding's inequality with a union bound over the
declared candidates, the reuse accounting follows the reusable-holdout literature, and the
interface results are Blackwell comparison of experiments. Full citations are in
[`AuditCP/CITATIONS.bib`](AuditCP/CITATIONS.md).

## Contents

- **[`AuditCP/`](AuditCP/)** is the machine-checked thesis in Lean 4, with the argument in
  chapter order and every declaration carrying a one-line statement of what it proves.
- **[`experiments/`](experiments/)** holds the four measured substrates and the archived
  data each script reads back.
- **[`notebooks/audit_cp_report.ipynb`](notebooks/audit_cp_report.ipynb)** turns three
  vectors of per-audit-unit losses into the five reported numbers.
- **[`examples/`](examples/README.md)** applies the measurement to published results.
- **`dist/`** carries downloadable snapshots of the Lean project and the experiment code.

## The Lean thesis

`AuditCP` is the paper's argument in order. The base declares seven types and proves
nothing. Twelve chapters follow, each importing its predecessor, so the import list is the
argument rather than a bibliography.

| chapters | content |
| --- | --- |
| 1 to 3 | the ledger, its exactness, and the finite-audit bound |
| 4 to 7 | the slack, a random envelope, a world-dependent audit law, and priced disclosure |
| 8 to 10 | sealing as a property of the interface, characterised four ways |
| 11 to 12 | the entropy floor, and how to read the instrument |

`AuditCPRL` carries the argument into reinforcement learning across thirteen further
modules, covering potential-based shaping with an estimated potential, audited
self-modification, policy improvement on a reused panel, and state aggregation.

The reinforcement-learning side is `rl-theory-in-lean` by Shangtong Zhang, MIT licensed
and included under `RLTheory/` with its licence at `RLTheory-LICENSE`. Upstream targets
Lean v4.22 while this development targets v4.31, so the copy here is a forward port. No
upstream declaration is removed or restated, the additions are internal helpers the port
required, and every result our crossovers cite exists upstream under the same name.

## Build and verify

```sh
cd AuditCP
lake exe cache get
lake build
```

Mathlib is pinned to an exact commit. The build is sorry-free and every theorem is axiom
audited; `Check.lean` prints the axiom set for each result.

## Reproduce the measurements

Each script reads archived data and asserts the published values, exiting non-zero if any
disagrees. All run on stock Python 3 with no network.

```sh
cd experiments
python3 dino_wm_droid_audit.py     # frozen world-model audit
python3 mmluprox_battery.py        # language battery and its separation profile
python3 cp_experiments.py --help   # the curriculum reward ablation
```

The curriculum ablation and the ARC-TGI panel regenerator draw their tasks from the
`simon-arc-lab` generators, which are not vendored. Clone that repository at the pinned
commit and point the scripts at it:

```sh
git clone https://github.com/neoneye/simon-arc-lab data/arc-tgi
git -C data/arc-tgi checkout d8a2621
export ARC_TGI_ROOT="$PWD/data/arc-tgi"
```

The ARC-TGI worked example is priced at the effective sample size of its cell-weighted
loss, which the archived record carries per seed. `experiments/c1_panelB_initial_loss.py
--force` regenerates every seed's panel from its seed and re-measures those counts; the
regenerated panel reproduces the archived initial level exactly, which is the check that
the counts belong to the panel the archived terminal levels were scored on.

The world-model audit scores seven predeclared candidates on DINO-WM features over DROID
robot data, at a loss range of one. The per-endpoint radius is 0.007434 and the
two-endpoint slack is 1.49% of the range. The identity candidate is best at both ends, so
that run reports no positive lower bound, which the script states rather than omits.

The language battery scores eight systems on 11,759 parallel MMLU-ProX question
identities in 29 languages. At a five-point threshold no individual language retains a
distinction after simultaneous correction, while the 29-language battery retains 6.20
points. Scores are reproduced from Xuan et al. and are not ours. Mean aggregation is
excluded because it does not inherit Blackwell monotonicity, and `--check-aggregators`
demonstrates the failure on random nested subsets.

## Citing

The preprint is [arXiv:2606.11417](https://arxiv.org/abs/2606.11417). Sources for every
inherited result are in [`AuditCP/CITATIONS.md`](AuditCP/CITATIONS.md).
