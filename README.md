# Audit Compression Progress

Reproducibility artifacts for the preprint **"Signed Compression Progress on a Sealed Audit is Goodhart-Resistant"** ([arXiv:2606.11417](https://arxiv.org/abs/2606.11417)).

Signed compression progress measured on a fixed, sealed audit loss telescopes to endpoint audit improvement, giving a zero false-positive budget; for a finite audit panel the cumulative empirical reward is bounded by the true audit improvement plus a `2*Delta_n` deviation budget. This repository hosts the two artifacts behind the paper.

## Contents

- **`AuditCP/`**: the machine-checked core (Lean 4 / Mathlib). Self-contained, with Mathlib as the only build dependency, pinned to an exact commit. Telescoping, the finite-audit `2*Delta_n` bound, finite Gibbs, and the conditional entropy floor are fully proved and axiom-audited. See [`AuditCP/README.md`](AuditCP/README.md).
- **`experiments/`**: the ARC-TGI experiment code (curriculum reward ablation, finite-audit concentration, the adaptive scalar-feedback holdout attack with its release defenses, and the boundary witnesses), plus `results_data/` for measured data that the code reads back.
- **`notebooks/`**: [`audit_cp_report.ipynb`](notebooks/audit_cp_report.ipynb), which turns three vectors of
  per-audit-unit losses into the five reported numbers and the public report object.
- **`examples/`**: the measurement applied to published results, indexed in [`examples/README.md`](examples/README.md). [`examples/lambada-openai/`](examples/lambada-openai/README.md) re-expresses GPT-2's LAMBADA table and a Pythia-160m training run in the five numbers, on one sealed panel.
- **`dist/`**: downloadable snapshots, `AuditCP_lean.zip` (the Lean project) and `auditcp_experiments.zip` (code plus per-seed result shards).

## Lean: build and verify

```sh
cd AuditCP
bash verify.sh        # lake exe cache get, then lake build, then the axiom audit (Check.lean)
```
Expected: `lake build` completes with no errors and no `sorry`, and the axiom audit reports that every core theorem depends only on `[propext, Classical.choice, Quot.sound]`.

## Experiments: requirements and use

Python 3.9+ with `numpy`, `torch`, and `matplotlib`. The task source is the ARC-TGI generators (the `simon-arc-lab` project, pinned commit `d8a2621`); clone it and point the code at it through the `ARC_TGI_ROOT` environment variable.

```sh
export ARC_TGI_ROOT=/path/to/simon-arc-lab
cd experiments
python3 cp_experiments.py c1 --scale full --seed 0      # one experiment, one seed
python3 e7_multiseed.py 20                               # 20-seed E7 power calibration + scaling curve
```
`run_parallel.sh` fans the full battery out over (experiment x seed) shards. `make_results_figures.py` and `replot_e7_multiseed.py` regenerate the figures from the result shards.

## Audit level of the untrained model on the sealed panel

`experiments/results_data/c1_panelB_initial_loss.json` holds the initial audit level `L_B(theta_0)` for all 20 camera-ready seeds. The C1 shards report only the terminal level, so this file supplies the second endpoint that the signed gain needs.

**What was measured.** The floored cross-entropy (probability floor `eps = 0.01`, content cells only, natural units) of the freshly initialised, untrained network, on the sealed audit panel `B` of the C1 experiment at `--scale full`. Panel `B` is `panel(seed + 2000, 512, 30, LEARNABLE_TASKS)`: `n = 12288` audit examples, disjoint by seed from the per-step reward probe panel `A` (`seed + 1000`) and from the training stream. The terminal level `L_B(theta_T)` is the `audit_cp` policy's `final_fresh_floored_ce`, read back from the C1 shards, so both endpoints are scored on the same panel under the same loss. `theta_0` is policy-independent: `run_c1` re-seeds torch immediately before `make_model`, so all seven C1 policies share the same initial weights at a given seed.

**Why it is a fixed-model measurement.** Panel `B` is scored exactly once per run, after the last training step. It never enters the reward loop: the per-step audit-CP reward reads panel `A`, and C1 has no early stopping, no checkpoint selection, and no hyperparameter or data selection driven by a panel-`B` score. Because the panel produced no signal that influenced training, the fixed-panel slack applies, with a declared candidate count of `N = 1` for the single pre-declared endpoint pair. Had any panel-`B` score steered training, that route would be invalid and the slack would have to be rebuilt from an honest count of the bits the panel leaked into the transcript.

**Independent unit.** `n` counts audit *examples* (one padded 30x30 grid each), not cells. Cells within a grid are dependent, so the example is the conservative unit.

**Estimator, and what it costs.** The archived panel level is not the unweighted mean of 12,288 per-example losses. `audit_panel_loss` in `experiments/cp_models.py` returns the total floored cross-entropy over every content cell of the panel divided by the total content-cell count, which is a content-cell-weighted mean `sum_i w_i m_i` with `w_i = c_i / sum_j c_j`; it computes no per-example value, and ARC-TGI grids run from 1x1 to 30x30 inside the padded canvas, so the weights vary. Route (c)'s `Delta = R*sqrt(ln(2N/delta)/(2n))` is Hoeffding for an *unweighted* mean of `n` bounded terms. For the weighted level the radius is `Delta*sqrt(n/n_eff)` with `n_eff = (sum_i c_i)^2 / sum_i c_i^2`, and `n_eff <= n` always, so the published `Delta` below is too small for the estimator that produced these levels, in a fixed direction.

The archived measurement stored no per-example cell counts, so `n_eff` cannot be recovered from this record and this repository does not publish a corrected number for it. What the record does fix is the threshold: `G > Gamma*sqrt(n/n_eff)` exactly while `n_eff > 2*R^2*ln(2N/delta)/G^2 = 289`, out of `n = 12288`. Since `n_eff >= n*mean(c)/max(c)` and `max(c) <= 900` on a 30x30 canvas, a panel averaging more than 21.2 content cells per example clears it on its own. Neither quantity is settled here.

`cp_models.audit_panel_loss` now also returns `floored_ce_per_example` (the unweighted mean of per-example means, which route (c) prices exactly) together with `sum_cells`, `sum_cells_sq` and `n_effective`, and `c1_panelB_initial_loss.py` records them per seed, so a re-run measures both readings and pins `n_eff` down. The archived numbers predate that.

**Aggregate over the 20 seeds** (nats; sd is the sample standard deviation, `ddof=1`). The lower bound and the ratio are the published route (c) arithmetic and are exact for the unweighted reading of the panel level; under the archived cell-weighted estimator they are conditional on `n_eff > 289`:

| quantity | value |
| --- | --- |
| mean `L_B(theta_0)` | 2.4841 (sd 0.0411) |
| mean `L_B(theta_T)` | 1.7476 (sd 0.0301) |
| mean signed gain `G` | 0.7366 (sd 0.0468) |
| `Delta` | 0.056421 |
| slack `Gamma = 2*Delta` | 0.112841 |
| lower bound on improvement `G - Gamma` | 0.6237 (unweighted reading; conditional on `n_eff > 289` under the archived estimator) |
| discrimination ratio `G / Gamma` | 6.53 (same condition) |
| `n_eff` of the archived level | not recorded |

The slack is `Delta = R * sqrt(ln(2N/delta) / (2n))` with `R = -ln 0.01 = 4.6052`, `delta = 0.05`, `N = 1`, `n = 12288`, and `Gamma = 2*Delta`, two-sided over the endpoints: an upper deviation at `theta_0` and a lower one at `theta_T`. The headline claim is the lower bound on improvement, `G - Gamma`; the discrimination ratio `G / Gamma` is dimensionless, comparable across substrates, and exceeds 1 exactly when that bound is positive.

The notebook publishes this run's report object with `lower_bound_on_improvement` and `discrimination_ratio` set to `null` and a `bound_status` naming the estimator mismatch, rather than printing a number its slack does not cover. The unweighted arithmetic above is reported alongside, as arithmetic.

Seed by seed the lower bound runs from 0.5266 to 0.6981 and is positive in 20 of 20 seeds. Each seed draws its own independent panel `B`, so that is the single-seed statement at `delta = 0.05` applied seed by seed, not a simultaneous 95% statement across all 20, which would need a union bound over seeds.

Regenerate:

```sh
export ARC_TGI_ROOT=/path/to/simon-arc-lab
cd experiments
python3 c1_panelB_initial_loss.py                    # measure all 20 seeds, then aggregate
python3 c1_panelB_initial_loss.py --aggregate-only   # recompute the aggregate block only
```

The script rebuilds `theta_0` from the `run_c1` prefix, saves after every seed so an interrupted run resumes, and exits non-zero if the aggregate stops matching the values above. It reads `L_B(theta_T)` from `results_data/c1_seed<S>.json` when those shards have been unpacked, and otherwise straight out of `dist/auditcp_experiments.zip`.

## Notebook: the five reported numbers

`notebooks/audit_cp_report.ipynb` computes the report for a run: terminal level against the
benchmark-owned reference, signed gain, slack, lower bound on improvement, and discrimination ratio,
all in nats. It takes arrays of per-audit-unit losses rather than model objects, so it is
framework-agnostic; the core needs only `numpy`, and an optional cell shows how to produce the arrays
from a torch model.

The notebook implements all four slack routes (complete verifier, fresh endpoints, fixed panel,
reused panel with a bounded transcript) and enforces the three declarations they depend on, on the
same call that computes the number.

- **How the panel was used.** The fixed-panel route is refused for a panel whose scores steered
  training. The declaration is immutable once made, a steering panel cannot declare fewer than one
  released bit, and a route (c) or (d) slack carries the panel it was priced under, so it cannot be
  assembled by hand around the check.
- **What one audit unit is.** Every route that consumes an `n` refuses a declared unit that is a
  sub-unit of a record (a token, a cell, a frame), and the report object refuses to publish under
  one. The slack's `n`, the length of the loss vectors and the published unit count have to agree.
- **Which estimator produced the level.** The routes price the unweighted mean of `n` per-record
  losses. A level that pools sub-units across records is a weighted mean and needs `n_eff`;
  declaring one without `n_eff` raises rather than falling back on the unweighted radius.

It also sizes a panel to the improvement it has to resolve, and reproduces the ARC-TGI numbers from
the paper under assertion, then prices what that run's archived estimator costs.

```sh
python3 -m pip install numpy jupyter
jupyter notebook notebooks/audit_cp_report.ipynb
```

The notebook runs top to bottom with no arguments; its Section 9 asserts the ARC-TGI values against
the archive and fails the run if they move. The worked example below does not reimplement any of
this: `examples/lambada-openai/report.py` executes the notebook's Sections 1 to 8 and calls its
`declare_panel`, `compute_slack`, `five_numbers`, `audit_cp_report` and `reconcile_increments`
directly, so editing the notebook changes the example's numbers.

## Example: a published result in the five numbers

[`examples/lambada-openai/`](examples/lambada-openai/README.md) applies the measurement to
Radford et al. (2019), Table 3: LAMBADA perplexity falls from 35.13 to 15.60 and accuracy rises from
45.99 to 55.48 percent between the 117M and 345M GPT-2 models. The same 5,153-passage panel also
carries four released revisions of Pythia-160m, so one training run can be measured alongside the
two model sizes. Route (c), `delta = 0.05`, probability floor 0.01, one audit unit per passage.

| target | `G` | `Gamma` | `G - Gamma` | `G / Gamma` |
|---|---|---|---|---|
| GPT-2 124M to 355M, LAMBADA final word | +0.6799 | 0.636342 | **+0.0436** | 1.07 |
| GPT-2 124M to 355M, whole passage | +0.2392 | 0.636342 | **-0.3971** | 0.38 |
| Pythia-160m step 1k to 143k, final word | +3.4868 | 0.684865 | **+2.8019** | 5.09 |
| Pythia-160m step 1k to 143k, whole passage | +0.9433 | 0.684865 | **+0.2584** | 1.38 |

The whole-passage GPT-2 comparison is reported as non-positive: no improvement is demonstrated at
that panel's resolution. The final-word GPT-2 bound is positive by 0.0436 nats at its own `N = 2`
and turns negative at the `N = 12` union over every quote scored on the panel, so it sits on the
boundary and its sign depends on an accounting choice that is declared rather than derived.

**The published metrics were re-measured, not carried over.** Scoring the released checkpoints on
the released evaluation file gives LAMBADA perplexity 40.06 for `gpt2` and 18.27 for `gpt2-medium`,
against the paper's 35.13 and 15.60; the paper documents the invertible de-tokenizers and the
stop-word filter that account for the gap, and releases neither. In log space the paper's gain is
0.8118 nats and this reproduction's is 0.7853, while the two levels sit 0.131 and 0.158 nats off the
paper's. Undisclosed preprocessing moves the level by about five times what it moves the difference,
which is an argument for reporting the signed gain alongside the level.

**What the measurement makes available.** A lower bound in nats whose slack contains `n`, `R`,
`delta` and `N` and no term in the parameter count, the step count, the optimizer or the trajectory,
so the same panel prices a 143,000-step adaptive run and a two-model size step identically. A
resolution known before any gradient step: this panel demonstrates nothing smaller than 0.64 nats on
the GPT-2 targets and 0.68 on the Pythia targets, and resolving 0.10 nats would take 208,661
independent passages against the 5,153 it holds. And a dimensionless discrimination ratio, the one
quantity here comparable across the two tokenizers, at 1.07 for the published size step against 5.09
for the training run of a model with a third as many parameters. The example also prices what a
token count instead of a passage count would have bought (it turns the negative whole-passage result
positive), how many transcript bits each bound absorbs under route (d) (2.9 for the GPT-2 target,
185.5 for Pythia), and a negative increment in Pythia's own released trajectory whose increments
still reconcile to the endpoints exactly.

`panel_declaration.json` fixes the panel, the unit, both loss functions, `alpha`, `delta`, the route
and the six model states. It was hashed before any state was scored, and that hash is stamped into
both files in `raw/` and into `report.json`, which `report.py` checks before it reads them.

```sh
cd examples/lambada-openai
python3 report.py         # rebuilds report.json from the per-passage losses in raw/, no downloads
python3 score_states.py   # re-scores the six pinned checkpoints, about 42 minutes on MPS
```

## Citation

```bibtex
@article{mittal2026signed,
  title   = {Signed Compression Progress on a Sealed Audit is Goodhart-Resistant},
  author  = {Mittal, Ayush and Gupta, Dhruv},
  journal = {arXiv preprint arXiv:2606.11417},
  year    = {2026}
}
```

## License

Apache-2.0 (see `AuditCP/LICENSE`).
