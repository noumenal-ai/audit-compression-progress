# Audit Compression Progress

Reproducibility artifacts for the preprint **"Signed Compression Progress on a Sealed Audit is Goodhart-Resistant"** ([arXiv:2606.11417](https://arxiv.org/abs/2606.11417)).

Signed compression progress measured on a fixed, sealed audit loss telescopes to endpoint audit improvement, giving a zero false-positive budget; for a finite audit panel the cumulative empirical reward is bounded by the true audit improvement plus a `2*Delta_n` deviation budget. This repository hosts the two artifacts behind the paper.

## Contents

- **`AuditCP/`**: the machine-checked core (Lean 4 / Mathlib). Self-contained, with Mathlib as the only build dependency, pinned to an exact commit. Telescoping, the finite-audit `2*Delta_n` bound, finite Gibbs, and the conditional entropy floor are fully proved and axiom-audited. See [`AuditCP/README.md`](AuditCP/README.md).
- **`experiments/`**: the ARC-TGI experiment code (curriculum reward ablation, finite-audit concentration, the adaptive scalar-feedback holdout attack with its release defenses, and the boundary witnesses), plus `results_data/` for measured data that the code reads back.
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

**Independent unit.** `n` counts audit *examples* (one padded 30x30 grid each), not cells. Cells within a grid are dependent, so the example is the conservative unit even though the loss is averaged over content cells.

**Aggregate over the 20 seeds** (nats; sd is the sample standard deviation, `ddof=1`):

| quantity | value |
| --- | --- |
| mean `L_B(theta_0)` | 2.4841 (sd 0.0411) |
| mean `L_B(theta_T)` | 1.7476 (sd 0.0301) |
| mean signed gain `G` | 0.7366 (sd 0.0468) |
| `Delta` | 0.056421 |
| slack `Gamma = 2*Delta` | 0.112841 |
| lower bound on improvement `G - Gamma` | 0.6237 |
| discrimination ratio `G / Gamma` | 6.53 |

The slack is `Delta = R * sqrt(ln(2N/delta) / (2n))` with `R = -ln 0.01 = 4.6052`, `delta = 0.05`, `N = 1`, `n = 12288`, and `Gamma = 2*Delta`, two-sided over the endpoints: an upper deviation at `theta_0` and a lower one at `theta_T`. The headline claim is the lower bound on improvement, `G - Gamma`; the discrimination ratio `G / Gamma` is dimensionless, comparable across substrates, and exceeds 1 exactly when that bound is positive.

Seed by seed the lower bound runs from 0.5266 to 0.6981 and is positive in 20 of 20 seeds. Each seed draws its own independent panel `B`, so that is the single-seed statement at `delta = 0.05` applied seed by seed, not a simultaneous 95% statement across all 20, which would need a union bound over seeds.

Regenerate:

```sh
export ARC_TGI_ROOT=/path/to/simon-arc-lab
cd experiments
python3 c1_panelB_initial_loss.py                    # measure all 20 seeds, then aggregate
python3 c1_panelB_initial_loss.py --aggregate-only   # recompute the aggregate block only
```

The script rebuilds `theta_0` from the `run_c1` prefix, saves after every seed so an interrupted run resumes, and exits non-zero if the aggregate stops matching the values above. It reads `L_B(theta_T)` from `results_data/c1_seed<S>.json` when those shards have been unpacked, and otherwise straight out of `dist/auditcp_experiments.zip`.

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
