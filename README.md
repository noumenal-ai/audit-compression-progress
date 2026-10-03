# Signed Compression Progress on a Sealed Audit is Goodhart-Resistant

Ayush Mittal and Dhruv Gupta. Poster at the 2nd Workshop on Lifelong Agent (LLA), COLM 2026.
Preprint: [arXiv:2606.11417](https://arxiv.org/abs/2606.11417).

This repository is the released artifact of the paper. It contains the Lean 4 development that
proves every declaration the paper cites, together with the archived per-seed records, the scripts
that recompute every reported experimental number, and the generators of the paper's figures.

The paper rewards a learner with the signed decrease of its loss on an audit panel that training
never reads. Cumulative signed progress telescopes to the difference of the audit loss at the two
endpoints of the run, so a trajectory that leaves a state and returns to it earns nothing, and one
uniform-deviation event over a class of candidates declared before the panel is drawn bounds the
excess of measured over true progress by a slack of `2Δ` at every horizon. The measured gain less
that slack is a lower bound on improvement.

## Contents

| Path | Content |
| --- | --- |
| `AuditCP/` | The Lean 4 development: libraries `AuditCP` and `AuditCPRL`, the vendored `RLTheory`, the build pins, `verify.sh` and the axiom audit `Check.lean` |
| `experiments/` | Experiment code, the archived records in `results_data/`, `summarize_witnesses.py`, and the figure generators |
| `notebooks/audit_cp_report.ipynb` | A Python reference implementation of the five-number report, checked against the archived sealed-panel record |
| `noumenal.json` | Metadata read by the Noumenal project website |

## The Lean development

`AuditCP/AuditCP/Paper.lean` imports the development chapter by chapter. Chapter 0 declares the
base types. Chapters 1 to 12 (`AuditCP`) build the ledger, the finite-audit slack, sealing as a
property of the interface, the entropy floor and the report; chapter 2½ (`CyberneticCocycle`)
characterizes exact change laws and chapter 9½ (`LawBridge`) relates the two law carriers.
Chapters 13 to 25 (`AuditCPRL`) carry the argument into reinforcement learning on top of
`RLTheory`.

The Lean project contains 67 files, counting the library roots, `Check.lean` and `lakefile.lean`.
`AuditCP` and `AuditCPRL` hold 30 modules with 231 theorems in 6,768 lines; the vendored
`RLTheory` holds 33 files and 10,174 lines.

### Build and audit

Requirements: [`elan`](https://github.com/leanprover/elan), which selects the pinned toolchain
`leanprover/lean4:v4.31.0`, and about 8 GB of disk for the Mathlib build cache. Mathlib is pinned
to commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in `AuditCP/lake-manifest.json`; do not run
`lake update`.

```sh
cd AuditCP
bash verify.sh      # lake exe cache get; lake build; lake env lean Check.lean
```

`lake build` compiles `AuditCP`, `AuditCPRL` and the `RLTheory` modules they import with no errors
and no `sorry`; `lake build RLTheory` compiles the three remaining vendored modules.
`Check.lean` prints the axioms of every declaration the paper cites; each line must read

```
'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and no line may mention `sorryAx`.

### Claim-to-declaration map

Declarations in `AuditCP/AuditCP/` live in the namespace `AuditCP`; declarations in
`AuditCP/AuditCPRL/` live in the namespace `AuditCPRL`.

| Result in the paper | Declarations | File |
| --- | --- | --- |
| Exact change laws are potential differences; clipping breaks cycle neutrality | `isChangeCocycle_iff_exists_potential`, `IsChangeCocycle.closed_path_eq_zero`, `clipped_change_closed_loop_counterexample` | `AuditCP/AuditCP/CyberneticCocycle.lean` |
| Telescoping of cumulative signed progress | `cumCP_telescope`, `cumCP_le_of_lb` | `AuditCP/AuditCP/Telescope.lean` |
| The Goodhart gap is the centered endpoint increment | `cumCP_sub_cumCP_eq_centered_increment`, `cumCP_sub_cumCP_le_of_endpoints`, `abs_cumCP_sub_cumCP_le_of_endpoints` | `AuditCP/AuditCPRL/L0.lean` |
| Finite-audit theorem | `finite_audit_goodhart` | `AuditCP/AuditCP/FiniteAudit.lean` |
| | `finite_audit_goodhart_twoPoint` | `AuditCP/AuditCPRL/L0.lean` |
| | `finite_experts_iid_uniformDev`, `finite_experts_iid_badEvent_le`, `deltaFiniteExperts` | `AuditCP/AuditCP/FiniteExperts.lean` |
| Five-number report: the printed interval | `auditBlind_pairwise_evidenceInterval` | `AuditCP/AuditCP/PaperMetrology.lean` |
| Self-modifying learner | `selfModifying_qlearning_audit_goodhart_bitPriced`, `transcriptEndpoints_bitPriced_goodhart`, `qBall_invariant_of_stepSize_mem_Icc`, `qBall_budget_of_reward_cap`, `selfModifying_qlearning_audit_goodhart`, `selfModifying_qlearning_audit_goodhart_twoPoint`, `selfModifying_stepSize_audit_goodhart_fixedWorld` | `AuditCP/AuditCPRL/SelfModification.lean` |
| Moving targets | `cumCP_sub_cumCP_le_of_endpoints` | `AuditCP/AuditCPRL/L0.lean` |
| | `versioned_product_goodhart`, `versioned_ledger_eq_product_add_bridge`, `versioned_bridge_vanishes_of_constant_version` | `AuditCP/AuditCPRL/VersionedTarget.lean` |
| Shaping with an estimated potential | `approx_shaping_single`, `approx_shaping_pairwise`, `approx_shaping_order_preserved`, `approx_shaping_argmax_preserved`, `approx_shaping_ranking_preserved`, `approx_shaping_slack_tendsto`, `cumCP_shapePot_const_shift`, `shaping_from_panel_trained_potential` | `AuditCP/AuditCPRL/Shaping.lean` |
| Disclosure priced in bits | `reachableEnvelope_card_le_of_disclosureBudget` | `AuditCP/AuditCP/FilteredAudit.lean` |
| | `reachableEnvelope_card_eq_two_pow_bits_mul`, `panelSize_affine_in_disclosureBits`, `sealed_adaptiveEndpoints_goodhart`, `sealed_adaptiveEndpoints_goodhart_iidPanel` | `AuditCP/AuditCPRL/Disclosure.lean` |
| | `policyImprovement_reusedPanel_goodhart`, `policyImprovement_reusedPanel_allHorizons`, `policyImprovement_reusedPanel_bitPriced` | `AuditCP/AuditCPRL/ReusedPanel.lean` |
| What the ledger cannot buy: entropy floor | `cond_entropy_floor_budget_crossEntropy`, `entropy_floor_budget_crossEntropy`, `entropy_floor_budget`, `klDivFinitePMF_nonneg`, `condKLDivFinitePMF_nonneg`, `crossEntropyFinitePMF_eq_entropy_add_kl`, `entropy_le_crossEntropyFinitePMF`, `condEntropy_le_condCrossEntropy` | `AuditCP/AuditCP/EntropyFloor.lean` |
| What the ledger cannot buy: milestones | `demonstrable_milestone_count_le` | `AuditCP/AuditCPRL/Milestone.lean` |
| What the ledger cannot buy: convergent runs | `iteratesOfResidual_ledger_capped_and_exhausted`, `iteratesOfResidual_lifetime_credit` | `AuditCP/AuditCPRL/Convergence.lean` |
| What the ledger cannot buy: intrinsic reward | `intrinsic_return_le_condKL`, `mrp_intrinsic_return_budget`, `mrp_no_unaudited_state` | `AuditCP/AuditCPRL/IntrinsicBudget.lean` |
| Bellman ladder on a sealed panel | `qlearning_ladder_sealedPanel_goodhart`, `populationLoss_update_sq_eq_bellman_sq_add_var` | `AuditCP/AuditCPRL/BellmanLadder.lean` |
| Sealing in the Blackwell order | `auditSealed_iff_factorsThroughPublic`, `learner_blackwellBelow_publicOnly_iff_auditSealed`, `deterministicAuditChannel_sealed_iff` | `AuditCP/AuditCP/FiniteBlackwell.lean` |
| | `auditSealed_iff_no_binary_decision_advantage` | `AuditCP/AuditCP/FiniteBlackwellDecision.lean` |
| | `finiteBrierPosteriorGain_eq_zero_iff_auditSealed` | `AuditCP/AuditCP/FiniteBlackwellBrier.lean` |
| Marginal tests cannot establish concealment | `padTwoStep_marginals_sealed`, `padTwoStep_not_sealed`, `padTwoStep_decodes`, `stateLaw_padChain_eq`, `marginal_tests_cannot_certify_concealment` | `AuditCP/AuditCPRL/Concealment.lean` |
| Coarsening can reverse signed progress | `deterministicGarbling_reverses_signedProgress_pmf` | `AuditCP/AuditCP/LawBridge.lean` |
| | `finiteMRP_occupancy_iff_fullSupport`, `stateAggregation_reverses_occupancy_progress` | `AuditCP/AuditCPRL/Occupancy.lean` |

## The experiments

The substrate is ARC-TGI: 24 learnable grid-transformation families and 8 distractor families
whose outputs are i.i.d. uniform noise, on 30 by 30 grids, with floored cross-entropy loss at
`ε = 0.01` (`R = 4.605`). Every experiment runs 20 seeds, and uncertainties are standard
deviations across seeds (`ddof = 1`).

### Claim-to-data map

Every value below is recomputed from the archived records and compared with the reported value
at the reported precision by

```sh
python3 experiments/summarize_witnesses.py
```

which needs only the Python 3 standard library and exits nonzero if any value fails to reproduce.
The script also checks the further values quoted in the paper's text (standard deviations, the
fitted temperature, the Welch statistic and the effective panel size).

| Experiment | Reported values | Records in `experiments/results_data/` |
| --- | --- | --- |
| Reward-signal ablation | Final active-cell accuracy: audit-CP 0.387 (0.014), prediction error 0.338, random network distillation 0.371, ICM 0.347, uniform 0.376, learnable-only oracle 0.391. Distractor fraction: audit-CP 0.219, prediction error 0.504, random network distillation 0.251, ICM 0.179, uniform 0.250. ICM spends less on distractors than audit-CP in 16 of 20 seeds; audit-CP is more accurate than random network distillation in 17 of 20. | `c1_seed<S>.json` |
| Stream scoring against a sealed audit | Cumulative stream progress 28.96 at `k = 0` and 29.95 at `k = 0.5`; sealed-audit progress 0.741, 0.715 and -0.031 (0.318) at `k = 0`, 0.5 and 1. | `e1_seed<S>.json` |
| Signed against clipped progress | Clipped 1.4175; signed -0.0721, equal to the endpoint change in every seed; gap 1.4896 (0.163), positive in 20 of 20 seeds. | `e3_seed<S>.json` |
| Training on the reusable panel | At 24 families: apparent progress 2.386, true progress -1.497, false-positive excess 3.883 (0.202). At 144 families: excess 3.527. | `e4a_seed<S>.json` |
| Uniform deviation against panel size | Log-log slope -0.526 (0.047) over panel sizes 16, 64 and 256. | `e5_seed<S>.json` |
| Calibration probe | Accuracy change exactly 0 in 20 of 20 seeds. | `e6_seed<S>.json` |
| Holdout attack | Naive release at `Q = 8000`, `n = 200`: gap 3.241 (0.070) against the threshold 1.6396, attacker wins 20 of 20. Fresh subsample 1.368; ladder, rounded and one-shot 0.000. Panel-size sweep at `n` = 50, 200, 800, 3200, 12800: gap 4.181, 3.242, 0.906, 0.226, 0.0564 against thresholds 3.279, 1.640, 0.842, 0.442, 0.231. | `e7_multiseed_summary.json`, `e7cal_seed0.json`, `e7scal_seed0.json` |
| Five-number report of the audit-CP run on the sealed panel | Mean gain 0.7366 (0.0468), slack 0.1549, lower bound on improvement 0.5817, discrimination ratio 4.76. | `c1_panelB_initial_loss.json`, `c1_seed<S>.json` |

The holdout-attack values come from the 20-seed summary written by `e7_multiseed.py`, which stores
the aggregate and not the per-seed results; the per-seed records are archived for seed 0. The
attack is pure NumPy and determined by its seed, and `python3 experiments/e7_multiseed.py 20`
regenerates the summary byte for byte.

### Figures

Both generators need `numpy` and `matplotlib` and write next to the script unless given an output
location.

| Figure | Command |
| --- | --- |
| `fig_e5.pdf` (uniform deviation against panel size) and `fig_c1_policy_bars.pdf` (reward-signal ablation) | `python3 experiments/regen_paper_figs.py [OUTDIR]` |
| `fig_e7.pdf` (holdout attack) | `python3 experiments/replot_e7_multiseed.py [OUT.pdf]` |

`regen_paper_figs.py` also writes `fig_boundary_witnesses.pdf`, which the camera-ready does not
use. The slope in the legend of `fig_e5.pdf` is the least-squares fit through the mean deviation
at each panel size, and its error bars are population standard deviations; the slope reported in
the text is the mean of the per-seed slopes.

### Regenerating the records

The training experiments need `numpy`, `torch`, and the `simon-arc-lab` task generators, which
are not vendored. Clone them at the pinned commit and point the scripts at the checkout:

```sh
git clone https://github.com/neoneye/simon-arc-lab data/arc-tgi
git -C data/arc-tgi checkout d8a2621
export ARC_TGI_ROOT="$PWD/data/arc-tgi"
```

| Script | Role |
| --- | --- |
| `cp_experiments.py` | Experiment drivers: `python3 cp_experiments.py <c1\|e1\|e3\|e4a\|e5\|e6\|e7cal\|e7scal> --scale full --seed S --out FILE` |
| `run_parallel.sh` | Runs (experiment, seed) shards in parallel into `camera_ready_results/json/` and aggregates them with `combine_cp.py` |
| `e7_multiseed.py` | Runs the holdout-attack calibration and panel-size sweep over 20 seeds and writes `results_data/e7_multiseed_summary.json` |
| `c1_panelB_initial_loss.py` | Measures the untrained network on the sealed panel for each seed and writes `results_data/c1_panelB_initial_loss.json`; `--aggregate-only` recomputes the report from the stored levels |
| `cp_models.py`, `verify_cp_models.py` | World models and audit loss, and their unit checks |
| `arc_tgi_source.py`, `arc_tgi_manifest.json` | The ARC-TGI task source and its family manifest |

The training runs are not bitwise reproducible across hardware; the archived records are the
outputs of the runs the paper reports.

## RLTheory

The reinforcement-learning chapters build on `rl-theory-in-lean` by Shangtong Zhang
(<https://github.com/ShangtongZhang/rl-theory-in-lean>, MIT license, reproduced in
`AuditCP/RLTheory-LICENSE`). The copy in `AuditCP/RLTheory/` is vendored from upstream commit
`fa1c276240ff4502d2d06a3b95591ca5991c3fe4` (2026-02-05, Lean v4.28.0-rc1). It has the same 33
Lean files as that commit; 14 are byte-identical to it and 19 are modified here, and the copy
builds against Lean v4.31.0 and the Mathlib commit pinned above. Please cite the library as
upstream requests:

> Shangtong Zhang. Towards Formalizing Reinforcement Learning Theory: A Robbins-Siegmund Approach.
> Reinforcement Learning Journal, 2026. arXiv:2511.03618.

## License

The Lean development in `AuditCP/` is released under the Apache License 2.0 (`AuditCP/LICENSE`),
except the vendored `RLTheory`, which remains under its MIT license.

## Citation

```bibtex
@misc{mittal2026signed,
  title         = {Signed Compression Progress on a Sealed Audit is Goodhart-Resistant},
  author        = {Ayush Mittal and Dhruv Gupta},
  year          = {2026},
  eprint        = {2606.11417},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LG}
}
```

Sources for the results the development inherits are listed in
[`AuditCP/CITATIONS.md`](AuditCP/CITATIONS.md).
