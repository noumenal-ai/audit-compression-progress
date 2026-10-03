# Experiments

This directory holds the ARC-TGI experiments of the paper, the archived records they produced,
and the scripts that recompute the reported numbers and redraw the figures. The map from each
reported number to its records is in the top-level [`README.md`](../README.md).

## Recompute the reported numbers

```sh
python3 summarize_witnesses.py
```

The script reads `results_data/`, prints every reported quantity as a mean with its standard
deviation across seeds (`ddof = 1`), compares it with the reported value at the reported
precision, and exits nonzero on any mismatch. It needs only the Python 3 standard library.

## Archived records (`results_data/`)

| Files | Experiment |
| --- | --- |
| `c1_seed<S>.json` | Reward-signal ablation under a fixed scheduler, seven reward signals |
| `e1_seed<S>.json` | Stream scoring on the family just trained against a sealed audit, at stream bias `k` in {0, 0.5, 1} |
| `e3_seed<S>.json` | Signed against clipped progress on a relearning cycle |
| `e4a_seed<S>.json` | Training directly on the reusable panel, at 24 and 144 families |
| `e5_seed<S>.json` | Uniform deviation of a finite family of frozen predictors at panel sizes 16, 64 and 256 |
| `e6_seed<S>.json` | Temperature calibration of a trained predictor |
| `e7_multiseed_summary.json` | Holdout attack over 20 seeds: calibration at `Q = 8000`, `n = 200`, the release mechanisms, and the panel-size sweep |
| `e7cal_seed0.json`, `e7scal_seed0.json` | The seed-0 calibration and sweep records; the summary's seed-0 entry equals them |
| `e7_regenerated/` | Seeds 1 to 19 of the calibration and sweep, regenerated from this code; with seed 0 they reproduce every value of the summary (see its README) |
| `c1_panelB_initial_loss.json` | Initial and terminal levels of the audit-CP run on the sealed panel, per seed, with the effective panel size and the five-number report |

Seeds `S` run from 0 to 19. Each per-seed file holds the driver's result under a top-level key
named after the experiment.

## Scripts

| Script | Role |
| --- | --- |
| `cp_experiments.py` | Experiment drivers, one per record type |
| `cp_models.py` | World models, curiosity baselines and the floored cross-entropy audit loss |
| `verify_cp_models.py` | Unit checks for `cp_models.py` |
| `arc_tgi_source.py`, `arc_tgi_manifest.json` | ARC-TGI task source and family manifest |
| `run_parallel.sh`, `combine_cp.py` | Parallel (experiment, seed) runner and its aggregator |
| `e7_multiseed.py` | 20-seed holdout attack; writes `results_data/e7_multiseed_summary.json` |
| `c1_panelB_initial_loss.py` | Sealed-panel initial levels and the five-number report |
| `summarize_witnesses.py` | Recomputes and checks every reported number |
| `regen_paper_figs.py` | Draws `fig_e5.pdf` and `fig_c1_policy_bars.pdf` (and `fig_boundary_witnesses.pdf`) |
| `replot_e7_multiseed.py` | Draws `fig_e7.pdf` from the holdout-attack summary |

The training drivers need `numpy`, `torch` and the `simon-arc-lab` generators at commit `d8a2621`
(set `ARC_TGI_ROOT`; see the top-level README). The figure scripts need `numpy` and `matplotlib`.
