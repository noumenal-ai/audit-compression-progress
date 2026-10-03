# AuditCP: the Lean 4 development

Lean 4 development for **"Signed Compression Progress on a Sealed Audit is Goodhart-Resistant"**
([arXiv:2606.11417](https://arxiv.org/abs/2606.11417)). The map from each result in the paper to
its declarations is in the top-level [`README.md`](../README.md).

## Build and audit

```sh
bash verify.sh      # = lake exe cache get; lake build; lake env lean Check.lean
```

- Toolchain: `leanprover/lean4:v4.31.0`, selected by `lean-toolchain` through
  [`elan`](https://github.com/leanprover/elan).
- Mathlib: commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, with its dependencies pinned in
  `lake-manifest.json`. Do not run `lake update`.
- Disk: about 8 GB for the Mathlib build cache that `lake exe cache get` downloads.

`lake build` compiles the libraries `AuditCP` and `AuditCPRL` and the `RLTheory` modules they
import with no errors and no `sorry`; `lake build RLTheory` compiles the three remaining vendored
modules. `Check.lean` prints the axioms of every declaration the paper cites, grouped by chapter;
each must depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

| Path | Content |
| --- | --- |
| `AuditCP.lean` | Library root; imports `AuditCP/Paper.lean` |
| `AuditCP/Paper.lean` | The chapters in order, with a table of what each adds |
| `AuditCP/*.lean` | Chapters 0 to 12, with the half chapters `CyberneticCocycle` (2½) and `LawBridge` (9½) |
| `AuditCP/Vendored/FinitePMF.lean` | Finite-PMF, KL and cross-entropy layer, copied with attribution from the author's earlier Lean development |
| `AuditCPRL.lean`, `AuditCPRL/*.lean` | Chapters 13 to 25: the reinforcement-learning results, built on `RLTheory` |
| `RLTheory.lean`, `RLTheory/` | Vendored `rl-theory-in-lean` (Shangtong Zhang, MIT; see `RLTheory-LICENSE`) |
| `Check.lean` | Axiom audit |
| `verify.sh` | Build and audit in one command |
| `lakefile.lean`, `lean-toolchain`, `lake-manifest.json` | Build configuration and pins |
| `CITATIONS.md`, `CITATIONS.bib` | Sources for the citation keys used in docstrings |
| `BREAKS.md` | Notes on two design choices in the type structure |
| `LICENSE` | Apache License 2.0 |

`RLTheory/` is vendored from upstream commit `fa1c276240ff4502d2d06a3b95591ca5991c3fe4` of
<https://github.com/ShangtongZhang/rl-theory-in-lean> (2026-02-05, Lean v4.28.0-rc1): the same 33
Lean files, 14 byte-identical to that commit and 19 modified here.
