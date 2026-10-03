import Lake
open Lake DSL

/-
Audit compression progress: the machine-checked thesis.

The `AuditCP` library is the paper's argument in order, from a seven-type base through
the sealed-audit interface results to the reported instrument. `AuditCPRL` carries that
argument into reinforcement learning.

Dependencies. Mathlib is pinned to an exact commit. `RLTheory` is Shangtong Zhang's
`rl-theory-in-lean` (MIT; see RLTheory-LICENSE and the README), vendored from upstream commit
fa1c276240ff4502d2d06a3b95591ca5991c3fe4 (2026-02-05, Lean v4.28.0-rc1). The vendored copy has
the same 33 Lean files as that commit; 14 are byte-identical to it and 19 are modified here. The
copy builds against the Lean v4.31.0 toolchain and the Mathlib commit pinned below.

The finite-PMF and cross-entropy layer in AuditCP/Vendored/FinitePMF.lean is copied and
cited from the author's prior Lean development rather than required.
-/

package «AuditCP» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"

lean_lib «RLTheory» where
  roots := #[`RLTheory]
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «AuditCP» where
  roots := #[`AuditCP]

@[default_target]
lean_lib «AuditCPRL» where
  roots := #[`AuditCPRL]
