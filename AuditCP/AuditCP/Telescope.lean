import AuditCP.Basic

/-!
# Chapter 2 — the ledger is exact

Two identities, both stated at B2 `AuditPotential` and B3 `AuditTrajectory` and nothing else.
Their exactness is what the rest of the thesis spends: because `cumCP` is a difference of a
potential and not a rectified sum, a closed path nets exactly zero at every horizon and for every
potential, so no cycle pumps the ledger, and the audited quantity reads exactly two stages however
long the trajectory is.

This is a telescoping identity, the kernel that gives `cumCP` its meaning (Mathlib anchor:
`Finset.sum_range_sub'`).
-/

namespace AuditCP

/-- Cumulative signed compression progress telescopes: `cumCP E g T = E (g 0) - E (g T)`. -/
theorem cumCP_telescope {ι : Type*} (E : AuditPotential ι) (g : AuditTrajectory ι) (T : ℕ) :
    cumCP E g T = E (g 0) - E (g T) := by
  induction T with
  | zero => simp [cumCP]
  | succ n ih =>
      simp only [cumCP, Finset.sum_range_succ] at ih ⊢
      rw [ih]; ring

/-- If `Emin ≤ E (g T)`, then `cumCP E g T ≤ E (g 0) - Emin`. -/
theorem cumCP_le_of_lb {ι : Type*} (E : AuditPotential ι) (g : AuditTrajectory ι) (T : ℕ)
    {Emin : ℝ} (hlb : Emin ≤ E (g T)) : cumCP E g T ≤ E (g 0) - Emin := by
  rw [cumCP_telescope]; linarith

end AuditCP
