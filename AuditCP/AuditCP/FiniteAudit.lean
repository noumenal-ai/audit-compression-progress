import AuditCP.Telescope

/-!
# Chapter 3 — the slack

The load-bearing theorem, and the only place the two hypotheses of the thesis meet.  It is stated
entirely at B2, B3 and B4: a measured potential, a population potential, a trajectory and an
envelope.  No probability appears; the probability is Chapter 4's job.

Its depth is not the endpoint algebra but the quantifier order.  The envelope `F` is declared
before the horizon and before the audit outcome, so a single uniform-deviation event controls every
horizon at once with **no union bound over `T`** — the telescoped ledger reads only `g 0` and
`g T`, both in `F` by `Admissible`.  Uniformity over `F` is what makes the radius horizon-free;
telescoping is what makes the constant `2` rather than `T + 1`.  The two are independent
ingredients and only their conjunction gives the statement its strength.
-/

namespace AuditCP

/-- Under `UniformDev F Ehat E Δ` and `Admissible g F`, empirical cumulative compression progress
is bounded by true cumulative progress plus `2Δ` at every horizon `T`:
`cumCP Ehat g T ≤ cumCP E g T + 2Δ`. -/
theorem finite_audit_goodhart {ι : Type*} {F : AuditEnvelope ι} {Ehat E : AuditPotential ι} {Δ : ℝ}
    (hUD : UniformDev F Ehat E Δ) {g : AuditTrajectory ι} (hg : Admissible g F) (T : ℕ) :
    cumCP Ehat g T ≤ cumCP E g T + 2 * Δ := by
  rw [cumCP_telescope Ehat g T, cumCP_telescope E g T]
  have h0 := abs_le.1 (hUD (g 0) (hg 0))
  have hT := abs_le.1 (hUD (g T) (hg T))
  linarith [h0.1, h0.2, hT.1, hT.2]

end AuditCP
