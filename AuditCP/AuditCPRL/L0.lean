import AuditCP.FiniteAudit

/-!
# L0 — the centered-empirical-process identity, and the two bounds every crossover uses

`AuditCP.finite_audit_goodhart` proves an inequality by `linarith` over two telescopes.  The
identity that `linarith` step consumes is never stated in the corpus.  It is stated here, once,
as `cumCP_sub_cumCP_eq_centered_increment`:

    cumCP Ê g T − cumCP E g T  =  (Ê − E)(g 0) − (Ê − E)(g T)

Exact: no event, no `δ`, no `N`, no probability, no hypothesis on `Ê`, `E`, `g`, `T` or `ι`.
The Goodhart gap is not bounded by a slack; it **is** the increment of the centered process
`X := Ê − E` between the two evaluated endpoints.

Everything downstream in this library is L0 followed by a bound on that increment.  Two bound
shapes occur, and both are proved here so no later file re-derives them:

* `cumCP_sub_cumCP_le_of_endpoints` — a one-sided `2Δ` from a symmetric endpoint bound.  This is
  `AuditCP.finite_audit_goodhart` with `Admissible` deleted: the corpus theorem needs `g t ∈ F`
  for every `t`, its proof uses `t = 0` and `t = T` only.
* `abs_cumCP_sub_cumCP_le_of_endpoints` — a two-sided bound with **independent** radii at the two
  endpoints.  `finite_audit_goodhart` is symmetric in the endpoints and cannot state this; it is
  what the discounted shaping crossover (`AuditCPRL.Shaping`) needs, because there the terminal
  endpoint carries a `γ ^ T` factor the start endpoint does not.

-/

namespace AuditCPRL

open AuditCP

/-- `cumCP Ehat g T - cumCP E g T = (Ehat (g 0) - E (g 0)) - (Ehat (g T) - E (g T))`. -/
theorem cumCP_sub_cumCP_eq_centered_increment {ι : Type*} (Ehat E : ι → ℝ) (g : ℕ → ι) (T : ℕ) :
    cumCP Ehat g T - cumCP E g T
      = (Ehat (g 0) - E (g 0)) - (Ehat (g T) - E (g T)) := by
  rw [cumCP_telescope Ehat g T, cumCP_telescope E g T]; ring

/-- If `|Ehat (g 0) - E (g 0)| ≤ Δ` and `|Ehat (g T) - E (g T)| ≤ Δ`, then
`cumCP Ehat g T ≤ cumCP E g T + 2Δ`. -/
theorem cumCP_sub_cumCP_le_of_endpoints {ι : Type*} {Ehat E : ι → ℝ} {g : ℕ → ι} {T : ℕ} {Δ : ℝ}
    (h0 : |Ehat (g 0) - E (g 0)| ≤ Δ) (hT : |Ehat (g T) - E (g T)| ≤ Δ) :
    cumCP Ehat g T ≤ cumCP E g T + 2 * Δ := by
  have hL0 := cumCP_sub_cumCP_eq_centered_increment Ehat E g T
  have a0 := abs_le.1 h0
  have aT := abs_le.1 hT
  linarith [a0.1, a0.2, aT.1, aT.2]

/-- If `|Ehat (g 0) - E (g 0)| ≤ c` and `|Ehat (g T) - E (g T)| ≤ d`, then
`|cumCP Ehat g T - cumCP E g T| ≤ c + d`. -/
theorem abs_cumCP_sub_cumCP_le_of_endpoints {ι : Type*} {Ehat E : ι → ℝ} {g : ℕ → ι} {T : ℕ}
    {c d : ℝ} (h0 : |Ehat (g 0) - E (g 0)| ≤ c) (hT : |Ehat (g T) - E (g T)| ≤ d) :
    |cumCP Ehat g T - cumCP E g T| ≤ c + d := by
  rw [cumCP_sub_cumCP_eq_centered_increment]
  exact (abs_sub _ _).trans (add_le_add h0 hT)

/-- If `UniformDev F Ehat E Δ` and the two endpoints `g 0, g T ∈ F`, then
`cumCP Ehat g T ≤ cumCP E g T + 2Δ`. -/
theorem finite_audit_goodhart_twoPoint {ι : Type*} {F : Set ι} {Ehat E : ι → ℝ} {Δ : ℝ}
    (hUD : UniformDev F Ehat E Δ) {g : ℕ → ι} {T : ℕ} (h0 : g 0 ∈ F) (hT : g T ∈ F) :
    cumCP Ehat g T ≤ cumCP E g T + 2 * Δ :=
  cumCP_sub_cumCP_le_of_endpoints (hUD (g 0) h0) (hUD (g T) hT)

end AuditCPRL
