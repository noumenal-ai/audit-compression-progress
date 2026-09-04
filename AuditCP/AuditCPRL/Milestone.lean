import AuditCP.PaperMetrology

/-!
# Target 11 — how many audit-demonstrable improvements a run can contain

A run reports a *measured* gain at each of `k` declared checkpoints.  If every reported gain clears
the audit's own slack by a fixed margin `ρ`, then `k` is bounded, and the bound is a ratio of a
world quantity to an audit quantity:

    k * ρ  ≤  klDivFinitePMF Q (P (g 0))

the world's initial divergence from its own law to the model, over the margin.  No horizon appears,
no path appears, and no property of the trajectory between checkpoints appears.

## Why the checkpoints need only be pairwise admissible

The per-step move is `AuditCP.finite_audit_goodhart` applied to
`AuditCP.endpointPairPath (g (s j), g (s (j+1)))` at horizon `1`, read through
`AuditCP.cumCP_endpointPairPath` at both potentials.  `AuditCP.Admissible` is therefore discharged
at two indices per step, so the trajectory may leave the declared envelope between checkpoints; only
the checkpoints themselves must lie in it.

## `Δ` is carried abstractly, and that is the point

The numerator lives on the vendored `AuditCP.FinitePMF` carrier; the only route that would fill the
denominator with a panel-size-indexed radius, `AuditCP.finite_experts_iid_uniformDev`, lives on
`MeasureTheory.Measure.pi`.  `AuditCP.Base` names bridging those carriers an *open obligation*, not
a completed derivation.  So the closed form

    k ≤ klDivFinitePMF Q (P (g 0)) * √(2n) / (2 L √(log (2N/δ)))

is a **reading blocked on that bridge**, and no theorem below states it.  `AuditCP.deltaFiniteExperts`
enters only through `milestone_count_implicit_bound`, where it is an *instantiation of `ρ`* supplied
by the caller and never derived here.

**Open obligation, not used below:** `AuditCP.finite_experts_iid_uniformDev`.  It is named here as
the missing link and occurs in no statement or proof in this module.

## What the implicit bound is, and what it is not

Instantiating `ρ = 2 * AuditCP.deltaFiniteExperts N n L δ` and using `k + 1 ≤ N` gives a necessary
condition in `k` alone.  It is **not** a fixed point and the count does not close on itself: the
step is monotonicity of the radius in the candidate bound, which derives a *weaker* inequality from
a stronger one.  What it buys is that the admissible `k` are a downward-closed set
(`milestone_count_lhs_monotone`), so "the maximal admissible `k`" is a well-posed threshold; the
growth of that threshold as `√n` up to a `√log` factor is arithmetic on
`AuditCP.deltaFiniteExperts` and is not claimed as a theorem here.

`k + 1 ≤ N` is discharged rather than carried: distinct checkpoints in a finite index type give
`k + 1 ≤ Fintype.card ι` (`checkpoint_index_card_le`), and `Fintype.card ι` is exactly the `N` that
`AuditCP.finite_experts_iid_uniformDev` declares.  The alternative — taking `N := k + 1`, i.e.
declaring the realized checkpoints as the audited class — is the declarability obstruction that
`AuditCPRL/ReachableEnvelope.lean` already names: the checkpoints are chosen inside the sample-path
binder, and an auditor who fixes a class before drawing a panel cannot use them.

## Reading

The audit is free in time and paid in reports.
-/

namespace AuditCPRL

open AuditCP

/-- If `UniformDev F Ehat (fun θ => crossEntropyFinitePMF Q (P θ)) Δ` holds, `s 0 = 0`, every
checkpoint `g (s j)` for `j ≤ k` lies in `F`, and each step reports a drop of at least `2Δ + ρ` in
`Ehat`, then `(k : ℝ) * ρ ≤ klDivFinitePMF Q (P (g 0))`. -/
theorem demonstrable_milestone_count_le
    {ι H : Type*} [Fintype H]
    (Q : FinitePMF H) (P : ι → FinitePMF H) [∀ θ, HasPositivePrior (P θ)]
    {F : AuditEnvelope ι} {Ehat : AuditPotential ι} {Δ ρ : ℝ}
    (hUD : UniformDev F Ehat (fun θ => crossEntropyFinitePMF Q (P θ)) Δ)
    (g : AuditTrajectory ι) (s : ℕ → ℕ) (k : ℕ) (hs0 : s 0 = 0)
    (hmem : ∀ j ≤ k, g (s j) ∈ F)
    (hdem : ∀ j < k, 2 * Δ + ρ ≤ Ehat (g (s j)) - Ehat (g (s (j + 1)))) :
    (k : ℝ) * ρ ≤ klDivFinitePMF Q (P (g 0)) := by
  classical
  set E : AuditPotential ι := fun θ => crossEntropyFinitePMF Q (P θ) with hE
  have hstep : ∀ j ∈ Finset.range k, ρ ≤ E (g (s j)) - E (g (s (j + 1))) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    have hadm : Admissible (endpointPairPath (g (s j), g (s (j + 1)))) F := by
      intro t
      cases t with
      | zero => exact hmem j hjk.le
      | succ _ => exact hmem (j + 1) hjk
    have hgh := finite_audit_goodhart hUD hadm 1
    rw [cumCP_endpointPairPath, cumCP_endpointPairPath] at hgh
    simp only at hgh
    linarith [hdem j hjk]
  calc (k : ℝ) * ρ
      = ∑ _j ∈ Finset.range k, ρ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range k, (E (g (s j)) - E (g (s (j + 1)))) := Finset.sum_le_sum hstep
    _ = E (g (s 0)) - E (g (s k)) := Finset.sum_range_sub' (fun j => E (g (s j))) k
    _ ≤ crossEntropyFinitePMF Q (P (g 0)) - entropyFinitePMF Q := by
        rw [hs0]
        have := entropy_le_crossEntropyFinitePMF Q (P (g (s k)))
        simp only [hE]
        linarith
    _ = klDivFinitePMF Q (P (g 0)) := by
        rw [crossEntropyFinitePMF_eq_entropy_add_kl Q (P (g 0))]; ring

/-- If the checkpoints `g (s 0), …, g (s k)` are pairwise distinct, then
`k + 1 ≤ Fintype.card ι`. -/
theorem checkpoint_index_card_le {ι : Type*} [Fintype ι]
    (g : AuditTrajectory ι) (s : ℕ → ℕ) (k : ℕ)
    (hinj : Function.Injective fun j : Fin (k + 1) => g (s j)) :
    k + 1 ≤ Fintype.card ι := by
  simpa using Fintype.card_le_of_injective _ hinj

/-- If `k + 1 ≤ N`, `0 < n`, `0 ≤ L`, `0 < δ`, `ρ = 2 · deltaFiniteExperts N n L δ`, and
`(k : ℝ) * ρ ≤ B`, then `(k : ℝ) * (2 · deltaFiniteExperts (k + 1) n L δ) ≤ B`. -/
theorem milestone_count_implicit_bound
    {B ρ : ℝ} (N n k : ℕ) (L δ : ℝ)
    (hkN : k + 1 ≤ N) (hn : 0 < n) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hρ : ρ = 2 * deltaFiniteExperts N n L δ)
    (hcount : (k : ℝ) * ρ ≤ B) :
    (k : ℝ) * (2 * deltaFiniteExperts (k + 1) n L δ) ≤ B := by
  have hmono : deltaFiniteExperts (k + 1) n L δ ≤ deltaFiniteExperts N n L δ :=
    deltaFiniteExperts_mono_candidateBound (Nat.succ_pos k) hkN hn hL hδ
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc (k : ℝ) * (2 * deltaFiniteExperts (k + 1) n L δ)
      ≤ (k : ℝ) * (2 * deltaFiniteExperts N n L δ) :=
        mul_le_mul_of_nonneg_left (by linarith) hk
    _ = (k : ℝ) * ρ := by rw [hρ]
    _ ≤ B := hcount

/-- Given `0 < n`, `0 ≤ L`, `0 < δ`, the map `k ↦ (k : ℝ) * (2 · deltaFiniteExperts (k + 1) n L δ)`
is monotone. -/
theorem milestone_count_lhs_monotone (n : ℕ) (L δ : ℝ)
    (hn : 0 < n) (hL : 0 ≤ L) (hδ : 0 < δ) :
    Monotone fun k : ℕ => (k : ℝ) * (2 * deltaFiniteExperts (k + 1) n L δ) := by
  intro k₁ k₂ h
  have hd : deltaFiniteExperts (k₁ + 1) n L δ ≤ deltaFiniteExperts (k₂ + 1) n L δ :=
    deltaFiniteExperts_mono_candidateBound (Nat.succ_pos k₁) (Nat.succ_le_succ h) hn hL hδ
  have hd0 : (0 : ℝ) ≤ deltaFiniteExperts (k₁ + 1) n L δ := by
    unfold deltaFiniteExperts
    exact mul_nonneg hL (Real.sqrt_nonneg _)
  have hk : (k₁ : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast h
  exact mul_le_mul hk (by linarith) (by linarith) (Nat.cast_nonneg k₂)

end AuditCPRL
