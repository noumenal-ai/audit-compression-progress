import AuditCPRL.ReachableEnvelope
import AuditCP.PaperMetrology

/-!
# Target 12 — what sealing buys, and what disclosure costs

An adaptive run under a disclosure interface reports a ledger read at two stages.  This module
settles which of its two ends is priced in the disclosure budget.

## Sealing is load-bearing at exactly one slot

`AuditCP.kernel_endpointPair_goodhart` takes an argument
`endpoints : Ωtrain → Candidate × Candidate`: a declared endpoint pair that is a function of the
**training coordinate alone**.  An audit-dependent interface cannot produce one — the realized
endpoints then move with the audit draw — and that, not the size of any class, is what
`AuditCP.AuditSealedUntil` supplies.  Under sealing the realized pair at stages `0` and `T` equals
the training-indexed declared pair for *every* audit draw, so the slot is filled and the adaptive
trajectory inherits the two-endpoint guarantee at whatever resolution the audit achieves.

Delete sealing and the endpoint pair is a function of `(t, a)`; the declarable class is the union
over the audit fiber, and under a `bits`-bit budget that union is the reachable envelope, of size
up to `2 ^ bits * M`.  The panel then pays for it: at a fixed two-endpoint resolution `ε`, panel
size is **affine in the disclosed bits**, with slope `2 L² log 2 / ε²`, and that ceiling is
attained.

## The `bits = T * b` rider stands

Nothing below overrides it: a loop leaking `b` bits per round has `bits = T * b`, the affine law
gives a panel linear in `T`, and the resolution returns to `√T`.  Sealing is what removes `T` from
the radius; a per-round leak puts it back.

## Named here, deliberately not used below

* `AuditCP.boolAuditDisclosure_is_auditDependent` — the closure's concrete witness that an
  audit-dependent interface fails the `endpoints` slot at stage `0` and is not sealed.  It is the
  reason the sealing hypothesis is not decoration; it is a witness, not a lemma this module needs.
* `AuditCP.reachableEnvelope_card_le`, `AuditCP.HasDisclosureBudget` and
  `AuditCP.reachableEnvelope_card_le_of_disclosureBudget` — the *inequality* form of the envelope
  ceiling, and the predicate it is stated under.  `reachableEnvelope_card_eq_two_pow_bits_mul` below
  is the equality that meets that ceiling, and it needs strictly more than the budget (a full
  alphabet, and disjoint fibers of common size), which is why it takes an equality hypothesis rather
  than that predicate and does not go through that theorem.
* `AuditCP.auditSealed_iff_factorsThroughPublic` — sealing of a *channel*, on the `PMF` carrier.
  `AuditCP.AuditSealedUntil` is sealing of a *filtration*, on the `Measure` carrier; the closure
  contains no declaration bridging them, and this module does not add one.

-/

namespace AuditCPRL

open AuditCP MeasureTheory ProbabilityTheory

/-- If `D` is audit-sealed through `T`, then the endpoint pair
`(D.candidateProcess policy 0 (t, a), D.candidateProcess policy T (t, a))` does not depend on the
audit coordinate `a`. -/
theorem sealed_endpointFiber_subsingleton
    {Ωtrain Ωaudit Transcript Candidate : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [MeasurableSpace Transcript]
    (D : FilteredDisclosure (Ωtrain × Ωaudit) Transcript)
    (policy : Transcript → AuditTrajectory Candidate) {T : ℕ}
    (hsealed : AuditSealedUntil D T) (t : Ωtrain) (a₁ a₂ : Ωaudit) :
    (D.candidateProcess policy 0 (t, a₁), D.candidateProcess policy T (t, a₁))
      = (D.candidateProcess policy 0 (t, a₂), D.candidateProcess policy T (t, a₂)) :=
  Prod.ext
    (D.candidateProcess_eq_of_auditSealedUntil policy hsealed (Nat.zero_le T) t a₁ a₂)
    (D.candidateProcess_eq_of_auditSealedUntil policy hsealed le_rfl t a₁ a₂)

/-- If `D` is audit-sealed through `T`, `F t` is the declared endpoint pair
`{D.candidateProcess policy 0 (t, a₀), D.candidateProcess policy T (t, a₀)}` at a reference audit
outcome `a₀`, the uniform-deviation failure event on `F` is measurable, and its kernel fiber has
probability at most `δ` for `μtrain`-almost every training state, then measured cumulative
compression progress along the realized disclosed process exceeds population progress by more
than `2Δ` with probability at most `δ` under `μtrain.compProd κ`. -/
theorem sealed_adaptiveEndpoints_goodhart
    {Ωtrain Ωaudit Transcript Candidate : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [MeasurableSpace Transcript]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (D : FilteredDisclosure (Ωtrain × Ωaudit) Transcript)
    (policy : Transcript → AuditTrajectory Candidate) {T : ℕ}
    (hsealed : AuditSealedUntil D T) (a₀ : Ωaudit)
    (F : Ωtrain → AuditEnvelope Candidate)
    (Ehat : Ωtrain → Ωaudit → AuditPotential Candidate) (E : Ωtrain → AuditPotential Candidate)
    (Δ : ℝ) (δ : ENNReal)
    (hF : ∀ t, F t =
      {D.candidateProcess policy 0 (t, a₀), D.candidateProcess policy T (t, a₀)})
    (hBad : MeasurableSet
      {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain, κ t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ) :
    (μtrain.compProd κ)
        {p : Ωtrain × Ωaudit |
          cumCP (Ehat p.1 p.2) (fun m => D.candidateProcess policy m p) T >
            cumCP (E p.1) (fun m => D.candidateProcess policy m p) T + 2 * Δ} ≤ δ := by
  have hendpoints : ∀ t : Ωtrain,
      (D.candidateProcess policy 0 (t, a₀), D.candidateProcess policy T (t, a₀)).1 ∈ F t ∧
        (D.candidateProcess policy 0 (t, a₀), D.candidateProcess policy T (t, a₀)).2 ∈ F t := by
    intro t
    rw [hF t]
    exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ rfl⟩
  have key := kernel_endpointPair_goodhart μtrain κ F
    (fun t => (D.candidateProcess policy 0 (t, a₀), D.candidateProcess policy T (t, a₀)))
    Ehat E Δ δ hendpoints hBad hfiber
  refine le_trans (measure_mono ?_) key
  rintro ⟨t, a⟩ hp
  simp only [Set.mem_setOf_eq, cumCP_telescope] at hp ⊢
  rwa [D.candidateProcess_eq_of_auditSealedUntil policy hsealed (Nat.zero_le T) t a a₀,
    D.candidateProcess_eq_of_auditSealedUntil policy hsealed (le_refl T) t a a₀] at hp

/-- If `D` is audit-sealed through `T`, `F t` is the declared endpoint pair at reference audit
outcome `a₀`, the uniform-deviation failure event on `F` is measurable, and `loss` is measurable
and a.e. valued in `[a, b]`, then on an i.i.d. panel of size `n`, measured cumulative compression
progress along the realized disclosed process exceeds population progress by more than
`2 · deltaFiniteExperts 2 n (b - a) dfail` with probability at most `ENNReal.ofReal dfail`. -/
theorem sealed_adaptiveEndpoints_goodhart_iidPanel
    {Ωtrain Transcript Candidate Z : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Z] [MeasurableSpace Transcript]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : AuditSampleLaw Z) [IsProbabilityMeasure Q] (n : ℕ) (hn : 0 < n)
    {a b : ℝ} (hab : a < b) {dfail : ℝ} (hd0 : 0 < dfail) (hd1 : dfail ≤ 1)
    (loss : Candidate → Z → ℝ) (hloss : ∀ θ, Measurable (loss θ))
    (hbdd : ∀ θ, ∀ᵐ z ∂Q, loss θ z ∈ Set.Icc a b)
    (D : FilteredDisclosure (Ωtrain × (Fin n → Z)) Transcript)
    (policy : Transcript → AuditTrajectory Candidate) {T : ℕ}
    (hsealed : AuditSealedUntil D T) (a₀ : Fin n → Z)
    (F : Ωtrain → AuditEnvelope Candidate)
    (hF : ∀ t, F t =
      {D.candidateProcess policy 0 (t, a₀), D.candidateProcess policy T (t, a₀)})
    (hBad : MeasurableSet
      {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (F p.1)
        (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ)
        (deltaFiniteExperts 2 n (b - a) dfail)}) :
    (μtrain.compProd (Kernel.const _ (Measure.pi (fun _ : Fin n => Q))))
        {p : Ωtrain × (Fin n → Z) |
          cumCP (fun θ => empiricalLoss loss θ p.2)
              (fun m => D.candidateProcess policy m p) T >
            cumCP (fun θ => populationLoss Q loss θ)
              (fun m => D.candidateProcess policy m p) T
              + 2 * deltaFiniteExperts 2 n (b - a) dfail}
      ≤ ENNReal.ofReal dfail := by
  refine sealed_adaptiveEndpoints_goodhart μtrain _ D policy hsealed a₀ F
    (fun _ panel θ => empiricalLoss loss θ panel) (fun _ θ => populationLoss Q loss θ)
    (deltaFiniteExperts 2 n (b - a) dfail) (ENNReal.ofReal dfail) hF hBad ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Kernel.const_apply, hF t]
  exact twoPoint_badEvent_le Q n hn hab hd0 hd1 loss _ _ (hloss _) (hloss _) (hbdd _) (hbdd _)

/-- If the transcript alphabet is full (`Fintype.card Transcript = 2^bits`), every transcript
enables exactly `M` candidates, and the per-transcript candidate sets are pairwise disjoint, then
`(reachableEnvelope choices).card = 2^bits * M`. -/
theorem reachableEnvelope_card_eq_two_pow_bits_mul
    {Transcript Candidate : Type*} [Fintype Transcript]
    (choices : Transcript → Finset Candidate) (bits M : ℕ)
    (hfull : Fintype.card Transcript = 2 ^ bits)
    (hcard : ∀ τ, (choices τ).card = M)
    (hdisj : ((Finset.univ : Finset Transcript) : Set Transcript).PairwiseDisjoint choices) :
    (reachableEnvelope choices).card = 2 ^ bits * M := by
  classical
  rw [reachableEnvelope, Finset.card_biUnion hdisj,
    Finset.sum_const_nat (fun τ _ => hcard τ), Finset.card_univ, hfull]

/-- Given `0 < M` and `0 < δ`,
`panelSizeForResolution (2^bits * M) L δ ε = (2L² log 2 / ε²) · bits + 2L² log(2M/δ) / ε²`. -/
theorem panelSize_affine_in_disclosureBits (bits M : ℕ) (L δ ε : ℝ)
    (hM : 0 < M) (hδ : 0 < δ) :
    panelSizeForResolution (2 ^ bits * M) L δ ε
      = (2 * L ^ 2 * Real.log 2 / ε ^ 2) * (bits : ℝ)
        + 2 * L ^ 2 * Real.log (2 * (M : ℝ) / δ) / ε ^ 2 := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  unfold panelSizeForResolution
  rw [show (2 : ℝ) * ((2 ^ bits * M : ℕ) : ℝ) / δ
        = (2 : ℝ) ^ bits * (2 * (M : ℝ) / δ) by push_cast; ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

end AuditCPRL
