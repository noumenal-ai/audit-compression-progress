import AuditCP.StructuralAudit
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Chapter 6 — the audit law may depend on the world

Chapter 5's product B7 law is replaced by a probability kernel from training/world state to the
audit outcome: Mathlib's `ProbabilityTheory.Kernel` is B7 made into a measurable family, and the
joint law is the composition-product `Measure.compProd`.  The final theorem removes even the kernel
as a hypothesis, using Mathlib's standard-Borel regular conditional distribution to cover an
arbitrary joint probability law.

Nothing in the ledger changes.  `F`, `g`, `Ehat` and `E` are still B4, B3 and B2, and the endpoint
inequality that gets integrated is still `finite_audit_goodhart`.  What changes is only which B7
law the failure event is measured under — which is why arbitrary statistical dependence between
world and audit costs nothing, while a *positional* change (letting `F` read the audit coordinate)
would cost everything.

The interactive-transcript layer is deliberately not defined here; it is Chapter 7.
-/

open MeasureTheory ProbabilityTheory

namespace AuditCP

/-- If `B` is measurable and its kernel fiber `κ t (Prod.mk t ⁻¹' B)` is at most `δ` for
`μ`-almost every `t`, then `(μ.compProd κ) B ≤ δ * μ Set.univ`. -/
theorem compProd_badEvent_le_mul
    {Ωtrain Ωaudit : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μ : AuditSampleLaw Ωtrain) [SFinite μ]
    (κ : Kernel Ωtrain Ωaudit) [IsSFiniteKernel κ]
    (B : Set (Ωtrain × Ωaudit)) (hB : MeasurableSet B) (δ : ENNReal)
    (hfiber : ∀ᵐ t ∂μ, κ t (Prod.mk t ⁻¹' B) ≤ δ) :
    (μ.compProd κ) B ≤ δ * μ Set.univ := by
  rw [Measure.compProd_apply hB]
  calc
    (∫⁻ t, κ t (Prod.mk t ⁻¹' B) ∂μ) ≤ ∫⁻ _t, δ ∂μ :=
      lintegral_mono_ae hfiber
    _ = δ * μ Set.univ := MeasureTheory.lintegral_const δ

/-- If every training-generated trajectory `g t` is admissible for `F t`, the uniform-deviation
failure event is measurable, and its kernel fiber under `κ` has probability at most `δ` for
`μtrain`-almost every training state, then measured cumulative compression progress exceeds
population progress by more than `2Δ` with probability at most `δ` under `μtrain.compProd κ`. -/
theorem kernel_randomTrajectory_goodhart
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (Ehat : Ωtrain → Ωaudit → AuditPotential ι) (E : Ωtrain → AuditPotential ι)
    (Δ : ℝ) (δ : ENNReal)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hBad : MeasurableSet
      {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ)
    (T : ℕ) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.1 p.2) (g p.1) T >
          cumCP (E p.1) (g p.1) T + 2 * Δ} ≤ δ := by
  calc
    (μtrain.compProd κ)
        {p : Ωtrain × Ωaudit |
          cumCP (Ehat p.1 p.2) (g p.1) T >
            cumCP (E p.1) (g p.1) T + 2 * Δ}
        ≤ (μtrain.compProd κ)
            {p : Ωtrain × Ωaudit |
              ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ} := by
          apply measure_mono
          intro p hp
          simp only [Set.mem_setOf_eq] at hp ⊢
          intro hUD
          exact (not_lt_of_ge (finite_audit_goodhart hUD (hadm p.1) T)) hp
    _ ≤ δ := by
      have h := compProd_badEvent_le_mul μtrain κ
        {p : Ωtrain × Ωaudit |
          ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ}
        hBad δ hfiber
      simpa [IsProbabilityMeasure.measure_univ] using h

/-- Under the hypotheses of `kernel_randomTrajectory_goodhart`, with the joint measurability
hypothesis discharged from countability of `ι` and coordinatewise measurability of `F`, `Ehat`,
and `E`, the same conclusion holds. -/
theorem kernel_countable_randomTrajectory_goodhart
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [Countable ι]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (Ehat : Ωtrain → Ωaudit → AuditPotential ι) (E : Ωtrain → AuditPotential ι)
    (Δ : ℝ) (δ : ENNReal)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hF : ∀ i, MeasurableSet {t | i ∈ F t})
    (hEhat : ∀ i, Measurable fun p : Ωtrain × Ωaudit => Ehat p.1 p.2 i)
    (hE : ∀ i, Measurable fun t => E t i)
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ)
    (T : ℕ) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.1 p.2) (g p.1) T >
          cumCP (E p.1) (g p.1) T + 2 * Δ} ≤ δ := by
  exact kernel_randomTrajectory_goodhart μtrain κ F g Ehat E Δ δ hadm
    (measurableSet_countable_uniformDev_failure F hF Ehat hEhat E hE Δ)
    hfiber T

/-- If `κ` is a conditional kernel for `ρ` (`ρ.IsCondKernel κ`), then under the remaining
hypotheses of `kernel_countable_randomTrajectory_goodhart` with the fiber bound taken relative to
`ρ.fst`, `ρ {p | cumCP (Ehat p.1 p.2) (g p.1) T > cumCP (E p.1) (g p.1) T + 2Δ} ≤ δ`. -/
theorem joint_countable_randomTrajectory_goodhart_of_condKernel
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [Countable ι]
    (ρ : AuditSampleLaw (Ωtrain × Ωaudit)) [IsProbabilityMeasure ρ]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ] [ρ.IsCondKernel κ]
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (Ehat : Ωtrain → Ωaudit → AuditPotential ι) (E : Ωtrain → AuditPotential ι)
    (Δ : ℝ) (δ : ENNReal)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hF : ∀ i, MeasurableSet {t | i ∈ F t})
    (hEhat : ∀ i, Measurable fun p : Ωtrain × Ωaudit => Ehat p.1 p.2 i)
    (hE : ∀ i, Measurable fun t => E t i)
    (hfiber : ∀ᵐ t ∂ρ.fst,
      κ t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ)
    (T : ℕ) :
    ρ {p : Ωtrain × Ωaudit |
      cumCP (Ehat p.1 p.2) (g p.1) T >
        cumCP (E p.1) (g p.1) T + 2 * Δ} ≤ δ := by
  have h := kernel_countable_randomTrajectory_goodhart
    ρ.fst κ F g Ehat E Δ δ hadm hF hEhat hE hfiber T
  rw [Measure.disintegrate ρ κ] at h
  exact h

/-- Under the hypotheses of `joint_countable_randomTrajectory_goodhart_of_condKernel` specialized
to Mathlib's regular conditional kernel `ρ.condKernel` (available when `Ωaudit` is nonempty
standard Borel), the same conclusion holds:
`ρ {p | cumCP (Ehat p.1 p.2) (g p.1) T > cumCP (E p.1) (g p.1) T + 2Δ} ≤ δ`. -/
theorem joint_countable_randomTrajectory_goodhart
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    [StandardBorelSpace Ωaudit] [Nonempty Ωaudit] [Countable ι]
    (ρ : AuditSampleLaw (Ωtrain × Ωaudit)) [IsProbabilityMeasure ρ]
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (Ehat : Ωtrain → Ωaudit → AuditPotential ι) (E : Ωtrain → AuditPotential ι)
    (Δ : ℝ) (δ : ENNReal)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hF : ∀ i, MeasurableSet {t | i ∈ F t})
    (hEhat : ∀ i, Measurable fun p : Ωtrain × Ωaudit => Ehat p.1 p.2 i)
    (hE : ∀ i, Measurable fun t => E t i)
    (hfiber : ∀ᵐ t ∂ρ.fst,
      ρ.condKernel t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ)
    (T : ℕ) :
    ρ {p : Ωtrain × Ωaudit |
      cumCP (Ehat p.1 p.2) (g p.1) T >
        cumCP (E p.1) (g p.1) T + 2 * Δ} ≤ δ := by
  exact joint_countable_randomTrajectory_goodhart_of_condKernel
    ρ ρ.condKernel F g Ehat E Δ δ hadm hF hEhat hE hfiber T

end AuditCP
