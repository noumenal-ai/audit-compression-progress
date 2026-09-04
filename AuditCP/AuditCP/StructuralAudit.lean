import AuditCP.FiniteExperts
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Chapter 5 — the envelope may be random, the audit may not see it

The training side of an audit is an arbitrary training-indexed B4 envelope `F : Ωtrain → Set ι`;
the sealed audit is the other coordinate of a product B7 law.  Both coordinates are B1 carriers and
nothing more; there is no finite-class, countability, label, or loss restriction.

The structural condition is positional, exactly as in the interface chapters: `F` and the
trajectory `g` may consume only the training coordinate `p.1`.  That is the whole of audit
blindness at this level — it is a fact about which coordinate a function is allowed to read, not a
fact about the learner's construction.

The product-event identity used below is Mathlib's `MeasureTheory.Measure.prod_apply`
(`Mathlib/MeasureTheory/Measure/Prod.lean`, pinned source line 223).  Independence of measurable
functions of the two coordinates is already supplied by `ProbabilityTheory.indepFun_prod`
(`Mathlib/Probability/Independence/Basic.lean`, pinned source line 725); AuditCP does not duplicate
that theorem.

The theorem's event-specific measurability premise is deliberate.  A map
`Γ : Ωtrain → Set ι` is not silently treated as a measurable multifunction: measurable graphs,
hit events, containment events, and suprema over an uncountable class are distinct obligations.
-/

open MeasureTheory

namespace AuditCP

/-- If `ι` is countable, membership in `F` is measurable in the training coordinate, and `Ehat`
and `E` are measurable in their respective coordinates at each candidate `i`, then the failure
event `{p | ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ}` is measurable. -/
theorem measurableSet_countable_uniformDev_failure
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [Countable ι]
    (F : Ωtrain → AuditEnvelope ι)
    (hF : ∀ i, MeasurableSet {t | i ∈ F t})
    (Ehat : Ωtrain → Ωaudit → AuditPotential ι)
    (hEhat : ∀ i, Measurable fun p : Ωtrain × Ωaudit => Ehat p.1 p.2 i)
    (E : Ωtrain → AuditPotential ι)
    (hE : ∀ i, Measurable fun t => E t i)
    (Δ : ℝ) :
    MeasurableSet
      {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ} := by
  classical
  let V : ι → Set (Ωtrain × Ωaudit) := fun i =>
    {p | i ∈ F p.1 ∧ Δ < |Ehat p.1 p.2 i - E p.1 i|}
  have hEvent :
      {p : Ωtrain × Ωaudit |
        ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ} = ⋃ i, V i := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_setOf_eq, UniformDev, not_forall, not_le] at hp
      obtain ⟨i, hiF, hi⟩ := hp
      exact Set.mem_iUnion.2 ⟨i, hiF, hi⟩
    · intro hp
      obtain ⟨i, hiF, hi⟩ := Set.mem_iUnion.1 hp
      simp only [Set.mem_setOf_eq, UniformDev]
      intro hUD
      exact (not_lt_of_ge (hUD i hiF)) hi
  rw [hEvent]
  apply MeasurableSet.iUnion
  intro i
  change MeasurableSet
    ({p : Ωtrain × Ωaudit | i ∈ F p.1} ∩
      {p : Ωtrain × Ωaudit | Δ < |Ehat p.1 p.2 i - E p.1 i|})
  apply MeasurableSet.inter
  · exact (hF i).preimage measurable_fst
  · exact measurableSet_lt measurable_const
      ((hEhat i).sub ((hE i).comp measurable_fst)).abs

/-- If the event `{p | Bad (Γ p.1) p.2}` is measurable and its audit fiber `{a | Bad (Γ t) a}` has
`μaudit`-probability at most `δ` for `μtrain`-almost every training history `t`, then its
probability under the product law `μtrain.prod μaudit` is at most `δ`. -/
theorem auditBlind_randomClass_badEvent_le
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (μaudit : AuditSampleLaw Ωaudit) [IsProbabilityMeasure μaudit]
    (Γ : Ωtrain → AuditEnvelope ι) (Bad : AuditEnvelope ι → Ωaudit → Prop) (δ : ENNReal)
    (hBad : MeasurableSet {p : Ωtrain × Ωaudit | Bad (Γ p.1) p.2})
    (hfiber : ∀ᵐ t ∂μtrain, μaudit {a | Bad (Γ t) a} ≤ δ) :
    (μtrain.prod μaudit) {p : Ωtrain × Ωaudit | Bad (Γ p.1) p.2} ≤ δ := by
  rw [Measure.prod_apply hBad]
  calc
    (∫⁻ t, μaudit (Prod.mk t ⁻¹' {p : Ωtrain × Ωaudit | Bad (Γ p.1) p.2}) ∂μtrain)
        ≤ ∫⁻ _t, δ ∂μtrain := by
          apply lintegral_mono_ae
          filter_upwards [hfiber] with t ht
          exact ht
    _ = δ := by
      simp [MeasureTheory.lintegral_const, IsProbabilityMeasure.measure_univ]

/-- If every training-generated trajectory `g t` is admissible for `F t`, the uniform-deviation
failure event is measurable, and its audit fiber has probability at most `δ` for `μtrain`-almost
every training history, then measured cumulative compression progress exceeds true progress by
more than `2Δ` with probability at most `δ` under `μtrain.prod μaudit`. -/
theorem auditBlind_randomTrajectory_goodhart
    {Ωtrain Ωaudit ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (μaudit : AuditSampleLaw Ωaudit) [IsProbabilityMeasure μaudit]
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (Ehat : Ωaudit → AuditPotential ι) (E : AuditPotential ι) (Δ : ℝ) (δ : ENNReal)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hBad : MeasurableSet
      {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.2) E Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      μaudit {a | ¬ UniformDev (F t) (Ehat a) E Δ} ≤ δ)
    (T : ℕ) :
    (μtrain.prod μaudit)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.2) (g p.1) T > cumCP E (g p.1) T + 2 * Δ} ≤ δ := by
  calc
    (μtrain.prod μaudit)
        {p : Ωtrain × Ωaudit |
          cumCP (Ehat p.2) (g p.1) T > cumCP E (g p.1) T + 2 * Δ}
        ≤ (μtrain.prod μaudit)
            {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.2) E Δ} := by
          apply measure_mono
          intro p hp
          simp only [Set.mem_setOf_eq] at hp ⊢
          intro hUD
          exact (not_lt_of_ge (finite_audit_goodhart hUD (hadm p.1) T)) hp
    _ ≤ δ :=
      auditBlind_randomClass_badEvent_le μtrain μaudit F
        (fun F' a => ¬ UniformDev F' (Ehat a) E Δ) δ hBad hfiber

/-- If every candidate's loss is measurable and a.e. valued in `[a, b]` under `Q`, every
training-generated trajectory is admissible for `F`, and the resulting uniform-deviation failure
event is measurable, then on an i.i.d. panel of size `n` drawn from `Q`, measured cumulative
empirical-loss progress exceeds population-loss progress by more than
`2 · deltaFiniteExperts (card ι) n (b - a) δ` with probability at most `ENNReal.ofReal δ`. -/
theorem auditBlind_finiteTrajectory_goodhart
    {Ωtrain Z ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Z] [Fintype ι] [Nonempty ι]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : AuditSampleLaw Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ)
    (hmeas : ∀ i, Measurable (loss i))
    (hbdd : ∀ i, ∀ᵐ z ∂Q, loss i z ∈ Set.Icc a b)
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hBad : MeasurableSet
      {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (F p.1)
        (fun i => empiricalLoss loss i p.2) (fun i => populationLoss Q loss i)
        (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)})
    (T : ℕ) :
    (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
      {p : Ωtrain × (Fin n → Z) |
        cumCP (fun i => empiricalLoss loss i p.2) (g p.1) T >
          cumCP (fun i => populationLoss Q loss i) (g p.1) T +
            2 * deltaFiniteExperts (Fintype.card ι) n (b - a) δ} ≤
      ENNReal.ofReal δ := by
  have hmaster := finite_experts_iid_badEvent_le
    Q n hn a b hab δ hδ0 hδ1 loss hmeas hbdd
  have hfiber : ∀ᵐ t ∂μtrain,
      Measure.pi (fun _ : Fin n => Q) {panel | ¬ UniformDev (F t)
        (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
        (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} ≤ ENNReal.ofReal δ :=
    Filter.Eventually.of_forall fun t => by
      calc
        Measure.pi (fun _ : Fin n => Q) {panel | ¬ UniformDev (F t)
            (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
            (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)}
            ≤ Measure.pi (fun _ : Fin n => Q) {panel | ¬ UniformDev Set.univ
                (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
                (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} := by
              apply measure_mono
              intro panel hfail
              simp only [Set.mem_setOf_eq] at hfail ⊢
              intro hmasterDev
              apply hfail
              intro i hi
              exact hmasterDev i (Set.mem_univ i)
        _ ≤ ENNReal.ofReal δ := hmaster
  exact auditBlind_randomTrajectory_goodhart μtrain
    (Measure.pi (fun _ : Fin n => Q)) F g
    (fun panel i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
    (deltaFiniteExperts (Fintype.card ι) n (b - a) δ) (ENNReal.ofReal δ)
    hadm hBad hfiber T

/-- Under the hypotheses of `auditBlind_finiteTrajectory_goodhart`, with the joint measurability
hypothesis replaced by measurability of each candidate's training-generated class membership
`{t | i ∈ F t}`, the same conclusion holds. -/
theorem auditBlind_finiteTrajectory_goodhart_of_measurableClass
    {Ωtrain Z ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Z] [Fintype ι] [Nonempty ι]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : AuditSampleLaw Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ)
    (hmeas : ∀ i, Measurable (loss i))
    (hbdd : ∀ i, ∀ᵐ z ∂Q, loss i z ∈ Set.Icc a b)
    (F : Ωtrain → AuditEnvelope ι) (g : Ωtrain → AuditTrajectory ι)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hF : ∀ i, MeasurableSet {t | i ∈ F t})
    (T : ℕ) :
    (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
      {p : Ωtrain × (Fin n → Z) |
        cumCP (fun i => empiricalLoss loss i p.2) (g p.1) T >
          cumCP (fun i => populationLoss Q loss i) (g p.1) T +
            2 * deltaFiniteExperts (Fintype.card ι) n (b - a) δ} ≤
      ENNReal.ofReal δ := by
  have hemp : ∀ i, Measurable (fun panel : Fin n → Z => empiricalLoss loss i panel) := by
    intro i
    simp only [empiricalLoss]
    exact (Finset.measurable_sum Finset.univ fun j _ =>
      (hmeas i).comp (measurable_pi_apply j)).div_const _
  have hBad : MeasurableSet
      {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (F p.1)
        (fun i => empiricalLoss loss i p.2) (fun i => populationLoss Q loss i)
        (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} :=
    measurableSet_countable_uniformDev_failure F hF
      (fun _t panel i => empiricalLoss loss i panel)
      (fun i => (hemp i).comp measurable_snd)
      (fun _t i => populationLoss Q loss i)
      (fun _i => measurable_const)
      (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)
  exact auditBlind_finiteTrajectory_goodhart μtrain Q n hn a b hab δ hδ0 hδ1
    loss hmeas hbdd F g hadm hBad T

end AuditCP
