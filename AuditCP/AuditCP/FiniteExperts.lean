import AuditCP.FiniteAudit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Chapter 4 — the slack has a number

Chapter 3 leaves `Δ` as a hypothesis.  This chapter supplies it, and in doing so introduces the
third base type: B7 `AuditSampleLaw`, the probability law of the audit panel.  Nothing here touches
the ledger; the whole chapter is a statement about a B2 potential pair over a B4 envelope, made
probable by a B7 law.

The proof is the standard finite-experts pipeline: bounded centered observations are sub-Gaussian,
the sum of independent observations has a Hoeffding tail, negation supplies the second tail, and a
finite union bound makes the deviation simultaneous over every candidate.  Independence is required
per candidate ACROSS PANEL POSITIONS and never across candidates, so one shared panel with
arbitrarily correlated candidates is admitted by the binders rather than excused in prose.

The theorem is deliberately stated for general bounded real losses, not only zero-one loss.  The
candidate family is a fixed finite type and the panel randomness lives in the B7 law; panel-
dependent candidate generation is outside this theorem's scope.

What the radius prices is the log-cardinality of the declared envelope and nothing else: not the
horizon, not the number of reuses, not the adaptivity of the selection.  There is no parameter-count
symbol because the route reads the envelope, not the parameterization.
-/

open MeasureTheory ProbabilityTheory

namespace AuditCP

/-- The finite-experts uniform-deviation radius, `L·√(log(2N/δ)/(2n))`, for `N` candidates, panel
size `n`, loss range `L`, and failure probability `δ` (hoeffding1963). -/
noncomputable def deltaFiniteExperts (N n : ℕ) (L δ : ℝ) : ℝ :=
  L * Real.sqrt (Real.log (2 * (N : ℝ) / δ) / (2 * (n : ℝ)))

/-- If each `Y i j` is `μ`-sub-Gaussian with proxy `(L/2)²` and, for each candidate `i`,
independent across panel positions `j`, then with probability at least `1 − δ` the panel means
`(∑ⱼ Y i j) / n` all lie within `deltaFiniteExperts (card ι) n L δ` of `0` (hoeffding1963). -/
theorem finite_experts_subgaussian_uniformDev
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : AuditSampleLaw Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 < L) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (Y : ι → Fin n → Ω → ℝ)
    (hsub : ∀ i j, HasSubgaussianMGF (Y i j) ((‖L‖₊ / 2) ^ 2) μ)
    (hindep : ∀ i, iIndepFun (Y i) μ) :
    1 - δ ≤ μ.real {ω | UniformDev Set.univ
      (fun i => (∑ j, Y i j ω) / (n : ℝ)) (fun _ => 0)
      (deltaFiniteExperts (Fintype.card ι) n L δ)} := by
  classical
  set N := Fintype.card ι with hN
  have hNpos : 0 < N := Fintype.card_pos
  have hRpos : (0 : ℝ) < L := hL
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  have hposarg : (0 : ℝ) < 2 * (N : ℝ) / δ :=
    div_pos (mul_pos (by norm_num) hNR) hδ0
  have hlog : 0 ≤ Real.log (2 * (N : ℝ) / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; nlinarith [hN1, hδ1])
  set Δ : ℝ := deltaFiniteExperts N n L δ with hΔdef
  have hΔ2 : Δ ^ 2 =
      L ^ 2 * (Real.log (2 * (N : ℝ) / δ) / (2 * (n : ℝ))) := by
    rw [hΔdef, deltaFiniteExperts, mul_pow,
      Real.sq_sqrt (div_nonneg hlog (by positivity))]
  have hε : (0 : ℝ) ≤ (n : ℝ) * Δ := by
    rw [hΔdef, deltaFiniteExperts]
    exact mul_nonneg (Nat.cast_nonneg n)
      (mul_nonneg hRpos.le (Real.sqrt_nonneg _))
  have hSnn :
      (∑ _j ∈ (Finset.univ : Finset (Fin n)), ((‖L‖₊ / 2) ^ 2)) =
        (n : NNReal) * ((‖L‖₊ / 2) ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : ∀ i : ι,
      μ.real {ω | Δ ≤ |(∑ j, Y i j ω) / (n : ℝ)|} ≤ δ / (N : ℝ) := by
    intro i
    have hUp : μ.real {ω | (n : ℝ) * Δ ≤ ∑ j, Y i j ω} ≤
        δ / (2 * (N : ℝ)) := by
      refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
        (hindep i) (fun j _ => hsub i j) hε).trans (le_of_eq ?_)
      rw [hSnn]
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg hRpos.le]
      rw [show δ / (2 * (N : ℝ)) =
          Real.exp (-(Real.log (2 * (N : ℝ) / δ))) from by
        rw [Real.exp_neg, Real.exp_log hposarg, inv_div]]
      congr 1
      rw [mul_pow, hΔ2]
      field_simp
    have hindepNeg : iIndepFun (fun (j : Fin n) (ω : Ω) => -(Y i j ω)) μ := by
      exact (hindep i).comp (fun _ : Fin n => (Neg.neg : ℝ → ℝ))
        (fun _ => measurable_neg)
    have hsubNeg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        HasSubgaussianMGF (fun ω => -(Y i j ω)) ((‖L‖₊ / 2) ^ 2) μ :=
      fun j _ => (hsub i j).neg
    have hLo : μ.real {ω | (n : ℝ) * Δ ≤ ∑ j, -(Y i j ω)} ≤
        δ / (2 * (N : ℝ)) := by
      refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
        hindepNeg hsubNeg hε).trans (le_of_eq ?_)
      rw [hSnn]
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg hRpos.le]
      rw [show δ / (2 * (N : ℝ)) =
          Real.exp (-(Real.log (2 * (N : ℝ) / δ))) from by
        rw [Real.exp_neg, Real.exp_log hposarg, inv_div]]
      congr 1
      rw [mul_pow, hΔ2]
      field_simp
    have hsubset : {ω | Δ ≤ |(∑ j, Y i j ω) / (n : ℝ)|} ⊆
        {ω | (n : ℝ) * Δ ≤ ∑ j, Y i j ω} ∪
          {ω | (n : ℝ) * Δ ≤ ∑ j, -(Y i j ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
      rw [abs_div, abs_of_nonneg hnR.le] at hω
      have hn' : (n : ℝ) * Δ ≤ |∑ j, Y i j ω| := by
        rw [mul_comm]
        exact (le_div_iff₀ hnR).mp hω
      rcases le_abs.mp hn' with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [Finset.sum_neg_distrib]; exact h)
    calc
      μ.real {ω | Δ ≤ |(∑ j, Y i j ω) / (n : ℝ)|}
          ≤ μ.real ({ω | (n : ℝ) * Δ ≤ ∑ j, Y i j ω} ∪
              {ω | (n : ℝ) * Δ ≤ ∑ j, -(Y i j ω)}) :=
            measureReal_mono hsubset
      _ ≤ μ.real {ω | (n : ℝ) * Δ ≤ ∑ j, Y i j ω} +
            μ.real {ω | (n : ℝ) * Δ ≤ ∑ j, -(Y i j ω)} :=
          measureReal_union_le _ _
      _ ≤ δ / (2 * (N : ℝ)) + δ / (2 * (N : ℝ)) := by
        linarith [hUp, hLo]
      _ = δ / (N : ℝ) := by field_simp; ring
  set G : Set Ω := {ω | ∀ i, |(∑ j, Y i j ω) / (n : ℝ)| ≤ Δ} with hG
  have hcompl : Gᶜ ⊆ ⋃ i ∈ (Finset.univ : Finset ι),
      {ω | Δ ≤ |(∑ j, Y i j ω) / (n : ℝ)|} := by
    intro ω hω
    simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ i) (le_of_lt hi)
  have hbad : μ.real Gᶜ ≤ δ := by
    calc
      μ.real Gᶜ
          ≤ μ.real (⋃ i ∈ (Finset.univ : Finset ι),
              {ω | Δ ≤ |(∑ j, Y i j ω) / (n : ℝ)|}) :=
            measureReal_mono hcompl (measure_ne_top μ _)
      _ ≤ ∑ i ∈ (Finset.univ : Finset ι),
            μ.real {ω | Δ ≤ |(∑ j, Y i j ω) / (n : ℝ)|} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset ι), δ / (N : ℝ) :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = δ := by
        rw [Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul]
        field_simp
  have hsplit : (1 : ℝ) ≤ μ.real G + μ.real Gᶜ := by
    have h := measureReal_union_le (μ := μ) G Gᶜ
    rwa [Set.union_compl_self, probReal_univ] at h
  have hgood : 1 - δ ≤ μ.real G := by linarith [hbad, hsplit]
  simpa only [UniformDev, Set.mem_univ, forall_const, sub_zero, hN, hΔdef] using hgood

/-- If each `Y i j` is measurable, a.e. valued in `[a, b]`, centered (`∫ Y i j ∂μ = 0`), and
independent across panel positions `j` for each candidate `i`, then with probability at least
`1 − δ` the panel means lie within `deltaFiniteExperts (card ι) n (b - a) δ` of `0`
(hoeffding1963; cesabianchi2006). -/
theorem finite_experts_uniformDev
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : AuditSampleLaw Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (Y : ι → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, AEMeasurable (Y i j) μ)
    (hbdd : ∀ i j, ∀ᵐ ω ∂μ, Y i j ω ∈ Set.Icc a b)
    (hcent : ∀ i j, ∫ ω, Y i j ω ∂μ = 0)
    (hindep : ∀ i, iIndepFun (Y i) μ) :
    1 - δ ≤ μ.real {ω | UniformDev Set.univ
      (fun i => (∑ j, Y i j ω) / (n : ℝ)) (fun _ => 0)
      (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} := by
  apply finite_experts_subgaussian_uniformDev μ n hn (b - a) (sub_pos.mpr hab)
    δ hδ0 hδ1 Y
  · intro i j
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hmeas i j) (hbdd i j) (hcent i j)
  · exact hindep

/-- The population loss of candidate `i` under the law `Q`, `∫ loss i z ∂Q`. -/
noncomputable def populationLoss {Z ι : Type*} [MeasurableSpace Z]
    (Q : AuditSampleLaw Z) (loss : ι → Z → ℝ) (i : ι) : ℝ :=
  ∫ z, loss i z ∂Q

/-- The empirical mean loss of candidate `i` on the panel, `(∑ⱼ loss i (panel j)) / n`. -/
noncomputable def empiricalLoss {Z ι : Type*} {n : ℕ}
    (loss : ι → Z → ℝ) (i : ι) (panel : Fin n → Z) : ℝ :=
  (∑ j, loss i (panel j)) / (n : ℝ)

/-- If every candidate's loss is measurable and a.e. valued in `[a, b]` under `Q`, then on an
i.i.d. panel of size `n` drawn from `Q`, with probability at least `1 − δ` the empirical loss
`empiricalLoss loss i panel` and the population loss `populationLoss Q loss i` agree within
`deltaFiniteExperts (card ι) n (b - a) δ` for every candidate `i` (hoeffding1963; cesabianchi2006). -/
theorem finite_experts_iid_uniformDev
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [Nonempty ι]
    (Q : AuditSampleLaw Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ)
    (hmeas : ∀ i, Measurable (loss i))
    (hbdd : ∀ i, ∀ᵐ z ∂Q, loss i z ∈ Set.Icc a b) :
    1 - δ ≤ (Measure.pi (fun _ : Fin n => Q)).real {panel | UniformDev Set.univ
      (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
      (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} := by
  classical
  set panelMeasure : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => Q)
    with hpanelMeasure
  set Y : ι → Fin n → (Fin n → Z) → ℝ := fun i j panel =>
    loss i (panel j) - populationLoss Q loss i
  have hsub : ∀ i j,
      HasSubgaussianMGF (Y i j) ((‖b - a‖₊ / 2) ^ 2) panelMeasure := by
    intro i j
    have hbase : HasSubgaussianMGF
        (fun z => loss i z - populationLoss Q loss i) ((‖b - a‖₊ / 2) ^ 2) Q := by
      exact hasSubgaussianMGF_of_mem_Icc (hmeas i).aemeasurable (hbdd i)
    have hlift : HasSubgaussianMGF
        ((fun z => loss i z - populationLoss Q loss i) ∘ fun panel : Fin n → Z => panel j)
        ((‖b - a‖₊ / 2) ^ 2) panelMeasure := by
      apply HasSubgaussianMGF.of_map (measurable_pi_apply j).aemeasurable
      rw [hpanelMeasure, measurePreserving_eval (fun _ : Fin n => Q) j |>.map_eq]
      exact hbase
    simpa only [Y, Function.comp_def] using hlift
  have hindep : ∀ i, iIndepFun (Y i) panelMeasure := by
    intro i
    rw [hpanelMeasure]
    simpa only [Y] using iIndepFun_pi
      (μ := fun _ : Fin n => Q)
      (X := fun _ z => loss i z - populationLoss Q loss i)
      (fun _ => ((hmeas i).sub measurable_const).aemeasurable)
  have hcore := finite_experts_subgaussian_uniformDev panelMeasure n hn (b - a)
    (sub_pos.mpr hab) δ hδ0 hδ1 Y hsub hindep
  have hdev : ∀ i panel,
      (∑ j, Y i j panel) / (n : ℝ) =
        empiricalLoss loss i panel - populationLoss Q loss i := by
    intro i panel
    simp only [Y, empiricalLoss, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
  have hevent :
      {panel | UniformDev Set.univ (fun i => (∑ j, Y i j panel) / (n : ℝ))
          (fun _ => 0) (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} =
      {panel | UniformDev Set.univ (fun i => empiricalLoss loss i panel)
          (fun i => populationLoss Q loss i)
          (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} := by
    ext panel
    simp only [Set.mem_setOf_eq, UniformDev, Set.mem_univ, forall_const, sub_zero]
    constructor
    · intro h i
      simpa only [hdev i panel] using h i
    · intro h i
      simpa only [hdev i panel] using h i
  rw [← hevent]
  exact hcore

/-- Under the hypotheses of `finite_experts_iid_uniformDev`, the `ENNReal`-valued probability that
the panel fails uniform deviation is at most `ENNReal.ofReal δ`. -/
theorem finite_experts_iid_badEvent_le
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [Nonempty ι]
    (Q : AuditSampleLaw Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ)
    (hmeas : ∀ i, Measurable (loss i))
    (hbdd : ∀ i, ∀ᵐ z ∂Q, loss i z ∈ Set.Icc a b) :
    Measure.pi (fun _ : Fin n => Q) {panel | ¬ UniformDev Set.univ
      (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
      (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} ≤ ENNReal.ofReal δ := by
  classical
  let panelMeasure : Measure (Fin n → Z) := Measure.pi (fun _ : Fin n => Q)
  let Δ := deltaFiniteExperts (Fintype.card ι) n (b - a) δ
  let G : Set (Fin n → Z) := {panel | UniformDev Set.univ
    (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i) Δ}
  have hemp (i : ι) : Measurable (fun panel : Fin n → Z => empiricalLoss loss i panel) := by
    simp only [empiricalLoss]
    exact (Finset.measurable_sum Finset.univ
      (fun j _ => (hmeas i).comp (measurable_pi_apply j))).div_const _
  have hGset : G = ⋂ i : ι,
      {panel : Fin n → Z | |empiricalLoss loss i panel - populationLoss Q loss i| ≤ Δ} := by
    ext panel
    simp only [G, UniformDev, Set.mem_univ, forall_const, Set.mem_iInter,
      Set.mem_setOf_eq]
  have hG : MeasurableSet G := by
    rw [hGset]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le ((hemp i).sub measurable_const).abs measurable_const
  have hgood : 1 - δ ≤ panelMeasure.real G := by
    simpa only [panelMeasure, G, Δ] using
      finite_experts_iid_uniformDev Q n hn a b hab δ hδ0 hδ1 loss hmeas hbdd
  have hbadReal : panelMeasure.real Gᶜ ≤ δ := by
    rw [probReal_compl_eq_one_sub hG]
    linarith
  have hbad : panelMeasure Gᶜ ≤ ENNReal.ofReal δ := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top panelMeasure Gᶜ) hδ0.le]
    exact hbadReal
  have hBadSet :
      {panel | ¬ UniformDev Set.univ
        (fun i => empiricalLoss loss i panel) (fun i => populationLoss Q loss i)
        (deltaFiniteExperts (Fintype.card ι) n (b - a) δ)} = Gᶜ := by
    ext panel
    simp only [G, Δ, Set.mem_setOf_eq, Set.mem_compl_iff]
  rw [hBadSet]
  exact hbad

end AuditCP
