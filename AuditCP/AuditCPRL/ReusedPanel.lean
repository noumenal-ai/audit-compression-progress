import AuditCPRL.L0
import AuditCP.StructuralAudit
import AuditCP.FilteredAudit
import AuditCP.PaperMetrology
import RLTheory.MarkovDecisionProcess.MarkovDecisionProcess

/-!
# Target 2 — one evaluation panel, reused across a whole policy-improvement run

The RL carrier is `ReinforcementLearning.MDPSpec`, **not** `ReinforcementLearning.FiniteMDP`:
`FiniteMDP` bundles one fixed policy together with irreducibility and aperiodicity of the chain
that policy induces, so it cannot host the class of all `|A|^|S|` deterministic policies (most of
which induce reducible chains) (dwork2015adaptive).  `MDPSpec` carries `p₀`, `P`, `r`, `γ` and nothing else, and a
deterministic `π : S → A` enters it as `fun s => Dirac (π s)` through `MDPSpec.induced_chain`.

Three statements.

* **Main.**  Reusing one panel across an entire improvement run costs `log |A|^|S|` once and
  nothing per round: the radius is `R * √((|S| log|A| + log(2/δ)) / (2n))` with no `T`, no
  adaptivity term and no count of evaluations.  The audited potential is a **cost**, because
  `AuditCP.cumCP` telescopes to `E (g 0) - E (g T)`; `cumCP_const_sub_eq_gain` is where the
  orientation is discharged, and a return would prove the mirror statement.
* **Every horizon at once.**  The uniform-deviation event is free of `T` and of the improvement
  rule, so one panel certifies every horizon simultaneously at the same `δ`.  This strengthening is
  not in the corpus and does not follow from the corpus theorem, whose `T` is fixed before the
  probability.
* **Channel form.**  When improvement is steered by a transcript of `bits` bits enabling at most
  `M` policies per message, only the reachable envelope must be priced, and the radius becomes
  `deltaFiniteExperts (2 ^ bits * M) n L δ`: a cost in bits, not in rounds.

## What is a hypothesis and why

RLTheory has no policy-return or policy-cost functional of any kind.  The audited cost is therefore
a hypothesis `chainCost` on the *induced chain*, evaluated on exogenous panel items; that the same
`n` items score every policy is the content of "reused panel" and is likewise a hypothesis, not a
consequence.
-/

namespace AuditCPRL

open AuditCP MeasureTheory ProbabilityTheory
open ReinforcementLearning

universe u

/-- `cumCP (fun i => c - V i) g T = V (g T) - V (g 0)`. -/
theorem cumCP_const_sub_eq_gain {ι : Type*} (c : ℝ) (V : ι → ℝ) (g : ℕ → ι) (T : ℕ) :
    cumCP (fun i => c - V i) g T = V (g T) - V (g 0) := by
  rw [cumCP_telescope]; ring

section Policies
variable {S : Type u} [Fintype S] [DecidableEq S]
variable {A : Type u} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The deterministic policy `π` read as a stochastic policy, `fun s => Measure.dirac (π s)`. -/
noncomputable def detPolicy (π : S → A) : S → ProbabilityMeasure A :=
  fun s => ⟨Measure.dirac (π s), Measure.dirac.isProbabilityMeasure⟩

omit [Fintype S] [DecidableEq S] [Fintype A] in
/-- `detPolicy` is injective. -/
theorem detPolicy_injective : Function.Injective (detPolicy (S := S) (A := A)) := by
  intro π π' h
  funext s
  have h1 : Measure.dirac (π s) = Measure.dirac (π' s) :=
    congrArg Subtype.val (congrFun h s)
  exact (MeasureTheory.dirac_eq_dirac_iff).1 h1

end Policies

/-! ### The audited object: the chain the MDP produces under a deterministic policy -/

section Panel
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The audited cost of policy `π` on panel item `z`,
`R - chainReturn (mdp.induced_chain (detPolicy π)) z`. -/
noncomputable def policyCost {Z : Type*} (mdp : MDPSpec (S := S) (A := A)) (R : ℝ)
    (chainReturn : MarkovChain.HomMarkovChainSpec (S × A) → Z → ℝ) : (S → A) → Z → ℝ :=
  fun π z => R - chainReturn (mdp.induced_chain (detPolicy π)) z

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Given `0 < δ`, `deltaFiniteExperts (Fintype.card (S → A)) n (R - 0) δ =
R * √((Fintype.card S * log (Fintype.card A) + log (2 / δ)) / (2n))`. -/
theorem deltaFiniteExperts_detPolicyClass (n : ℕ) (R : ℝ) {δ : ℝ} (hδ0 : 0 < δ) :
    deltaFiniteExperts (Fintype.card (S → A)) n (R - 0) δ
      = R * Real.sqrt
          (((Fintype.card S : ℝ) * Real.log (Fintype.card A) + Real.log (2 / δ))
            / (2 * (n : ℝ))) := by
  have hcardA : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : ((Fintype.card (S → A) : ℕ) : ℝ) = (Fintype.card A : ℝ) ^ Fintype.card S := by
    rw [Fintype.card_fun]; push_cast; ring
  have hlog : Real.log (2 * (Fintype.card (S → A) : ℝ) / δ)
      = (Fintype.card S : ℝ) * Real.log (Fintype.card A) + Real.log (2 / δ) := by
    rw [hcard, show (2 : ℝ) * ((Fintype.card A : ℝ) ^ Fintype.card S) / δ
        = 2 / δ * ((Fintype.card A : ℝ) ^ Fintype.card S) from by ring,
      Real.log_mul (div_pos (by norm_num) hδ0).ne' (pow_pos hcardA _).ne', Real.log_pow]
    ring
  simp only [deltaFiniteExperts, sub_zero, hlog]

omit [Nonempty S] [DecidableEq A] in
/-- If the policy cost is measurable and a.e. valued in `[0, R]` for every deterministic policy,
every training-generated improvement sequence is admissible for `F`, and class membership is
measurable, then on an i.i.d. panel of size `n`, the measured cumulative cost reduction exceeds
the population reduction by more than `2R√((|S| log|A| + log(2/δ)) / (2n))` with probability at
most `ENNReal.ofReal δ`, at every horizon `T`. -/
theorem policyImprovement_reusedPanel_goodhart
    {Z Ωtrain : Type*} [MeasurableSpace Z] [MeasurableSpace Ωtrain]
    (mdp : MDPSpec (S := S) (A := A))
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) {R : ℝ} (hR : 0 < R) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (chainReturn : MarkovChain.HomMarkovChainSpec (S × A) → Z → ℝ)
    (hmeas : ∀ π : S → A, Measurable (policyCost mdp R chainReturn π))
    (hbdd : ∀ π : S → A, ∀ᵐ z ∂Q, policyCost mdp R chainReturn π z ∈ Set.Icc 0 R)
    (F : Ωtrain → Set (S → A)) (improve : Ωtrain → ℕ → (S → A))
    (hadm : ∀ t, Admissible (improve t) (F t))
    (hF : ∀ π : S → A, MeasurableSet {t | π ∈ F t}) (T : ℕ) :
    (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
      {p : Ωtrain × (Fin n → Z) |
        cumCP (fun π => empiricalLoss (policyCost mdp R chainReturn) π p.2) (improve p.1) T >
          cumCP (fun π => populationLoss Q (policyCost mdp R chainReturn) π) (improve p.1) T
            + 2 * (R * Real.sqrt
                (((Fintype.card S : ℝ) * Real.log (Fintype.card A) + Real.log (2 / δ))
                  / (2 * (n : ℝ))))} ≤ ENNReal.ofReal δ := by
  simpa only [deltaFiniteExperts_detPolicyClass (S := S) (A := A) n R hδ0] using
    auditBlind_finiteTrajectory_goodhart_of_measurableClass μtrain Q n hn 0 R hR δ hδ0 hδ1
      (policyCost mdp R chainReturn) hmeas hbdd F improve hadm hF T

omit [Nonempty S] [DecidableEq A] in
/-- Under the hypotheses of `policyImprovement_reusedPanel_goodhart`, the same radius controls
every horizon simultaneously: the probability that some `T` witnesses measured cost reduction
exceeding population reduction by more than `2R√((|S| log|A| + log(2/δ)) / (2n))` is at most
`ENNReal.ofReal δ` (dwork2015adaptive). -/
theorem policyImprovement_reusedPanel_allHorizons
    {Z Ωtrain : Type*} [MeasurableSpace Z] [MeasurableSpace Ωtrain]
    (mdp : MDPSpec (S := S) (A := A))
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) {R : ℝ} (hR : 0 < R) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (chainReturn : MarkovChain.HomMarkovChainSpec (S × A) → Z → ℝ)
    (hmeas : ∀ π : S → A, Measurable (policyCost mdp R chainReturn π))
    (hbdd : ∀ π : S → A, ∀ᵐ z ∂Q, policyCost mdp R chainReturn π z ∈ Set.Icc 0 R)
    (F : Ωtrain → Set (S → A)) (improve : Ωtrain → ℕ → (S → A))
    (hadm : ∀ t, Admissible (improve t) (F t))
    (hF : ∀ π : S → A, MeasurableSet {t | π ∈ F t}) :
    (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
      {p : Ωtrain × (Fin n → Z) | ∃ T : ℕ,
        cumCP (fun π => empiricalLoss (policyCost mdp R chainReturn) π p.2) (improve p.1) T >
          cumCP (fun π => populationLoss Q (policyCost mdp R chainReturn) π) (improve p.1) T
            + 2 * (R * Real.sqrt
                (((Fintype.card S : ℝ) * Real.log (Fintype.card A) + Real.log (2 / δ))
                  / (2 * (n : ℝ))))} ≤ ENNReal.ofReal δ := by
  classical
  rw [← deltaFiniteExperts_detPolicyClass (S := S) (A := A) n R hδ0]
  set loss : (S → A) → Z → ℝ := policyCost mdp R chainReturn with hlossdef
  set Δ : ℝ := deltaFiniteExperts (Fintype.card (S → A)) n (R - 0) δ with hΔdef
  have hemp : ∀ π : S → A, Measurable fun panel : Fin n → Z => empiricalLoss loss π panel := by
    intro π
    simp only [empiricalLoss]
    exact (Finset.measurable_sum Finset.univ fun j _ =>
      (hmeas π).comp (measurable_pi_apply j)).div_const _
  have hBad : MeasurableSet
      {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (F p.1)
        (fun π => empiricalLoss loss π p.2) (fun π => populationLoss Q loss π) Δ} :=
    measurableSet_countable_uniformDev_failure F hF
      (fun _t panel π => empiricalLoss loss π panel)
      (fun π => (hemp π).comp measurable_snd)
      (fun _t π => populationLoss Q loss π) (fun _π => measurable_const) Δ
  have hmaster := finite_experts_iid_badEvent_le Q n hn 0 R hR δ hδ0 hδ1 loss hmeas hbdd
  have hfiber : ∀ᵐ t ∂μtrain,
      Measure.pi (fun _ : Fin n => Q) {panel | ¬ UniformDev (F t)
        (fun π => empiricalLoss loss π panel) (fun π => populationLoss Q loss π) Δ}
        ≤ ENNReal.ofReal δ := by
    refine Filter.Eventually.of_forall fun t => le_trans (measure_mono ?_) hmaster
    intro panel hfail
    simp only [Set.mem_setOf_eq] at hfail ⊢
    intro hmasterDev
    exact hfail fun π _ => hmasterDev π (Set.mem_univ π)
  calc
    (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
        {p : Ωtrain × (Fin n → Z) | ∃ T : ℕ,
          cumCP (fun π => empiricalLoss loss π p.2) (improve p.1) T >
            cumCP (fun π => populationLoss Q loss π) (improve p.1) T + 2 * Δ}
        ≤ (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
            {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (F p.1)
              (fun π => empiricalLoss loss π p.2) (fun π => populationLoss Q loss π) Δ} := by
          refine measure_mono fun p hp => ?_
          simp only [Set.mem_setOf_eq] at hp ⊢
          intro hUD
          obtain ⟨T, hT⟩ := hp
          exact (not_lt_of_ge
            (finite_audit_goodhart_twoPoint hUD (hadm p.1 0) (hadm p.1 T))) hT
    _ ≤ ENNReal.ofReal δ :=
        auditBlind_randomClass_badEvent_le μtrain (Measure.pi (fun _ : Fin n => Q)) F
          (fun F' panel => ¬ UniformDev F' (fun π => empiricalLoss loss π panel)
            (fun π => populationLoss Q loss π) Δ) (ENNReal.ofReal δ) hBad hfiber

omit [Nonempty S] [DecidableEq S] [DecidableEq A] [Nonempty A] in
/-- If improvement is steered by a disclosure `D` with `bits`-bit transcript budget, every
transcript enables at most `M` policies, and the policy cost is measurable and a.e. valued in
`[0, L]`, then there is a measurable panel-good event `G` of co-probability at most
`ENNReal.ofReal δ` on which, for every disclosure realization and horizon, measured cumulative
cost reduction along the disclosed policy process is bounded by the population reduction plus
`2 · deltaFiniteExperts (2 ^ bits * M) n L δ` (dwork2015adaptive). -/
theorem policyImprovement_reusedPanel_bitPriced
    {Z Transcript Ω : Type*} [MeasurableSpace Z]
    [Fintype Transcript] [MeasurableSpace Transcript] [MeasurableSpace Ω]
    (mdp : MDPSpec (S := S) (A := A))
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (D : FilteredDisclosure Ω Transcript)
    (choices : Transcript → Finset (S → A)) (improve : Transcript → ℕ → (S → A))
    (hreach : ∀ τ k, improve τ k ∈ choices τ)
    (bits M : ℕ) (hbudget : HasDisclosureBudget Transcript bits)
    (hlocal : ∀ τ, (choices τ).card ≤ M) (hne : (reachableEnvelope choices).Nonempty)
    (n : ℕ) (hn : 0 < n) {L : ℝ} (hL : 0 < L) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (chainReturn : MarkovChain.HomMarkovChainSpec (S × A) → Z → ℝ)
    (hmeas : ∀ π : S → A, Measurable (policyCost mdp L chainReturn π))
    (hbdd : ∀ π : S → A, ∀ᵐ z ∂Q, policyCost mdp L chainReturn π z ∈ Set.Icc 0 L) :
    ∃ G : Set (Fin n → Z), MeasurableSet G ∧
      (Measure.pi fun _ : Fin n => Q) Gᶜ ≤ ENNReal.ofReal δ ∧
      ∀ panel ∈ G, ∀ (ω : Ω) (T : ℕ),
        cumCP (fun π => empiricalLoss (policyCost mdp L chainReturn) π panel)
            (fun k => D.candidateProcess improve k ω) T
          ≤ cumCP (fun π => populationLoss Q (policyCost mdp L chainReturn) π)
              (fun k => D.candidateProcess improve k ω) T
            + 2 * deltaFiniteExperts (2 ^ bits * M) n L δ := by
  classical
  haveI : Nonempty ↥(reachableEnvelope choices) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  set loss : (S → A) → Z → ℝ := policyCost mdp L chainReturn with hlossdef
  set env : Finset (S → A) := reachableEnvelope choices with henvdef
  set lossE : ↥env → Z → ℝ := fun e => loss ↑e with hlossE
  set Δ₀ : ℝ := deltaFiniteExperts (Fintype.card ↥env) n (L - 0) δ with hΔ₀
  have hempE : ∀ e : ↥env, Measurable fun panel : Fin n → Z => empiricalLoss lossE e panel := by
    intro e
    simp only [empiricalLoss]
    exact (Finset.measurable_sum Finset.univ fun j _ =>
      (hmeas ↑e).comp (measurable_pi_apply j)).div_const _
  refine ⟨{panel : Fin n → Z | UniformDev Set.univ
      (fun e : ↥env => empiricalLoss lossE e panel)
      (fun e : ↥env => populationLoss Q lossE e) Δ₀}, ?_, ?_, ?_⟩
  · have hrewrite : {panel : Fin n → Z | UniformDev Set.univ
        (fun e : ↥env => empiricalLoss lossE e panel)
        (fun e : ↥env => populationLoss Q lossE e) Δ₀}
        = ⋂ e : ↥env, {panel : Fin n → Z |
            |empiricalLoss lossE e panel - populationLoss Q lossE e| ≤ Δ₀} := by
      ext panel
      simp only [UniformDev, Set.mem_univ, forall_const, Set.mem_iInter, Set.mem_setOf_eq]
    rw [hrewrite]
    exact MeasurableSet.iInter fun e =>
      measurableSet_le ((hempE e).sub measurable_const).abs measurable_const
  · simpa only [Set.compl_setOf] using
      finite_experts_iid_badEvent_le Q n hn 0 L hL δ hδ0 hδ1 lossE
        (fun e => hmeas ↑e) (fun e => hbdd ↑e)
  · intro panel hpanelG ω T
    have hUD0 : UniformDev (↑env : Set (S → A))
        (fun π => empiricalLoss loss π panel) (fun π => populationLoss Q loss π) Δ₀ :=
      fun π hπ => hpanelG ⟨π, hπ⟩ (Set.mem_univ _)
    have hmono : Δ₀ ≤ deltaFiniteExperts (2 ^ bits * M) n L δ := by
      rw [hΔ₀, Fintype.card_coe, sub_zero]
      exact deltaFiniteExperts_mono_candidateBound (Finset.card_pos.2 hne)
        (reachableEnvelope_card_le_of_disclosureBudget choices bits M hbudget hlocal)
        hn hL.le hδ0
    exact D.filteredPolicy_goodhart choices improve hreach _ _ _
      (fun π hπ => le_trans (hUD0 π hπ) hmono) ω T

end Panel

end AuditCPRL
