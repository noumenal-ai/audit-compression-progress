import AuditCPRL.BellmanLadder
import AuditCP.FilteredAudit
import AuditCP.PaperMetrology

/-!
# Target 6 — a Q-learning agent that closes its own dynamics on the audit signal

The agent is allowed to rewrite, as an arbitrary function of the realized audit outcome, both its
behaviour path and its step-size schedule.  Formally the whole `QLearningSpec` becomes a function
of the audit outcome, and `ReinforcementLearning.QLearning.QLearningIterates` is imposed for each
realization: `spec t o` supplies the step sizes actually used, `path t o` the transitions actually
visited.  Reported compression progress still cannot exceed true progress by more than the
pre-committed `2Δ`.

The RL-side ingredient is an **audit-independent invariant sup-norm ball**.  For a reward cap and a
budget `B` closed under the Bellman target, the Q-learning iterates stay in `qBall B` along every
sample path and every step-size sequence in `[0,1]`, because each update is a convex combination
toward a bounded target.  RLTheory does not have this: `QLearningSpec.α : ℕ → ℝ` is unconstrained
and `StochasticApproximation.RobbinsMonro` imposes no upper bound.  Restricting the step sizes to
`[0,1]` is exactly the price of admitting self-modification of the schedule.

Three properties are the content.

* **Two points, not a path.**  `AuditCPRL.finite_audit_goodhart_twoPoint` reads the trajectory only
  at `0` and `T`, so for a single declared reporting horizon the interface requirement is two-point
  containment and the iterates may leave the ball in between.  The invariant ball is needed only
  for validity at every horizon at once.
* **No regularity on the self-modification.**  `AuditCP.kernel_adaptiveTrajectory_goodhart` reaches
  the bound's event by `measure_mono`, so the map from audit outcome to rewritten dynamics needs
  no measurability, adaptedness or integrability.  Every RLTheory convergence route assumes
  measurability of the update.
* **No horizon factor, no behaviour-policy term, no schedule term** in the penalty.

## The obligation, closed by changing the envelope

`selfModifying_qlearning_audit_goodhart` and its two-point form carry the audit-side premise
`hfiber` on `qBall B`.  That premise cannot be discharged, and the reason is not a missing lemma:
the ball is the wrong envelope.  It is a superset of everything the audit can read, it is a
continuum, and every in-scope concentration route
(`AuditCP.finite_experts_iid_badEvent_le`) carries `[Fintype ι]`.

The right envelope is the **disclosed endpoint set**.  Condition on the training coordinate; given
it, the agent's iterates are a deterministic function of the transcript the interface released, and
a declared reporting horizon reads the ledger at `0` and `T` only.  So the audited class is
`⋃ τ, {q t τ 0 (path t τ), q t τ T (path t τ)}`, of cardinality at most `2 * 2 ^ bits` under
`AuditCP.HasDisclosureBudget`; it is fixed before the panel is drawn and the realized transcript
merely selects a member of it.  `transcriptEndpoints_bitPriced_goodhart` and
`selfModifying_qlearning_audit_goodhart_bitPriced` are that statement, with radius
`AuditCP.deltaFiniteExperts (2 * 2 ^ bits) n (b - a) δ` — the class term is the disclosure bits and
nothing else: no covering number, no `|S| |A|`, no horizon.

The ball keeps exactly one job in the closed form: the **range**.
`qBall_invariant_of_stepSize_mem_Icc` is the range lemma — the iterates stay in the ball, so the
audited loss is bounded by `b - a` at the two endpoints under an arbitrarily self-rewritten
schedule — and it is not the envelope lemma.  The ball-as-envelope statements are kept because they
are more general in the audit kernel, the potentials and the resolution; their `hfiber` stays named,
and is now a hypothesis about a superset rather than an open obligation of the module.
-/

namespace AuditCPRL

open AuditCP MeasureTheory ProbabilityTheory RLTheory
open ReinforcementLearning ReinforcementLearning.QLearning

universe u

/-! ### The audit-side ingredient: a declared finite envelope inside a continuum carrier -/

/-- If `env` is a nonempty finite subset of `ι` with `env.card ≤ N`, and `loss` is measurable and
a.e. valued in `[a, b]` on `env`, then on an i.i.d. panel of size `n`, the probability that `env`
fails uniform deviation at radius `deltaFiniteExperts N n (b - a) δ` is at most
`ENNReal.ofReal δ`. -/
theorem finiteEnvelope_badEvent_le {Z ι : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (n : ℕ) (hn : 0 < n)
    {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ) (env : Finset ι) (hne : env.Nonempty) {N : ℕ} (hN : env.card ≤ N)
    (hmeas : ∀ θ ∈ env, Measurable (loss θ))
    (hbdd : ∀ θ ∈ env, ∀ᵐ z ∂Q, loss θ z ∈ Set.Icc a b) :
    Measure.pi (fun _ : Fin n => Q)
        {panel | ¬ UniformDev (↑env : Set ι)
          (fun θ => empiricalLoss loss θ panel) (fun θ => populationLoss Q loss θ)
          (deltaFiniteExperts N n (b - a) δ)}
      ≤ ENNReal.ofReal δ := by
  classical
  haveI : Nonempty ↥env := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have key := finite_experts_iid_badEvent_le (ι := ↥env) Q n hn a b hab δ hδ0 hδ1
    (fun e => loss ↑e) (fun e => hmeas ↑e e.2) (fun e => hbdd ↑e e.2)
  rw [Fintype.card_coe] at key
  have hmono : deltaFiniteExperts env.card n (b - a) δ ≤ deltaFiniteExperts N n (b - a) δ :=
    deltaFiniteExperts_mono_candidateBound (Finset.card_pos.2 hne) hN hn
      (sub_nonneg.2 hab.le) hδ0
  refine le_trans (measure_mono ?_) key
  intro panel hpanel
  simp only [Set.mem_setOf_eq] at hpanel ⊢
  intro hUD
  exact hpanel fun θ hθ => le_trans (hUD ⟨θ, hθ⟩ (Set.mem_univ _)) hmono

/-! ### The disclosed endpoint set: the audited class of a transcript-driven learner -/

/-- If the transcript alphabet has a `bits`-bit disclosure budget, `loss` is measurable, and both
endpoints `g t τ 0` and `g t τ T` are measurable in `t` and a.e. loss-bounded in `[a, b]`, then on
an i.i.d. panel of size `n`, for any disclosure map `disclose`, measured cumulative compression
progress along the disclosed endpoint trajectory `g · (disclose · ·)` exceeds population progress
by more than `2 · deltaFiniteExperts (2 · 2^bits) n (b - a) δ` with probability at most
`ENNReal.ofReal δ` (dwork2015adaptive). -/
theorem transcriptEndpoints_bitPriced_goodhart
    {Ωtrain Transcript Z ι : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Z] [MeasurableSpace ι]
    [Fintype Transcript] [Nonempty Transcript]
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (bits n : ℕ) (hbudget : HasDisclosureBudget Transcript bits) (hn : 0 < n)
    {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ) (hloss : Measurable (Function.uncurry loss))
    (g : Ωtrain → Transcript → AuditTrajectory ι) (T : ℕ)
    (hg0 : ∀ τ, Measurable fun t => g t τ 0) (hgT : ∀ τ, Measurable fun t => g t τ T)
    (hb0 : ∀ t τ, ∀ᵐ z ∂Q, loss (g t τ 0) z ∈ Set.Icc a b)
    (hbT : ∀ t τ, ∀ᵐ z ∂Q, loss (g t τ T) z ∈ Set.Icc a b)
    (disclose : Ωtrain → (Fin n → Z) → Transcript) :
    (μtrain.compProd (Kernel.const Ωtrain (Measure.pi fun _ : Fin n => Q)))
        {p : Ωtrain × (Fin n → Z) |
          cumCP (fun θ => empiricalLoss loss θ p.2) (g p.1 (disclose p.1 p.2)) T >
            cumCP (fun θ => populationLoss Q loss θ) (g p.1 (disclose p.1 p.2)) T
              + 2 * deltaFiniteExperts (2 * 2 ^ bits) n (b - a) δ}
      ≤ ENNReal.ofReal δ := by
  classical
  set Δ : ℝ := deltaFiniteExperts (2 * 2 ^ bits) n (b - a) δ with hΔ
  set env : Ωtrain → Finset ι :=
    fun t => reachableEnvelope (fun τ => ({g t τ 0, g t τ T} : Finset ι)) with henv
  have hmem0 : ∀ t τ, g t τ 0 ∈ env t := fun t τ =>
    mem_reachableEnvelope _ τ (Finset.mem_insert_self _ _)
  have hmemT : ∀ t τ, g t τ T ∈ env t := fun t τ =>
    mem_reachableEnvelope _ τ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsplit : ∀ t θ, θ ∈ env t → ∃ τ, θ = g t τ 0 ∨ θ = g t τ T := by
    intro t θ hθ
    simp only [henv, reachableEnvelope, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] at hθ
    exact hθ
  have hcard : ∀ t, (env t).card ≤ 2 * 2 ^ bits := by
    intro t
    have hlocal : ∀ τ, ({g t τ 0, g t τ T} : Finset ι).card ≤ 2 := by
      intro τ
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    refine le_trans (reachableEnvelope_card_le_of_disclosureBudget
      (fun τ => ({g t τ 0, g t τ T} : Finset ι)) bits 2 hbudget hlocal) ?_
    exact le_of_eq (Nat.mul_comm _ _)
  have hpop : Measurable fun θ : ι => populationLoss Q loss θ := by
    have h := (hloss.stronglyMeasurable).integral_kernel_prod_right' (κ := Kernel.const ι Q)
    simp only [Kernel.const_apply] at h
    simpa only [populationLoss, Function.uncurry_apply_pair] using h.measurable
  have hcent : ∀ e : Ωtrain → ι, Measurable e →
      Measurable fun p : Ωtrain × (Fin n → Z) =>
        empiricalLoss loss (e p.1) p.2 - populationLoss Q loss (e p.1) := by
    intro e he
    have hemp : Measurable fun p : Ωtrain × (Fin n → Z) => empiricalLoss loss (e p.1) p.2 := by
      simp only [empiricalLoss]
      exact (Finset.measurable_sum Finset.univ fun j _ =>
        hloss.comp ((he.comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd))).div_const _
    exact hemp.sub ((hpop.comp he).comp measurable_fst)
  have hBadEq :
      {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (↑(env p.1) : Set ι)
          (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ) Δ}
        = ⋃ τ : Transcript,
            ({p : Ωtrain × (Fin n → Z) | Δ <
                |empiricalLoss loss (g p.1 τ 0) p.2 - populationLoss Q loss (g p.1 τ 0)|} ∪
             {p : Ωtrain × (Fin n → Z) | Δ <
                |empiricalLoss loss (g p.1 τ T) p.2 - populationLoss Q loss (g p.1 τ T)|}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union]
    constructor
    · intro hp
      by_contra hcon
      push Not at hcon
      refine hp fun θ hθ => ?_
      obtain ⟨τ, hτ⟩ := hsplit p.1 θ (Finset.mem_coe.1 hθ)
      rcases hτ with rfl | rfl
      · exact (hcon τ).1
      · exact (hcon τ).2
    · rintro ⟨τ, h | h⟩ hUD
      · exact absurd (hUD _ (Finset.mem_coe.2 (hmem0 p.1 τ))) (not_le.2 h)
      · exact absurd (hUD _ (Finset.mem_coe.2 (hmemT p.1 τ))) (not_le.2 h)
  have hBad : MeasurableSet
      {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (↑(env p.1) : Set ι)
        (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ) Δ} := by
    rw [hBadEq]
    refine MeasurableSet.iUnion fun τ => MeasurableSet.union ?_ ?_
    · exact measurableSet_lt measurable_const (hcent _ (hg0 τ)).abs
    · exact measurableSet_lt measurable_const (hcent _ (hgT τ)).abs
  have hfiber : ∀ᵐ t ∂μtrain,
      (Kernel.const Ωtrain (Measure.pi fun _ : Fin n => Q)) t
        (Prod.mk t ⁻¹' {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (↑(env p.1) : Set ι)
          (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ) Δ})
        ≤ ENNReal.ofReal δ := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Kernel.const_apply]
    have hpre : (Prod.mk t ⁻¹' {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (↑(env p.1) : Set ι)
          (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ) Δ})
        = {panel : Fin n → Z | ¬ UniformDev (↑(env t) : Set ι)
            (fun θ => empiricalLoss loss θ panel) (fun θ => populationLoss Q loss θ) Δ} := rfl
    rw [hpre, hΔ]
    refine finiteEnvelope_badEvent_le Q n hn hab hδ0 hδ1 loss (env t)
      ⟨g t (Classical.arbitrary Transcript) 0, hmem0 t _⟩ (hcard t)
      (fun θ _ => hloss.comp (measurable_const.prodMk measurable_id)) ?_
    intro θ hθ
    obtain ⟨τ, hτ⟩ := hsplit t θ hθ
    rcases hτ with rfl | rfl
    · exact hb0 t τ
    · exact hbT t τ
  calc
    (μtrain.compProd (Kernel.const Ωtrain (Measure.pi fun _ : Fin n => Q)))
        {p : Ωtrain × (Fin n → Z) |
          cumCP (fun θ => empiricalLoss loss θ p.2) (g p.1 (disclose p.1 p.2)) T >
            cumCP (fun θ => populationLoss Q loss θ) (g p.1 (disclose p.1 p.2)) T + 2 * Δ}
        ≤ (μtrain.compProd (Kernel.const Ωtrain (Measure.pi fun _ : Fin n => Q)))
            {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (↑(env p.1) : Set ι)
              (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ) Δ} := by
          refine measure_mono fun p hp => ?_
          simp only [Set.mem_setOf_eq] at hp ⊢
          intro hUD
          exact (not_lt_of_ge (finite_audit_goodhart_twoPoint hUD
            (Finset.mem_coe.2 (hmem0 p.1 (disclose p.1 p.2)))
            (Finset.mem_coe.2 (hmemT p.1 (disclose p.1 p.2))))) hp
    _ ≤ ENNReal.ofReal δ := by
        have h := compProd_badEvent_le_mul μtrain
          (Kernel.const Ωtrain (Measure.pi fun _ : Fin n => Q))
          {p : Ωtrain × (Fin n → Z) | ¬ UniformDev (↑(env p.1) : Set ι)
            (fun θ => empiricalLoss loss θ p.2) (fun θ => populationLoss Q loss θ) Δ}
          hBad (ENNReal.ofReal δ) hfiber
        simpa [IsProbabilityMeasure.measure_univ] using h

section SelfMod
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Nonempty S] in
/-- `(spec.update q y) i = if i = sa_to_fin y.1 then spec.r y.1 +
spec.γ * QLearningSpec.maxₐ q y.2.1 - q (sa_to_fin y.1) else 0`. -/
theorem update_apply (spec : QLearningSpec (S := S) (A := A))
    (q : E (Fintype.card (S × A))) (y : (S × A) × S × A) (i : Fin (Fintype.card (S × A))) :
    (spec.update q y) i
      = if i = sa_to_fin y.1 then
          spec.r y.1 + spec.γ * QLearningSpec.maxₐ q y.2.1 - q (sa_to_fin y.1) else 0 := by
  simp [QLearningSpec.update, QLearningSpec.x, mul_ite]

omit [Nonempty S] in
/-- If `q` satisfies `QLearningIterates spec q`, the initial iterate `spec.q₀ ∈ qBall B`, the
budget `B` is closed under the Bellman target (`|spec.r sa| + spec.γ * B ≤ B`), and every step
size `spec.α k ∈ [0, 1]`, then `Admissible (fun k => q k ω) (qBall B)` for every sample path
`ω`. -/
theorem qBall_invariant_of_stepSize_mem_Icc
    (spec : QLearningSpec (S := S) (A := A)) {B : ℝ}
    {q : ℕ → (ℕ → (S × A) × S × A) → E (Fintype.card (S × A))}
    (hq : QLearningIterates (spec := spec) (q := q))
    (hq₀ : spec.q₀ ∈ qBall (S := S) (A := A) B)
    (hB : ∀ sa : S × A, |spec.r sa| + spec.γ * B ≤ B)
    (hα : ∀ k, spec.α k ∈ Set.Icc (0 : ℝ) 1)
    (ω : ℕ → (S × A) × S × A) :
    Admissible (fun k => q k ω) (qBall (S := S) (A := A) B) := by
  have hγ : 0 ≤ spec.γ := spec.hγ.1
  intro k
  induction k with
  | zero =>
    show q 0 ω ∈ qBall B
    rw [hq.init]; exact hq₀
  | succ k ih =>
    show q (k + 1) ω ∈ qBall B
    intro i
    obtain ⟨hα0, hα1⟩ := hα k
    rw [hq.step k ω, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, update_apply]
    by_cases hi : i = sa_to_fin (ω (k + 1)).1
    · subst hi
      rw [if_pos rfl]
      have hgm : |spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1| ≤ spec.γ * B := by
        rw [abs_mul, abs_of_nonneg hγ]
        exact mul_le_mul_of_nonneg_left (abs_max_a_le_of_mem_qBall ih _) hγ
      have htgt : |spec.r (ω (k + 1)).1
          + spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1| ≤ B := by
        have htri := abs_add_le (spec.r (ω (k + 1)).1)
          (spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1)
        linarith [hB (ω (k + 1)).1]
      have hconv : q k ω (sa_to_fin (ω (k + 1)).1)
          + spec.α k * (spec.r (ω (k + 1)).1
              + spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1
              - q k ω (sa_to_fin (ω (k + 1)).1))
          = (1 - spec.α k) * q k ω (sa_to_fin (ω (k + 1)).1)
            + spec.α k * (spec.r (ω (k + 1)).1
                + spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1) := by ring
      rw [hconv, abs_le]
      have h1 := abs_le.1 (ih (sa_to_fin (ω (k + 1)).1))
      have h2 := abs_le.1 htgt
      have hA : 0 ≤ (1 - spec.α k) * (B - q k ω (sa_to_fin (ω (k + 1)).1)) :=
        mul_nonneg (by linarith) (by linarith [h1.2])
      have hC : 0 ≤ (1 - spec.α k) * (q k ω (sa_to_fin (ω (k + 1)).1) + B) :=
        mul_nonneg (by linarith) (by linarith [h1.1])
      have hD : 0 ≤ spec.α k * (B - (spec.r (ω (k + 1)).1
          + spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1)) :=
        mul_nonneg hα0 (by linarith [h2.2])
      have hEe : 0 ≤ spec.α k * ((spec.r (ω (k + 1)).1
          + spec.γ * QLearningSpec.maxₐ (q k ω) (ω (k + 1)).2.1) + B) :=
        mul_nonneg hα0 (by linarith [h2.1])
      constructor <;> nlinarith
    · rw [if_neg hi, mul_zero, add_zero]
      exact ih i

omit [Nonempty S] [Nonempty A] in
/-- If `|spec.r sa| ≤ Rmax` for every `sa` and `Rmax / (1 - spec.γ) ≤ B`, then
`|spec.r sa| + spec.γ * B ≤ B`. -/
theorem qBall_budget_of_reward_cap (spec : QLearningSpec (S := S) (A := A))
    {Rmax B : ℝ} (hR : ∀ sa : S × A, |spec.r sa| ≤ Rmax)
    (hBB : Rmax / (1 - spec.γ) ≤ B) (sa : S × A) :
    |spec.r sa| + spec.γ * B ≤ B := by
  have hone : (0 : ℝ) < 1 - spec.γ := by linarith [spec.hγ.2]
  have hmul : Rmax ≤ B * (1 - spec.γ) := (div_le_iff₀ hone).1 hBB
  nlinarith [hR sa]

/-! ### The crossover: the agent rewrites its own dynamics on the audit outcome -/

omit [Nonempty S] in
/-- If, for every training/audit outcome `(t, o)`, `q t o` satisfies `QLearningIterates (spec t o)`
with initial iterate in `qBall B`, budget `B` closed under the Bellman target, and step sizes in
`[0, 1]`, and the uniform-deviation failure event on `qBall B` is measurable with kernel fiber at
most `δ` for `μtrain`-almost every training outcome, then measured cumulative compression progress
along the audit-rewritten Q-learning path exceeds population progress by more than `2Δ` with
probability at most `δ` under `μtrain.compProd κ`, at every horizon `T`. -/
theorem selfModifying_qlearning_audit_goodhart
    {Ωtrain Ωaudit : Type*} [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (spec : Ωtrain → Ωaudit → QLearningSpec (S := S) (A := A)) {B : ℝ}
    (q : Ωtrain → Ωaudit → ℕ → (ℕ → (S × A) × S × A) → E (Fintype.card (S × A)))
    (hq : ∀ t o, QLearningIterates (spec := spec t o) (q := q t o))
    (hq₀ : ∀ t o, (spec t o).q₀ ∈ qBall (S := S) (A := A) B)
    (hB : ∀ t o (sa : S × A), |(spec t o).r sa| + (spec t o).γ * B ≤ B)
    (hα : ∀ t o k, (spec t o).α k ∈ Set.Icc (0 : ℝ) 1)
    (path : Ωtrain → Ωaudit → ℕ → (S × A) × S × A)
    (Ehat : Ωtrain → Ωaudit → E (Fintype.card (S × A)) → ℝ)
    (Epop : Ωtrain → E (Fintype.card (S × A)) → ℝ) (Δ : ℝ) (δ : ENNReal)
    (hBad : MeasurableSet {p : Ωtrain × Ωaudit |
      ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat p.1 p.2) (Epop p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {o | ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat t o) (Epop t) Δ} ≤ δ)
    (T : ℕ) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.1 p.2) (fun k => q p.1 p.2 k (path p.1 p.2)) T >
          cumCP (Epop p.1) (fun k => q p.1 p.2 k (path p.1 p.2)) T + 2 * Δ} ≤ δ :=
  kernel_adaptiveTrajectory_goodhart μtrain κ (fun _ => qBall (S := S) (A := A) B)
    (fun t o k => q t o k (path t o)) Ehat Epop Δ δ
    (fun t o => qBall_invariant_of_stepSize_mem_Icc (spec t o) (hq t o) (hq₀ t o)
      (hB t o) (hα t o) (path t o))
    hBad hfiber T

omit [Nonempty S] in
/-- Under the hypotheses of `selfModifying_qlearning_audit_goodhart` but without the
budget-closure or step-size constraints, if instead the initial iterate lies in `qBall B` and the
terminal iterate `q t o T (path t o) ∈ qBall B` for every training/audit outcome `(t, o)`, the same
conclusion holds. -/
theorem selfModifying_qlearning_audit_goodhart_twoPoint
    {Ωtrain Ωaudit : Type*} [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (spec : Ωtrain → Ωaudit → QLearningSpec (S := S) (A := A)) {B : ℝ}
    (q : Ωtrain → Ωaudit → ℕ → (ℕ → (S × A) × S × A) → E (Fintype.card (S × A)))
    (hq : ∀ t o, QLearningIterates (spec := spec t o) (q := q t o))
    (hq₀ : ∀ t o, (spec t o).q₀ ∈ qBall (S := S) (A := A) B)
    (path : Ωtrain → Ωaudit → ℕ → (S × A) × S × A)
    (Ehat : Ωtrain → Ωaudit → E (Fintype.card (S × A)) → ℝ)
    (Epop : Ωtrain → E (Fintype.card (S × A)) → ℝ) (Δ : ℝ) (δ : ENNReal)
    (hBad : MeasurableSet {p : Ωtrain × Ωaudit |
      ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat p.1 p.2) (Epop p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {o | ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat t o) (Epop t) Δ} ≤ δ)
    (T : ℕ) (hterminal : ∀ t o, q t o T (path t o) ∈ qBall (S := S) (A := A) B) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.1 p.2) (fun k => q p.1 p.2 k (path p.1 p.2)) T >
          cumCP (Epop p.1) (fun k => q p.1 p.2 k (path p.1 p.2)) T + 2 * Δ} ≤ δ := by
  calc
    (μtrain.compProd κ)
        {p : Ωtrain × Ωaudit |
          cumCP (Ehat p.1 p.2) (fun k => q p.1 p.2 k (path p.1 p.2)) T >
            cumCP (Epop p.1) (fun k => q p.1 p.2 k (path p.1 p.2)) T + 2 * Δ}
        ≤ (μtrain.compProd κ) {p : Ωtrain × Ωaudit |
            ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat p.1 p.2) (Epop p.1) Δ} := by
          refine measure_mono fun p hp => ?_
          simp only [Set.mem_setOf_eq] at hp ⊢
          intro hUD
          refine (not_lt_of_ge (finite_audit_goodhart_twoPoint hUD ?_ (hterminal p.1 p.2))) hp
          show q p.1 p.2 0 (path p.1 p.2) ∈ qBall (S := S) (A := A) B
          rw [(hq p.1 p.2).init]
          exact hq₀ p.1 p.2
    _ ≤ δ := by
        have h := compProd_badEvent_le_mul μtrain κ
          {p : Ωtrain × Ωaudit |
            ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat p.1 p.2) (Epop p.1) Δ}
          hBad δ hfiber
        simpa [IsProbabilityMeasure.measure_univ] using h

omit [Nonempty S] in
/-- If the transcript alphabet has a `bits`-bit disclosure budget, every `(t, τ)` generates
Q-learning iterates satisfying `QLearningIterates` with initial iterate in `qBall B`, budget `B`
closed under the Bellman target, and step sizes in `[0, 1]`, `loss` is measurable and a.e. valued
in `[a, b]` on `qBall B`, and the two audited endpoints are measurable in the training coordinate,
then on an i.i.d. panel of size `n`, for any disclosure map, measured cumulative compression
progress along the disclosed self-modifying Q-learning path exceeds population progress by more
than `2 · deltaFiniteExperts (2 · 2^bits) n (b - a) δ` with probability at most
`ENNReal.ofReal δ` (dwork2015adaptive). -/
theorem selfModifying_qlearning_audit_goodhart_bitPriced
    {Ωtrain Transcript Z : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Z]
    [Fintype Transcript] [Nonempty Transcript]
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (bits n : ℕ) (hbudget : HasDisclosureBudget Transcript bits) (hn : 0 < n)
    (spec : Ωtrain → Transcript → QLearningSpec (S := S) (A := A)) {B : ℝ}
    (q : Ωtrain → Transcript → ℕ → (ℕ → (S × A) × S × A) → E (Fintype.card (S × A)))
    (hq : ∀ t τ, QLearningIterates (spec := spec t τ) (q := q t τ))
    (hq₀ : ∀ t τ, (spec t τ).q₀ ∈ qBall (S := S) (A := A) B)
    (hB : ∀ t τ (sa : S × A), |(spec t τ).r sa| + (spec t τ).γ * B ≤ B)
    (hα : ∀ t τ k, (spec t τ).α k ∈ Set.Icc (0 : ℝ) 1)
    (path : Ωtrain → Transcript → ℕ → (S × A) × S × A)
    (loss : E (Fintype.card (S × A)) → Z → ℝ) (hloss : Measurable (Function.uncurry loss))
    {a b : ℝ} (hab : a < b)
    (hrange : ∀ θ ∈ qBall (S := S) (A := A) B, ∀ᵐ z ∂Q, loss θ z ∈ Set.Icc a b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (T : ℕ)
    (hmeas0 : ∀ τ, Measurable fun t => q t τ 0 (path t τ))
    (hmeasT : ∀ τ, Measurable fun t => q t τ T (path t τ))
    (disclose : Ωtrain → (Fin n → Z) → Transcript) :
    (μtrain.compProd (Kernel.const Ωtrain (Measure.pi fun _ : Fin n => Q)))
        {p : Ωtrain × (Fin n → Z) |
          cumCP (fun θ => empiricalLoss loss θ p.2)
              (fun k => q p.1 (disclose p.1 p.2) k (path p.1 (disclose p.1 p.2))) T >
            cumCP (fun θ => populationLoss Q loss θ)
                (fun k => q p.1 (disclose p.1 p.2) k (path p.1 (disclose p.1 p.2))) T
              + 2 * deltaFiniteExperts (2 * 2 ^ bits) n (b - a) δ}
      ≤ ENNReal.ofReal δ := by
  have hball : ∀ t τ k, q t τ k (path t τ) ∈ qBall (S := S) (A := A) B := fun t τ =>
    qBall_invariant_of_stepSize_mem_Icc (spec t τ) (hq t τ) (hq₀ t τ) (hB t τ) (hα t τ) (path t τ)
  exact transcriptEndpoints_bitPriced_goodhart μtrain Q bits n hbudget hn hab hδ0 hδ1
    loss hloss (fun t τ k => q t τ k (path t τ)) T hmeas0 hmeasT
    (fun t τ => hrange _ (hball t τ 0)) (fun t τ => hrange _ (hball t τ T)) disclose

omit [Nonempty S] in
/-- If `W` is a fixed finite MDP with reward bounded by `Rmax`, `Rmax / (1 - W.γ) ≤ B`,
`q₀ ∈ qBall B`, every step size `alpha t o k ∈ [0, 1]`, and `q t o` satisfies `QLearningIterates`
for the spec built from `W`, `alpha t o`, and `q₀`, with the uniform-deviation failure event on
`qBall B` measurable and kernel-fiber-bounded by `δ`, then measured cumulative compression
progress along the run exceeds population progress by more than `2Δ` with probability at most `δ`
under `μtrain.compProd κ`, at every horizon `T`. -/
theorem selfModifying_stepSize_audit_goodhart_fixedWorld
    {Ωtrain Ωaudit : Type*} [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (W : FiniteMDP (S := S) (A := A)) {Rmax B : ℝ}
    (hR : ∀ sa : S × A, |W.r sa| ≤ Rmax) (hBB : Rmax / (1 - W.γ) ≤ B)
    (q₀ : E (Fintype.card (S × A))) (hq₀ : q₀ ∈ qBall (S := S) (A := A) B)
    (alpha : Ωtrain → Ωaudit → ℕ → ℝ) (hα : ∀ t o k, alpha t o k ∈ Set.Icc (0 : ℝ) 1)
    (q : Ωtrain → Ωaudit → ℕ → (ℕ → (S × A) × S × A) → E (Fintype.card (S × A)))
    (hq : ∀ t o, QLearningIterates
      (spec := { toFiniteMDP := W, α := alpha t o, q₀ := q₀ }) (q := q t o))
    (path : Ωtrain → Ωaudit → ℕ → (S × A) × S × A)
    (Ehat : Ωtrain → Ωaudit → E (Fintype.card (S × A)) → ℝ)
    (Epop : Ωtrain → E (Fintype.card (S × A)) → ℝ) (Δ : ℝ) (δ : ENNReal)
    (hBad : MeasurableSet {p : Ωtrain × Ωaudit |
      ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat p.1 p.2) (Epop p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {o | ¬ UniformDev (qBall (S := S) (A := A) B) (Ehat t o) (Epop t) Δ} ≤ δ)
    (T : ℕ) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.1 p.2) (fun k => q p.1 p.2 k (path p.1 p.2)) T >
          cumCP (Epop p.1) (fun k => q p.1 p.2 k (path p.1 p.2)) T + 2 * Δ} ≤ δ :=
  selfModifying_qlearning_audit_goodhart μtrain κ
    (fun t o => { toFiniteMDP := W, α := alpha t o, q₀ := q₀ }) q hq (fun _ _ => hq₀)
    (fun t o sa => qBall_budget_of_reward_cap
      { toFiniteMDP := W, α := alpha t o, q₀ := q₀ } hR hBB sa)
    hα path Ehat Epop Δ δ hBad hfiber T

end SelfMod

end AuditCPRL
