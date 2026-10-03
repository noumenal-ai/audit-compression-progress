import AuditCPRL.Convergence
import AuditCP.FiniteBlackwell
import AuditCP.EntropyFloor

/-!
# Target 3 — the reachable envelope of a learner

Every `AuditCP` theorem takes the audited class as given.  For a learner the class is the set its
own iterates reach, and this module settles what the two corpora do and do not supply for it.

## Admissibility is free; a declarable, priceable envelope is not

`AuditCP.Admissible` holds for any superset of the path's range, so it is never the obstruction.
Two things are, and they are different:

* **Declarability.**  Convergence delivers a ball containing the whole run, but the radius is
  chosen inside the almost-sure binder, so it is a function of the sample path.  An auditor fixing
  a class before drawing a panel cannot use it.  `StochasticApproximation.IteratesOfResidual.bdd`
  does deliver a path-uniform radius, but one per index, so what it declares is an envelope per
  horizon, not per run.  A run-uniform predeclared ball is exactly what neither corpus has; it is
  carried below as a named hypothesis, and it points RL → AuditCP, so it is a residual of this
  crossover and not part of it.
* **Priceability.**  Even granted the ball, no in-scope route gives it a radius:
  `AuditCP.deltaFiniteExperts` and the concentration results behind it are indexed by a finite
  candidate type, and the joint-measurability routes need a countable one.  `RLTheory.E d` is
  neither for `d ≥ 1`.  So the composition of the audit with a trajectory-indexed class is sound
  and has no defined resolution.

## The asymmetry, and the repair

The obstruction is on the measurement, not on the learner.
`AuditCP.condEntropy_le_condCrossEntropy` constrains the candidate type not at all, so the *true*
compression progress of the entire run is budgeted by a constant fixed at initialisation, with no
class, no concentration and no horizon term.  What a learner can do is not mine unbounded genuine
progress; it is run a trajectory whose measured progress admits no positive lower bound on improvement at the
resolution of the trajectory.

The repair changes what is reported, not how it is bounded: audit two **declared checkpoints**
instead of the path.  The audited class then has two elements, and
`AuditCP.kernel_endpointPair_goodhart` applies on the training ⊗ audit product with radius
`AuditCP.deltaFiniteExperts 2 n (b - a) δ = (b - a) * √(log (4 / δ) / (2 * n))`.  Every premise of
that theorem which is about the learner is discharged here:

* the endpoints lie in the class they generate;
* the deviation-failure event is jointly measurable — a two-element class needs no countability, and
  the checkpoints are measurable functions of the training path because
  `StochasticApproximation.IteratesOfResidual.adaptedOnSamplePath` factors each iterate through
  finitely many samples;
* the audit reads the audit coordinate only and the learner reads the training coordinate only,
  which in both cases is forced by the carrier types rather than assumed.

Only the concentration premise is audit-side, and `AuditCPRL.twoPoint_badEvent_le` discharges it
from `AuditCP.finite_experts_iid_badEvent_le` at a two-element family.  The resulting radius carries
panel size, loss range and confidence, and no term in the number of updates, the horizon, or the
separation of the checkpoints.

## Named, not fabricated

Two hypotheses are named and neither is discharged: the run-uniform predeclared radius, and a
uniform-deviation radius on a ball.  A third, audit-side regularity of the loss, is named where the
audit functions are abstract and discharged where they are instantiated.
-/

namespace AuditCPRL

open AuditCP RLTheory StochasticApproximation ReinforcementLearning MeasureTheory Filter
open ProbabilityTheory

universe u

/-! ### Ingredient.  No RL binder occurs, so this is **not** a crossover. -/

/-- If `Set.range g ⊆ Fenv`, then `Admissible g Fenv`. -/
theorem admissible_of_range_subset {ι : Type*} {g : ℕ → ι} {Fenv : Set ι}
    (h : Set.range g ⊆ Fenv) : Admissible g Fenv :=
  fun t => h (Set.mem_range_self t)

/-! ### What RLTheory does supply. -/

section Supplied

variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {d : ℕ}
variable {Fres : E d → (S × S) → E d} {f : E d → E d} {fixedPoint x₀ : E d}
variable {x : ℕ → (ℕ → S × S) → E d} {α : ℕ → ℝ} {mrp : FiniteMRP (S := S)}

/-- Under the hypotheses of stochastic-approximation convergence (`IteratesOfResidual`, a
measurable Lipschitz residual, the fixed-point and expectation equations, Robbins–Monro step
sizes, and a Lyapunov function), almost surely there exists `C` with
`Admissible (fun n => x n ω) (Metric.closedBall 0 C)`. -/
theorem iteratesOfResidual_ae_admissible_closedBall
    (hx : IteratesOfResidual x x₀ α Fres)
    (hFm : Measurable Fres.uncurry)
    (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖Fres w y - Fres w' y‖ ≤ C * ‖w - w'‖)
    (hf : fixedPoint = f fixedPoint)
    (hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • Fres w (s, s'))
    (hα : RobbinsMonro α)
    {φ : E d → ℝ} {φ' : E d → E d} (hφm : Measurable φ) (hgradφm : Measurable φ')
    [LyapunovFunction φ φ' f] :
    ∀ᵐ ω ∂ mrp.iid_samples,
      ∃ C : ℝ, Admissible (fun n => x n ω) (Metric.closedBall (0 : E d) C) := by
  filter_upwards [ae_tendsto_of_iterates_iid_samples hx hFm hFlip hf hfF hα hφm hgradφm] with ω hω
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hω).subset_closedBall (0 : E d)
  exact ⟨C, admissible_of_range_subset hC⟩

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres` with a Lipschitz residual, then for every
horizon `T` there is `C ≥ 0` such that `UniformDev (Metric.closedBall 0 C) Ehat Etrue Δ` gives
`cumCP Ehat (fun n => x n ω) T ≤ cumCP Etrue (fun n => x n ω) T + 2Δ` for every sample path `ω`. -/
theorem iteratesOfResidual_goodhart_horizonIndexed
    (hx : IteratesOfResidual x x₀ α Fres)
    (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖Fres w y - Fres w' y‖ ≤ C * ‖w - w'‖) (T : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ehat Etrue : E d → ℝ) (Δ : ℝ),
      UniformDev (Metric.closedBall (0 : E d) C) Ehat Etrue Δ →
      ∀ ω, cumCP Ehat (fun n => x n ω) T ≤ cumCP Etrue (fun n => x n ω) T + 2 * Δ := by
  obtain ⟨C, hC0, hC⟩ := hx.bdd hFlip T
  refine ⟨max ‖x₀‖ C, le_trans (norm_nonneg x₀) (le_max_left _ _), fun Ehat Etrue Δ hUD ω => ?_⟩
  refine finite_audit_goodhart_twoPoint (g := fun n => x n ω) (T := T) hUD ?_ ?_
  · exact mem_closedBall_zero_iff.2 (by rw [hx.init ω]; exact le_max_left _ _)
  · exact mem_closedBall_zero_iff.2 ((hC ω).trans (le_max_right _ _))

end Supplied

/-! ### What neither library supplies: the two hypotheses are named, not fabricated. -/

/-- If almost every sample path stays in the closed ball of radius `C` and `UniformDev` holds at
radius `Δ` on that ball, then almost surely `cumCP Ehat (fun n => x n ω) T ≤
cumCP Etrue (fun n => x n ω) T + 2Δ` at every horizon `T`. -/
theorem goodhart_of_uniform_envelope {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x : ℕ → Ω → E d} {C : ℝ} (hunif : ∀ᵐ ω ∂μ, ∀ n, ‖x n ω‖ ≤ C)
    {Ehat Etrue : E d → ℝ} {Δ : ℝ}
    (hUD : UniformDev (Metric.closedBall (0 : E d) C) Ehat Etrue Δ) :
    ∀ᵐ ω ∂μ, ∀ T, cumCP Ehat (fun n => x n ω) T ≤ cumCP Etrue (fun n => x n ω) T + 2 * Δ := by
  filter_upwards [hunif] with ω hω T
  exact finite_audit_goodhart_twoPoint (g := fun n => x n ω) (T := T) hUD
    (mem_closedBall_zero_iff.2 (hω 0)) (mem_closedBall_zero_iff.2 (hω T))

/-! ### The repair: audit declared checkpoints, not the trajectory. -/

section Checkpoints

variable {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable {d : ℕ}
variable {Fres : E d → (S × S) → E d} {x₀ : E d}
variable {x : ℕ → (ℕ → S × S) → E d} {α : ℕ → ℝ}

omit [Nonempty S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres`, then `x n` is measurable. -/
theorem measurable_iterate (hx : IteratesOfResidual x x₀ α Fres) (n : ℕ) :
    Measurable (x n) := by
  obtain ⟨xn, hxn, heq⟩ := (hx.adaptedOnSamplePath).property n
  have hfun : x n = xn ∘ (Preorder.frestrictLe n) := funext heq
  rw [hfun]
  exact hxn.comp (Preorder.measurable_frestrictLe n)

/-- If `loss θ₀` and `loss θ₁` are measurable and a.e. valued in `[a, b]` under `Q`, then on an
i.i.d. panel of size `n`, the probability that `{θ₀, θ₁}` fails uniform deviation at radius
`deltaFiniteExperts 2 n (b - a) δ` is at most `ENNReal.ofReal δ`. -/
theorem twoPoint_badEvent_le {Z ι : Type*} [MeasurableSpace Z]
    (Q : Measure Z) [IsProbabilityMeasure Q] (n : ℕ) (hn : 0 < n)
    {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ) (θ₀ θ₁ : ι)
    (hm₀ : Measurable (loss θ₀)) (hm₁ : Measurable (loss θ₁))
    (hb₀ : ∀ᵐ z ∂Q, loss θ₀ z ∈ Set.Icc a b) (hb₁ : ∀ᵐ z ∂Q, loss θ₁ z ∈ Set.Icc a b) :
    Measure.pi (fun _ : Fin n => Q)
        {panel | ¬ UniformDev ({θ₀, θ₁} : Set ι)
          (fun θ => empiricalLoss loss θ panel) (fun θ => populationLoss Q loss θ)
          (deltaFiniteExperts 2 n (b - a) δ)}
      ≤ ENNReal.ofReal δ := by
  classical
  have key := finite_experts_iid_badEvent_le (ι := Fin 2) Q n hn a b hab δ hδ0 hδ1
    ![loss θ₀, loss θ₁] (fun i => by fin_cases i <;> simpa)
    (fun i => by fin_cases i; · simpa using hb₀
                 · simpa using hb₁)
  rw [Fintype.card_fin] at key
  refine le_trans (measure_mono ?_) key
  intro panel hpanel
  simp only [Set.mem_setOf_eq] at hpanel ⊢
  intro hUD
  refine hpanel fun θ hθ => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl
  · simpa [empiricalLoss, populationLoss] using hUD 0 (Set.mem_univ 0)
  · simpa [empiricalLoss, populationLoss] using hUD 1 (Set.mem_univ 1)

omit [Nonempty S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres`, `Ehat` and `Etrue` are measurable, and the
uniform-deviation failure event on the checkpoint pair `{x t₀ t, x tT t}` has kernel fiber at most
`δ` for `μtrain`-almost every training path, then the signed checkpoint report exceeds its
population value by more than `2Δ` with probability at most `δ` under `μtrain.compProd κ`. -/
theorem checkpointed_iterates_goodhart
    (hx : IteratesOfResidual x x₀ α Fres) (t₀ tT : ℕ)
    {Ωaudit : Type*} [MeasurableSpace Ωaudit]
    (μtrain : Measure (ℕ → S × S)) [IsProbabilityMeasure μtrain]
    (κ : Kernel (ℕ → S × S) Ωaudit) [IsMarkovKernel κ]
    {Ehat : Ωaudit → E d → ℝ} {Etrue : E d → ℝ} {Δ : ℝ} {δ : ENNReal}
    (hEhat : Measurable (Function.uncurry Ehat)) (hEtrue : Measurable Etrue)
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {a | ¬ UniformDev ({x t₀ t, x tT t} : Set (E d)) (Ehat a) Etrue Δ} ≤ δ) :
    (μtrain.compProd κ)
        {p : (ℕ → S × S) × Ωaudit |
          Ehat p.2 (x t₀ p.1) - Ehat p.2 (x tT p.1)
            > Etrue (x t₀ p.1) - Etrue (x tT p.1) + 2 * Δ} ≤ δ := by
  have hm0 : Measurable (x t₀) := measurable_iterate hx t₀
  have hmT : Measurable (x tT) := measurable_iterate hx tT
  have hg0 : Measurable fun p : (ℕ → S × S) × Ωaudit =>
      Ehat p.2 (x t₀ p.1) - Etrue (x t₀ p.1) :=
    (hEhat.comp (measurable_snd.prodMk (hm0.comp measurable_fst))).sub
      (hEtrue.comp (hm0.comp measurable_fst))
  have hgT : Measurable fun p : (ℕ → S × S) × Ωaudit =>
      Ehat p.2 (x tT p.1) - Etrue (x tT p.1) :=
    (hEhat.comp (measurable_snd.prodMk (hmT.comp measurable_fst))).sub
      (hEtrue.comp (hmT.comp measurable_fst))
  have hset : {p : (ℕ → S × S) × Ωaudit |
        UniformDev ({x t₀ p.1, x tT p.1} : Set (E d)) (Ehat p.2) Etrue Δ}
      = {p : (ℕ → S × S) × Ωaudit | |Ehat p.2 (x t₀ p.1) - Etrue (x t₀ p.1)| ≤ Δ}
        ∩ {p : (ℕ → S × S) × Ωaudit | |Ehat p.2 (x tT p.1) - Etrue (x tT p.1)| ≤ Δ} := by
    ext p
    constructor
    · intro h
      exact ⟨h _ (Set.mem_insert _ _), h _ (Set.mem_insert_of_mem _ rfl)⟩
    · rintro ⟨h0, hT⟩ θ hθ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
      rcases hθ with rfl | rfl
      exacts [h0, hT]
  have hGood : MeasurableSet {p : (ℕ → S × S) × Ωaudit |
      UniformDev ({x t₀ p.1, x tT p.1} : Set (E d)) (Ehat p.2) Etrue Δ} := by
    rw [hset]
    exact (measurableSet_le hg0.abs measurable_const).inter
      (measurableSet_le hgT.abs measurable_const)
  exact kernel_endpointPair_goodhart μtrain κ
    (fun t => ({x t₀ t, x tT t} : Set (E d))) (fun t => (x t₀ t, x tT t))
    (fun _ a => Ehat a) (fun _ => Etrue) Δ δ
    (fun t => ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ rfl⟩) hGood.compl hfiber

omit [Nonempty S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres` and `loss` is measurable and a.e. valued in
`[a, b]` under `Q`, then on an i.i.d. panel of size `n`, the empirical drop in loss between
checkpoints `x t₀` and `x tT` exceeds the population drop by more than
`2 · deltaFiniteExperts 2 n (b - a) δ` with probability at most `ENNReal.ofReal δ`. -/
theorem checkpointed_iterates_goodhart_iidPanel
    (hx : IteratesOfResidual x x₀ α Fres) (t₀ tT : ℕ)
    (μtrain : Measure (ℕ → S × S)) [IsProbabilityMeasure μtrain]
    {Z : Type*} [MeasurableSpace Z] (Q : Measure Z) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 0 < n) {a b : ℝ} (hab : a < b) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : E d → Z → ℝ) (hloss : Measurable (Function.uncurry loss))
    (hbdd : ∀ θ, ∀ᵐ z ∂Q, loss θ z ∈ Set.Icc a b) :
    (μtrain.compProd (Kernel.const _ (Measure.pi (fun _ : Fin n => Q))))
        {p : (ℕ → S × S) × (Fin n → Z) |
          empiricalLoss loss (x t₀ p.1) p.2 - empiricalLoss loss (x tT p.1) p.2
            > populationLoss Q loss (x t₀ p.1) - populationLoss Q loss (x tT p.1)
              + 2 * deltaFiniteExperts 2 n (b - a) δ}
      ≤ ENNReal.ofReal δ := by
  have hEhat : Measurable (Function.uncurry fun (panel : Fin n → Z) (θ : E d) =>
      empiricalLoss loss θ panel) := by
    simp only [empiricalLoss]
    exact (Finset.measurable_sum Finset.univ fun j _ =>
      hloss.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))).div_const _
  have hEtrue : Measurable fun θ : E d => populationLoss Q loss θ := by
    have h := (hloss.stronglyMeasurable).integral_kernel_prod_right'
      (κ := Kernel.const (E d) Q)
    simp only [Kernel.const_apply] at h
    simpa only [populationLoss, Function.uncurry_apply_pair] using h.measurable
  have hfiber : ∀ᵐ t ∂μtrain,
      (Kernel.const (ℕ → S × S) (Measure.pi (fun _ : Fin n => Q))) t
          {panel | ¬ UniformDev ({x t₀ t, x tT t} : Set (E d))
            ((fun (panel : Fin n → Z) (θ : E d) => empiricalLoss loss θ panel) panel)
            (fun θ => populationLoss Q loss θ) (deltaFiniteExperts 2 n (b - a) δ)}
        ≤ ENNReal.ofReal δ := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Kernel.const_apply]
    exact twoPoint_badEvent_le Q n hn hab hδ0 hδ1 loss (x t₀ t) (x tT t)
      (hloss.comp (measurable_const.prodMk measurable_id))
      (hloss.comp (measurable_const.prodMk measurable_id))
      (hbdd (x t₀ t)) (hbdd (x tT t))
  exact checkpointed_iterates_goodhart hx t₀ tT μtrain
    (Kernel.const _ (Measure.pi (fun _ : Fin n => Q))) hEhat hEtrue hfiber

end Checkpoints

/-! ### The asymmetry: the kill is on the measurement, not on the learner. -/

section TrueProgress

variable {S : Type u} {d : ℕ}
variable {Fres : E d → (S × S) → E d} {x₀ : E d}
variable {x : ℕ → (ℕ → S × S) → E d} {α : ℕ → ℝ}

/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres` and every `P θ ξ` has positive prior, then
`cumCP (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) (fun n => x n ω) T ≤
condCrossEntropyFinitePMF μ Q (P x₀) - condEntropyFinitePMF μ Q`. -/
theorem iteratesOfResidual_condCrossEntropy_budget
    {X H : Type*} [Fintype X] [Fintype H]
    (hx : IteratesOfResidual x x₀ α Fres)
    (μ : FinitePMF X) (Q : X → FinitePMF H) (P : E d → X → FinitePMF H)
    [hP : ∀ θ, ∀ ξ, HasPositivePrior (P θ ξ)] (ω : ℕ → S × S) (T : ℕ) :
    cumCP (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) (fun n => x n ω) T
      ≤ condCrossEntropyFinitePMF μ Q (P x₀) - condEntropyFinitePMF μ Q :=
  iteratesOfResidual_ledger_le_initial_gap hx
    (fun z => by haveI := hP z; exact condEntropy_le_condCrossEntropy μ Q (P z)) ω T

end TrueProgress

end AuditCPRL
