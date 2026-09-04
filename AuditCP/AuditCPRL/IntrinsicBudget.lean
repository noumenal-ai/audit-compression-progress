import AuditCPRL.L0
import AuditCP.EntropyFloor
import AuditCP.FiniteExperts
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

/-!
# Target 3 — an intrinsic compression reward is budgeted by the environment's own kernel

The agent's intrinsic reward at step `t` is the **measured** audit decrement
`r t = Ehat (θ t) − Ehat (θ (t+1))`, so the intrinsic return over a horizon `T` is exactly
`AuditCP.cumCP Ehat g T` (schmidhuber1991; schmidhuber2010).  Audit the agent's model of *its own environment*: the audit input
law is the MRP's stationary occupancy `ReinforcementLearning.FiniteMRP.μ` and the audit target
conditional is the MRP's transition row `ReinforcementLearning.FiniteMRP.P`.

Two facts, and only the second is a crossover.

* `intrinsic_return_le_condKL` — the intrinsic return is at most the **initial conditional KL**
  of the agent's model from the audited conditional, plus `2Δ`, for every horizon at once.  This
  is `AuditCPRL.finite_audit_goodhart_twoPoint` (L0 plus a bound on the centered increment)
  composed with `AuditCP.cumCP_le_of_lb`, `AuditCP.condEntropy_le_condCrossEntropy` and
  `AuditCP.condCrossEntropyFinitePMF_eq_entropy_add_kl`.  It carries **no** RL binder, and it is
  labelled a remark below for exactly that reason: every RL binder is deletable from it.
* `mrp_intrinsic_return_budget` — the same bound with the audited pair supplied by an ergodic
  MRP, **together with** the statement that the audit weight is strictly positive at every state.
  The second conjunct is not deletable: it is `StochasticMatrix.pos_of_stationary` applied to
  `ReinforcementLearning.FiniteMRP.μ`, and it consumes irreducibility, i.e. the first component
  of `ReinforcementLearning.FiniteMRP.hM`.  Its content is that an ergodic environment leaves the
  agent no unaudited state on which to hide model error, so the budget is a **full-support**
  average of per-state divergences.

## Scope, stated rather than assumed

The bound is the initial conditional KL, not the initial cross-entropy: the environment's own
conditional entropy `AuditCP.condEntropyFinitePMF` has already been deducted and is unreachable.
The prize is finite, collected once, and largest exactly when the agent started ignorant.

-/

namespace AuditCPRL

open AuditCP ReinforcementLearning StochasticMatrix MeasureTheory

universe u

section Bridge
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The MRP's stationary occupancy `FiniteMRP.μ` packaged as a finite pmf. -/
noncomputable def mrpOccupancy (MRP : FiniteMRP (S := S)) : FinitePMF S where
  prob := FiniteMRP.μ (MRP := MRP)
  prob_nonneg := (inferInstance : StochasticVec (FiniteMRP.μ (MRP := MRP))).nonneg
  prob_sum_one := (inferInstance : StochasticVec (FiniteMRP.μ (MRP := MRP))).rowsum

/-- Row `s` of the MRP's transition matrix `FiniteMRP.P` packaged as a finite pmf. -/
noncomputable def mrpKernelRow (MRP : FiniteMRP (S := S)) (s : S) : FinitePMF S where
  prob := FiniteMRP.P (MRP := MRP) s
  prob_nonneg := ((inferInstance : RowStochastic (FiniteMRP.P (MRP := MRP))).stochastic s).nonneg
  prob_sum_one := ((inferInstance : RowStochastic (FiniteMRP.P (MRP := MRP))).stochastic s).rowsum

end Bridge

/-! ### The audit-side budget.  No RL binder occurs, and none is deletable from it because none
is present: this is `AuditCP` instantiated at a conditional log-loss potential.  It is stated
because the crossover below is exactly it plus one fact about ergodic occupancy. -/

section Remark
variable {ι X H : Type*} [Fintype X] [Fintype H]

/-- If `UniformDev F Ehat (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) Δ` holds and the
endpoints `g 0, g T ∈ F` have positive-prior `P`, then
`cumCP Ehat g T ≤ condKLDivFinitePMF μ Q (P (g 0)) + 2Δ`. -/
theorem intrinsic_return_le_condKL
    (μ : FinitePMF X) (Q : X → FinitePMF H) (P : ι → X → FinitePMF H)
    {F : Set ι} {Ehat : ι → ℝ} {Δ : ℝ}
    (hUD : UniformDev F Ehat (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) Δ)
    (g : ℕ → ι) (T : ℕ) (h0 : g 0 ∈ F) (hT : g T ∈ F)
    [∀ x, HasPositivePrior (P (g 0) x)] [∀ x, HasPositivePrior (P (g T) x)] :
    cumCP Ehat g T ≤ condKLDivFinitePMF μ Q (P (g 0)) + 2 * Δ := by
  have hslack := finite_audit_goodhart_twoPoint hUD h0 hT
  have hfloor := cumCP_le_of_lb (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) g T
    (condEntropy_le_condCrossEntropy μ Q (P (g T)))
  have hdec := condCrossEntropyFinitePMF_eq_entropy_add_kl μ Q (P (g 0))
  linarith

end Remark

/-! ### The crossover.  `ReinforcementLearning.FiniteMRP` enters and is not deletable. -/

section Crossover
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {ι : Type*}

/-- Under the hypotheses of `intrinsic_return_le_condKL` specialized to `μ := mrpOccupancy MRP`
and `Q := mrpKernelRow MRP`, the same bound holds, and in addition
`0 < (mrpOccupancy MRP).prob s` at every state `s` (schmidhuber1991; schmidhuber2010). -/
theorem mrp_intrinsic_return_budget (MRP : FiniteMRP (S := S))
    (P : ι → S → FinitePMF S) {F : Set ι} {Ehat : ι → ℝ} {Δ : ℝ}
    (hUD : UniformDev F Ehat
      (fun θ => condCrossEntropyFinitePMF (mrpOccupancy MRP) (mrpKernelRow MRP) (P θ)) Δ)
    (g : ℕ → ι) (T : ℕ) (h0 : g 0 ∈ F) (hT : g T ∈ F)
    [∀ x, HasPositivePrior (P (g 0) x)] [∀ x, HasPositivePrior (P (g T) x)] :
    cumCP Ehat g T
        ≤ condKLDivFinitePMF (mrpOccupancy MRP) (mrpKernelRow MRP) (P (g 0)) + 2 * Δ
      ∧ ∀ s : S, 0 < (mrpOccupancy MRP).prob s := by
  haveI : StochasticMatrix.Irreducible (FiniteMRP.P (MRP := MRP)) := MRP.hM.1
  exact ⟨intrinsic_return_le_condKL (mrpOccupancy MRP) (mrpKernelRow MRP) P hUD g T h0 hT,
    pos_of_stationary (FiniteMRP.μ (MRP := MRP)) (FiniteMRP.P (MRP := MRP))⟩

/-- `0 < (mrpOccupancy MRP).prob s`, and `(mrpOccupancy MRP).prob s *
klDivFinitePMF (mrpKernelRow MRP s) (P s) ≤ condKLDivFinitePMF (mrpOccupancy MRP)
(mrpKernelRow MRP) P`. -/
theorem mrp_no_unaudited_state (MRP : FiniteMRP (S := S))
    (P : S → FinitePMF S) [∀ x, HasPositivePrior (P x)] (s : S) :
    0 < (mrpOccupancy MRP).prob s
      ∧ (mrpOccupancy MRP).prob s * klDivFinitePMF (mrpKernelRow MRP s) (P s)
          ≤ condKLDivFinitePMF (mrpOccupancy MRP) (mrpKernelRow MRP) P := by
  refine ⟨pos_of_stationary (FiniteMRP.μ (MRP := MRP)) (FiniteMRP.P (MRP := MRP)) s, ?_⟩
  simp only [condKLDivFinitePMF]
  exact Finset.single_le_sum
    (f := fun x => (mrpOccupancy MRP).prob x * klDivFinitePMF (mrpKernelRow MRP x) (P x))
    (fun x _ => mul_nonneg ((mrpOccupancy MRP).prob_nonneg x)
      (klDivFinitePMF_nonneg (mrpKernelRow MRP x) (P x)))
    (Finset.mem_univ s)

/-- If the panel's population loss equals `condCrossEntropyFinitePMF (mrpOccupancy MRP)
(mrpKernelRow MRP) (P θ)` at every `θ` (`hloss`), `loss` is measurable and a.e. valued in
`[a, b]`, and the two endpoints have positive-prior `P`, then `0 < (mrpOccupancy MRP).prob s` at
every state `s`, and on an i.i.d. panel of size `n`, with probability at least `1 - δ` the
measured intrinsic return over every horizon is at most `condKLDivFinitePMF (mrpOccupancy MRP)
(mrpKernelRow MRP) (P (g 0)) + 2 · deltaFiniteExperts (card ι) n (b - a) δ`. -/
theorem mrp_intrinsic_return_budget_iid (MRP : FiniteMRP (S := S))
    [Fintype ι] [Nonempty ι] (P : ι → S → FinitePMF S)
    {Z : Type*} [MeasurableSpace Z] (Qmeas : Measure Z) [IsProbabilityMeasure Qmeas]
    (n : ℕ) (hn : 0 < n) (a b : ℝ) (hab : a < b) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (loss : ι → Z → ℝ) (hmeas : ∀ i, Measurable (loss i))
    (hbdd : ∀ i, ∀ᵐ z ∂Qmeas, loss i z ∈ Set.Icc a b)
    (hloss : ∀ θ, populationLoss Qmeas loss θ
      = condCrossEntropyFinitePMF (mrpOccupancy MRP) (mrpKernelRow MRP) (P θ))
    (g : ℕ → ι) (T : ℕ)
    [∀ x, HasPositivePrior (P (g 0) x)] [∀ x, HasPositivePrior (P (g T) x)] :
    (∀ s : S, 0 < (mrpOccupancy MRP).prob s)
      ∧ 1 - δ ≤ (Measure.pi fun _ : Fin n => Qmeas).real
          {panel : Fin n → Z | cumCP (fun θ => empiricalLoss loss θ panel) g T
            ≤ condKLDivFinitePMF (mrpOccupancy MRP) (mrpKernelRow MRP) (P (g 0))
              + 2 * deltaFiniteExperts (Fintype.card ι) n (b - a) δ} := by
  refine ⟨pos_of_stationary (FiniteMRP.μ (MRP := MRP)) (FiniteMRP.P (MRP := MRP)), ?_⟩
  refine (finite_experts_iid_uniformDev Qmeas n hn a b hab δ hδ0 hδ1 loss hmeas hbdd).trans
    (measureReal_mono ?_ (measure_ne_top _ _))
  intro panel hpanel
  have hUD : UniformDev Set.univ (fun θ => empiricalLoss loss θ panel)
      (fun θ => condCrossEntropyFinitePMF (mrpOccupancy MRP) (mrpKernelRow MRP) (P θ))
      (deltaFiniteExperts (Fintype.card ι) n (b - a) δ) := by
    intro θ hθ
    simpa only [hloss θ] using hpanel θ hθ
  exact intrinsic_return_le_condKL (mrpOccupancy MRP) (mrpKernelRow MRP) P hUD g T
    (Set.mem_univ _) (Set.mem_univ _)

end Crossover

end AuditCPRL
