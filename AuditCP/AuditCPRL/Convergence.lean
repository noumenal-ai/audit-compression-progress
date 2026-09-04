import AuditCPRL.L0
import AuditCP.PaperMetrology
import RLTheory.StochasticApproximation.IIDSamples

/-!
# Target 2 — a convergent stochastic-approximation run exhausts its audit ledger

`AuditCP.cumCP` is a signed ledger over an arbitrary index type.  Instantiate the index at the
iterate space `RLTheory.E d` of a stochastic-approximation run and two things become visible that
neither corpus states.

* **The ledger has a pre-training cap.**  For a potential bounded below by `m`, signed cumulative
  compression progress never exceeds `Etrue x₀ - m`, pathwise, at every horizon.  The number is
  deterministic and available before the run starts, because
  `StochasticApproximation.IteratesOfResidual.init` fixes the start point.  This needs no measure
  and no convergence.
* **The cap is exhausted, not merely respected.**  If the potential attains its floor at the limit
  point, the ledger converges almost surely to exactly `Etrue x₀ - m`.  The learner's total
  lifetime audit credit is therefore a quantity an auditor can price at initialisation, and running
  longer cannot enlarge it.

At the distance-to-limit potential the constant is `‖x₀ - fixedPoint‖`: the run's entire lifetime
credit is its initial suboptimality, and nothing else.

## Which RLTheory hypotheses bite

`StochasticApproximation.ae_tendsto_of_iterates_iid_samples` is the handle.  Every one of its
hypotheses is consumed and none is assumed: the residual map's measurability and Lipschitz bound,
the fixed-point equation, the expectation identity against `ReinforcementLearning.FiniteMRP`'s
`μ` and `P`, `StochasticApproximation.RobbinsMonro` on the step sizes, and the
`StochasticApproximation.LyapunovFunction` instance.  The measure is
`ReinforcementLearning.FiniteMRP.iid_samples`.  Deleting the `hx` binder alone costs both halves:
the cap loses its pre-training constant and exhaustion loses its hypothesis outright.

The claim is stated at the stochastic-approximation level rather than at one algorithm.  That is
where it is invariant: RLTheory's linear-TD and Q-learning convergence theorems are the same handle
under different names, and instantiating either changes only the constant.  Perturbing the
potential changes only the constant too, which is why the potential is a binder here.

## The audited half

`AuditCP.UniformDev` and `AuditCP.Admissible` enter as binders, and the audit is routed through L0
(`AuditCPRL.cumCP_sub_cumCP_eq_centered_increment`) plus a bound on the centered increment, i.e.
through `AuditCPRL.finite_audit_goodhart_twoPoint`, never through the corpus theorem that
quantifies containment over every step.  Two consequences.

* The audit reads two points, and `init` supplies one of them before training, so the audit's
  requirement at the start point is an ω-free, T-free design-time check.
* One uniform-deviation event covers every horizon: `Fenv` and `Δ` carry no `T`, so the *measured*
  ledger obeys `≤ (Etrue x₀ - m) + 2 * Δ` uniformly in the number of updates.  The auditor does not
  pay for the learner's sample complexity.

Exhibiting `Fenv` and `Δ` for an actual learner is not done here and is not assumed away: it is the
subject of `AuditCPRL.ReachableEnvelope`, and every statement below that needs it carries it as a
binder.

Signed `AuditCP.cumCP` throughout.  Nothing is clipped, and intermediate horizons may carry a
negative ledger.
-/

namespace AuditCPRL

open AuditCP RLTheory StochasticApproximation ReinforcementLearning MeasureTheory Filter Topology

universe u

/-! ### Ingredient.  No RL binder occurs, so this is **not** a crossover. -/

/-- If `Φ` is continuous at `z` and `g` tends to `z`, then `cumCP Φ g T` tends to
`Φ (g 0) - Φ z`. -/
theorem cumCP_tendsto_of_tendsto {ι : Type*} [TopologicalSpace ι] {Φ : ι → ℝ} {g : ℕ → ι} {z : ι}
    (hΦ : ContinuousAt Φ z) (hg : Tendsto g atTop (nhds z)) :
    Tendsto (fun T => cumCP Φ g T) atTop (nhds (Φ (g 0) - Φ z)) := by
  simpa [cumCP_telescope, Function.comp_def] using (hΦ.tendsto.comp hg).const_sub (Φ (g 0))

/-! ### The crossovers.  `StochasticApproximation.IteratesOfResidual` enters here. -/

section Crossover

variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {d : ℕ}
variable {Fres : E d → (S × S) → E d} {f : E d → E d} {fixedPoint x₀ : E d}
variable {x : ℕ → (ℕ → S × S) → E d} {α : ℕ → ℝ} {mrp : FiniteMRP (S := S)}

omit [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres` and `Etrue` is bounded below by `m`, then
`cumCP Etrue (fun n => x n ω) T ≤ Etrue x₀ - m` for every sample path `ω` and horizon `T`. -/
theorem iteratesOfResidual_ledger_le_initial_gap
    (hx : IteratesOfResidual x x₀ α Fres) {Etrue : E d → ℝ} {m : ℝ}
    (hlb : ∀ z, m ≤ Etrue z) (ω : ℕ → S × S) (T : ℕ) :
    cumCP Etrue (fun n => x n ω) T ≤ Etrue x₀ - m := by
  have h := cumCP_le_of_lb Etrue (fun n => x n ω) T (hlb (x T ω))
  rwa [hx.init ω] at h

/-- If `x` is a measurable, Lipschitz-residual stochastic-approximation run toward the fixed point
of `f` under Robbins–Monro step sizes with a Lyapunov function, and the potential `Φ` is
continuous at the fixed point, bounded below by `m`, and attains `m` there, then
`cumCP Φ (fun n => x n ω) T ≤ Φ x₀ - m` for every sample path and horizon, and
`cumCP Φ (fun n => x n ω) T` tends almost surely (in the run's iid-samples law) to `Φ x₀ - m`. -/
theorem iteratesOfResidual_ledger_capped_and_exhausted
    (hx : IteratesOfResidual x x₀ α Fres)
    (hFm : Measurable Fres.uncurry)
    (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖Fres w y - Fres w' y‖ ≤ C * ‖w - w'‖)
    (hf : fixedPoint = f fixedPoint)
    (hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • Fres w (s, s'))
    (hα : RobbinsMonro α)
    {φ : E d → ℝ} {φ' : E d → E d} (hφm : Measurable φ) (hgradφm : Measurable φ')
    [LyapunovFunction φ φ' f]
    {Φ : E d → ℝ} {m : ℝ} (hΦ : ContinuousAt Φ fixedPoint) (hlb : ∀ z, m ≤ Φ z)
    (hfloor : Φ fixedPoint = m) :
    (∀ ω T, cumCP Φ (fun n => x n ω) T ≤ Φ x₀ - m)
      ∧ ∀ᵐ ω ∂ mrp.iid_samples,
          Tendsto (fun T => cumCP Φ (fun n => x n ω) T) atTop (nhds (Φ x₀ - m)) := by
  refine ⟨iteratesOfResidual_ledger_le_initial_gap hx hlb, ?_⟩
  · filter_upwards [ae_tendsto_of_iterates_iid_samples hx hFm hFlip hf hfF hα hφm hgradφm]
      with ω hω
    have h := cumCP_tendsto_of_tendsto hΦ hω
    rwa [hx.init ω, hfloor] at h

/-- Under the hypotheses of `iteratesOfResidual_ledger_capped_and_exhausted` specialized to the
distance-to-limit potential `Φ := fun z => ‖z - fixedPoint‖` and `m := 0`,
`cumCP (fun z => ‖z - fixedPoint‖) (fun n => x n ω) T ≤ ‖x₀ - fixedPoint‖` for every sample path
and horizon, and the ledger tends almost surely to `‖x₀ - fixedPoint‖`. -/
theorem iteratesOfResidual_lifetime_credit
    (hx : IteratesOfResidual x x₀ α Fres)
    (hFm : Measurable Fres.uncurry)
    (hFlip : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖Fres w y - Fres w' y‖ ≤ C * ‖w - w'‖)
    (hf : fixedPoint = f fixedPoint)
    (hfF : ∀ w, f w = ∑ s, ∑ s', (mrp.μ s * mrp.P s s') • Fres w (s, s'))
    (hα : RobbinsMonro α)
    {φ : E d → ℝ} {φ' : E d → E d} (hφm : Measurable φ) (hgradφm : Measurable φ')
    [LyapunovFunction φ φ' f] :
    (∀ ω T, cumCP (fun z => ‖z - fixedPoint‖) (fun n => x n ω) T ≤ ‖x₀ - fixedPoint‖)
      ∧ ∀ᵐ ω ∂ mrp.iid_samples,
          Tendsto (fun T => cumCP (fun z => ‖z - fixedPoint‖) (fun n => x n ω) T) atTop
            (nhds ‖x₀ - fixedPoint‖) := by
  have h := iteratesOfResidual_ledger_capped_and_exhausted hx hFm hFlip hf hfF hα hφm hgradφm
    (Φ := fun z => ‖z - fixedPoint‖) (m := 0)
    (Continuous.continuousAt (by fun_prop)) (fun z => norm_nonneg _) (by simp)
  simpa using h

omit [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres`, `UniformDev Fenv Ehat Etrue Δ` holds,
`x₀ ∈ Fenv`, and the horizon endpoint `x T ω ∈ Fenv`, then
`evidenceLowerBound (cumCP Ehat (fun n => x n ω) T) (2Δ) ≤ cumCP Etrue (fun n => x n ω) T`. -/
theorem iteratesOfResidual_evidenceLowerBound_twoPoint
    (hx : IteratesOfResidual x x₀ α Fres)
    {Fenv : Set (E d)} {Ehat Etrue : E d → ℝ} {Δ : ℝ}
    (hUD : UniformDev Fenv Ehat Etrue Δ) (hstart : x₀ ∈ Fenv)
    (ω : ℕ → S × S) {T : ℕ} (hend : x T ω ∈ Fenv) :
    evidenceLowerBound (cumCP Ehat (fun n => x n ω) T) (2 * Δ)
      ≤ cumCP Etrue (fun n => x n ω) T := by
  have h0 : (fun n => x n ω) 0 ∈ Fenv := by simpa [hx.init ω] using hstart
  exact evidenceLowerBound_le_true (finite_audit_goodhart_twoPoint hUD h0 hend)

omit [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- If `x` satisfies `IteratesOfResidual x x₀ α Fres`, `UniformDev Fenv Ehat Etrue Δ` holds,
`Etrue` is bounded below by `m`, and the run is admissible for `Fenv`, then
`cumCP Ehat (fun n => x n ω) T ≤ (Etrue x₀ - m) + 2Δ` at every horizon `T`. -/
theorem iteratesOfResidual_measured_ledger_le_initial_gap
    (hx : IteratesOfResidual x x₀ α Fres)
    {Fenv : Set (E d)} {Ehat Etrue : E d → ℝ} {Δ m : ℝ}
    (hUD : UniformDev Fenv Ehat Etrue Δ) (hlb : ∀ z, m ≤ Etrue z)
    {ω : ℕ → S × S} (henv : Admissible (fun n => x n ω) Fenv) (T : ℕ) :
    cumCP Ehat (fun n => x n ω) T ≤ (Etrue x₀ - m) + 2 * Δ := by
  have hgood := finite_audit_goodhart_twoPoint (g := fun n => x n ω) (T := T) hUD
    (henv 0) (henv T)
  have hcap := iteratesOfResidual_ledger_le_initial_gap hx hlb ω T
  linarith

end Crossover

end AuditCPRL
