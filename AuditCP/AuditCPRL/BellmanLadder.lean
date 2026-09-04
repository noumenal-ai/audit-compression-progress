import AuditCPRL.L0
import AuditCP.StructuralAudit
import RLTheory.Algorithm.QLearning

/-!
# Target 3 — a declared Q-function ladder, audited on one sealed panel

The audited object is `ReinforcementLearning.QLearning.QLearningSpec.update`, RLTheory's own
Q-learning update vector, scored by its squared magnitude on one i.i.d. panel of transitions.
Two things are proved.

* **The radius is priced in MDP terms.**  `‖QLearningSpec.x y‖ = 1` and a sup-norm budget `B` on
  the ladder put the audited loss in `[0, (Rmax + (1 + γ) * B)²]`, so the finite-experts radius
  `AuditCP.deltaFiniteExperts` carries `γ` and `Rmax`.  Perturbing the discount perturbs the
  conclusion; the RL binder is not decoration.
* **What the panel certifies is not the Bellman residual.**  Averaging the audited loss over the
  next state at a fixed state-action pair splits exactly into the squared Bellman residual of
  `QLearningSpec.bellman_op` plus `γ²` times the conditional variance of the greedy target.  A
  single-transition panel cannot separate them: this is the double-sampling gap, and it is what
  audit-CP has to say about RL here.

## Obligation carried, not discharged

`populationLoss_update_sq_eq_bellman_sq_add_var` takes the panel law's one-step marginal structure
as the **named hypothesis** `hpanel`.  RLTheory has no functional taking a `QLearningSpec` to a law
on transitions, so `hpanel` cannot be derived in scope and is not fabricated.
-/

namespace AuditCPRL

open AuditCP MeasureTheory RLTheory
open ReinforcementLearning ReinforcementLearning.QLearning

universe u

/-! ### Weighted bias-variance split (infrastructure, no RL and no audit) -/

/-- If `∑ i, p i = 1`, then `∑ i, p i * (c + γ * M i) ^ 2 = (c + γ * ∑ i, p i * M i) ^ 2 +
γ ^ 2 * ∑ i, p i * (M i - ∑ j, p j * M j) ^ 2`. -/
theorem sum_weighted_sq_eq_sq_add_var {ι : Type*} [Fintype ι] (p M : ι → ℝ) (c γ : ℝ)
    (hp : ∑ i, p i = 1) :
    ∑ i, p i * (c + γ * M i) ^ 2
      = (c + γ * ∑ i, p i * M i) ^ 2
        + γ ^ 2 * ∑ i, p i * (M i - ∑ j, p j * M j) ^ 2 := by
  classical
  set m : ℝ := ∑ j, p j * M j with hm
  have h1 : ∑ i, p i * (c + γ * M i) ^ 2
      = ∑ i, ((c + γ * m) ^ 2 * p i
          + (2 * γ * (c + γ * m)) * (p i * M i - m * p i)
          + γ ^ 2 * (p i * (M i - m) ^ 2)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hp, ← hm, ← Finset.mul_sum]
  ring

section Ball
variable {S : Type u} [Fintype S] {A : Type u} [Fintype A]

/-- The sup-norm ball of radius `B` in `E (Fintype.card (S × A))`, `{z | ∀ i, |z i| ≤ B}`. -/
def qBall (B : ℝ) : Set (E (Fintype.card (S × A))) := {z | ∀ i, |z i| ≤ B}

/-- If `q ∈ qBall B`, then `|QLearningSpec.maxₐ q s| ≤ B`. -/
theorem abs_max_a_le_of_mem_qBall [Nonempty A] {B : ℝ} {q : E (Fintype.card (S × A))}
    (hq : q ∈ qBall (S := S) (A := A) B) (s : S) :
    |QLearningSpec.maxₐ q s| ≤ B := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  refine abs_le.2 ⟨?_, ?_⟩
  · exact le_trans (abs_le.1 (hq (sa_to_fin (s, a₀)))).1
      (Finset.le_sup' (fun a => q (sa_to_fin (s, a))) (Finset.mem_univ a₀))
  · exact Finset.sup'_le _ _ fun a _ => (abs_le.1 (hq (sa_to_fin (s, a)))).2

/-- `‖QLearningSpec.x y‖ = 1`. -/
theorem norm_qlearning_x_eq_one (y : S × A) :
    ‖QLearningSpec.x (S := S) (A := A) y‖ = 1 := by
  have h : QLearningSpec.x (S := S) (A := A) y
      = EuclideanSpace.single (sa_to_fin y) (1 : ℝ) := by
    refine PiLp.ext ?_
    intro i
    simp [QLearningSpec.x]
  rw [h, PiLp.norm_single, norm_one]

end Ball

/-! ### The audited loss, and its range in MDP units -/

section Update
variable {S : Type u} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- `‖spec.update q y‖ ^ 2 = (spec.r y.1 + spec.γ * QLearningSpec.maxₐ q y.2.1 -
q (sa_to_fin y.1)) ^ 2`. -/
theorem sq_norm_update (spec : QLearningSpec (S := S) (A := A))
    (q : E (Fintype.card (S × A))) (y : (S × A) × S × A) :
    ‖spec.update q y‖ ^ 2
      = (spec.r y.1 + spec.γ * QLearningSpec.maxₐ q y.2.1 - q (sa_to_fin y.1)) ^ 2 := by
  simp only [QLearningSpec.update, norm_smul, Real.norm_eq_abs, norm_qlearning_x_eq_one, mul_one]
  exact sq_abs _

/-- If `|spec.r sa| ≤ Rmax` for every `sa` and `q ∈ qBall B`, then
`‖spec.update q y‖ ≤ Rmax + (1 + spec.γ) * B`. -/
theorem norm_update_le_of_mem_qBall (spec : QLearningSpec (S := S) (A := A))
    {Rmax B : ℝ} (hR : ∀ sa : S × A, |spec.r sa| ≤ Rmax)
    {q : E (Fintype.card (S × A))} (hq : q ∈ qBall (S := S) (A := A) B)
    (y : (S × A) × S × A) :
    ‖spec.update q y‖ ≤ Rmax + (1 + spec.γ) * B := by
  have hγ : 0 ≤ spec.γ := spec.hγ.1
  have hx : ‖spec.update q y‖
      = |spec.r y.1 + spec.γ * QLearningSpec.maxₐ q y.2.1 - q (sa_to_fin y.1)| := by
    simp only [QLearningSpec.update, norm_smul, Real.norm_eq_abs, norm_qlearning_x_eq_one, mul_one]
  have h1 := abs_le.1 (hR y.1)
  have h2 := abs_le.1 (abs_max_a_le_of_mem_qBall hq y.2.1)
  have h3 := abs_le.1 (hq (sa_to_fin y.1))
  have hu : spec.γ * QLearningSpec.maxₐ q y.2.1 ≤ spec.γ * B :=
    mul_le_mul_of_nonneg_left h2.2 hγ
  have hl : spec.γ * (-B) ≤ spec.γ * QLearningSpec.maxₐ q y.2.1 :=
    mul_le_mul_of_nonneg_left h2.1 hγ
  have hlr : spec.γ * (-B) = -(spec.γ * B) := by ring
  have hexp : Rmax + (1 + spec.γ) * B = Rmax + B + spec.γ * B := by ring
  rw [hx, abs_le, hexp]
  rw [hlr] at hl
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

/-! ### The crossover: one sealed panel, a declared ladder, an MDP-priced radius -/

/-- If the reward is bounded by `Rmax`, every rung of the ladder lies in `qBall B`, every
training-generated path `g` through the ladder is admissible for `F`, and class membership is
measurable, then on an i.i.d. panel of size `n`, measured cumulative reduction in squared update
magnitude across the ladder exceeds the population reduction by more than
`2 · deltaFiniteExperts N n ((Rmax + (1 + spec.γ) * B) ^ 2) δ` with probability at most
`ENNReal.ofReal δ`. -/
theorem qlearning_ladder_sealedPanel_goodhart
    {Ωtrain : Type*} [MeasurableSpace Ωtrain]
    (spec : QLearningSpec (S := S) (A := A))
    (μtrain : Measure Ωtrain) [IsProbabilityMeasure μtrain]
    (Q : Measure ((S × A) × S × A)) [IsProbabilityMeasure Q]
    {N : ℕ} (hN : 0 < N) (ladder : Fin N → E (Fintype.card (S × A)))
    {Rmax B : ℝ} (hRmax : 0 < Rmax) (hB : 0 ≤ B)
    (hR : ∀ sa : S × A, |spec.r sa| ≤ Rmax)
    (hladder : ∀ i, ladder i ∈ qBall (S := S) (A := A) B)
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (F : Ωtrain → Set (Fin N)) (g : Ωtrain → ℕ → Fin N)
    (hadm : ∀ t, Admissible (g t) (F t))
    (hF : ∀ i, MeasurableSet {t | i ∈ F t}) (T : ℕ) :
    (μtrain.prod (Measure.pi (fun _ : Fin n => Q)))
      {p : Ωtrain × (Fin n → (S × A) × S × A) |
        cumCP (fun i => empiricalLoss (fun j y => ‖spec.update (ladder j) y‖ ^ 2) i p.2)
            (g p.1) T >
          cumCP (fun i => populationLoss Q (fun j y => ‖spec.update (ladder j) y‖ ^ 2) i)
            (g p.1) T
          + 2 * deltaFiniteExperts N n ((Rmax + (1 + spec.γ) * B) ^ 2) δ} ≤
      ENNReal.ofReal δ := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hγ : 0 ≤ spec.γ := spec.hγ.1
  have hsum : 0 < Rmax + (1 + spec.γ) * B := by nlinarith
  have hrange : (0 : ℝ) < (Rmax + (1 + spec.γ) * B) ^ 2 := pow_pos hsum 2
  have hmeas : ∀ j, Measurable (fun y : (S × A) × S × A => ‖spec.update (ladder j) y‖ ^ 2) :=
    fun _ => measurable_of_countable _
  have hbdd : ∀ j, ∀ᵐ y ∂Q, ‖spec.update (ladder j) y‖ ^ 2 ∈
      Set.Icc (0 : ℝ) ((Rmax + (1 + spec.γ) * B) ^ 2) := by
    intro j
    refine Filter.Eventually.of_forall fun y => ⟨sq_nonneg _, ?_⟩
    have h := norm_update_le_of_mem_qBall spec hR (hladder j) y
    nlinarith [norm_nonneg (spec.update (ladder j) y)]
  simpa only [Fintype.card_fin, sub_zero] using
    auditBlind_finiteTrajectory_goodhart_of_measurableClass
      μtrain Q n hn 0 ((Rmax + (1 + spec.γ) * B) ^ 2) hrange δ hδ0 hδ1
      (fun j y => ‖spec.update (ladder j) y‖ ^ 2) hmeas hbdd F g hadm hF T

/-! ### What the sealed panel actually certifies: the double-sampling gap -/

/-- `spec.bellman_op q (sa_to_fin sa) = spec.r sa + spec.γ * ∑ s', (spec.P sa {s'} : ℝ) *
QLearningSpec.maxₐ q s'`. -/
theorem bellman_op_apply (spec : QLearningSpec (S := S) (A := A))
    (q : E (Fintype.card (S × A))) (sa : S × A) :
    spec.bellman_op q (sa_to_fin sa)
      = spec.r sa + spec.γ * ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
          * QLearningSpec.maxₐ q s' := by
  simp only [QLearningSpec.bellman_op, PiLp.toLp_apply, fin_to_sa, sa_to_fin,
    Equiv.symm_apply_apply]

/-- `∑ s', (spec.P sa {s'} : ℝ) * (spec.r sa + spec.γ * QLearningSpec.maxₐ q s' -
q (sa_to_fin sa)) ^ 2 = (spec.bellman_op q (sa_to_fin sa) - q (sa_to_fin sa)) ^ 2 +
spec.γ ^ 2 * ∑ s', (spec.P sa {s'} : ℝ) * (QLearningSpec.maxₐ q s' -
∑ s'', (spec.P sa {s''} : ℝ) * QLearningSpec.maxₐ q s'') ^ 2`. -/
theorem sum_residual_sq_eq_bellman_residual_sq_add_var
    (spec : QLearningSpec (S := S) (A := A)) (q : E (Fintype.card (S × A))) (sa : S × A) :
    ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
        * (spec.r sa + spec.γ * QLearningSpec.maxₐ q s' - q (sa_to_fin sa)) ^ 2
      = (spec.bellman_op q (sa_to_fin sa) - q (sa_to_fin sa)) ^ 2
        + spec.γ ^ 2 * ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
            * (QLearningSpec.maxₐ q s'
                - ∑ s'' : S, ((spec.P sa {s''} : NNReal) : ℝ)
                    * QLearningSpec.maxₐ q s'') ^ 2 := by
  have hp : ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ) = 1 := by
    rw [← NNReal.coe_sum, sum_probability_singleton, NNReal.coe_one]
  have hkey := sum_weighted_sq_eq_sq_add_var
    (fun s' : S => ((spec.P sa {s'} : NNReal) : ℝ)) (fun s' : S => QLearningSpec.maxₐ q s')
    (spec.r sa - q (sa_to_fin sa)) spec.γ hp
  rw [show (∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
        * (spec.r sa + spec.γ * QLearningSpec.maxₐ q s' - q (sa_to_fin sa)) ^ 2)
      = ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
        * (spec.r sa - q (sa_to_fin sa) + spec.γ * QLearningSpec.maxₐ q s') ^ 2
      from Finset.sum_congr rfl fun s' _ => by ring, bellman_op_apply,
    show spec.r sa + spec.γ * (∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
          * QLearningSpec.maxₐ q s') - q (sa_to_fin sa)
        = spec.r sa - q (sa_to_fin sa) + spec.γ * (∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
          * QLearningSpec.maxₐ q s') from by ring]
  exact hkey

/-- If the panel law's (state-action, next-state) marginal is `visit` composed with the MDP's own
transition kernel (`hpanel`), then `populationLoss Q (fun j y => ‖spec.update (ladder j) y‖ ^ 2) i`
equals the `visit`-weighted sum of the squared Bellman residual of `ladder i` plus `spec.γ ^ 2`
times the `visit`-weighted conditional variance of the greedy continuation value. -/
theorem populationLoss_update_sq_eq_bellman_sq_add_var
    (spec : QLearningSpec (S := S) (A := A)) (Q : Measure ((S × A) × S × A))
    {N : ℕ} (ladder : Fin N → E (Fintype.card (S × A))) (i : Fin N) (visit : S × A → ℝ)
    (hpanel : ∀ f : (S × A) → S → ℝ,
      ∫ y, f y.1 y.2.1 ∂Q
        = ∑ sa : S × A, visit sa * ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ) * f sa s') :
    populationLoss Q (fun j y => ‖spec.update (ladder j) y‖ ^ 2) i
      = ∑ sa : S × A, visit sa *
          ((spec.bellman_op (ladder i) (sa_to_fin sa) - (ladder i) (sa_to_fin sa)) ^ 2
            + spec.γ ^ 2 * ∑ s' : S, ((spec.P sa {s'} : NNReal) : ℝ)
                * (QLearningSpec.maxₐ (ladder i) s'
                    - ∑ s'' : S, ((spec.P sa {s''} : NNReal) : ℝ)
                        * QLearningSpec.maxₐ (ladder i) s'') ^ 2) := by
  have hQ := hpanel fun sa s' =>
    (spec.r sa + spec.γ * QLearningSpec.maxₐ (ladder i) s' - (ladder i) (sa_to_fin sa)) ^ 2
  simp only [populationLoss, sq_norm_update]
  rw [hQ]
  exact Finset.sum_congr rfl fun sa _ => by
    rw [sum_residual_sq_eq_bellman_residual_sq_add_var]

end Update

end AuditCPRL
