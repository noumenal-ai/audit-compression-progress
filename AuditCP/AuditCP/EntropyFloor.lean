import AuditCP.FiniteBlackwellBrier
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chapter 11 — what the ledger cannot buy

The slack of Chapter 3 bounds the gap between a measured and a population reading (schmidhuber2010).  It says nothing
about how much true progress there is to have.  This chapter says that, and the answer is a
pre-training constant: the total signed progress available on a B2 potential along any B3
trajectory is the initial excess over a floor, and for a cross-entropy potential the floor is the
data's own entropy.  Reducible ignorance pays; noise does not.

The concrete instance refines B2 exactly as `AuditCP.Base` describes it: `FinitePMF` is the
simplex-constrained refinement of a real reading, and `fun θ => condCrossEntropyFinitePMF μ Q (P θ)`
is the resulting `AuditPotential ι` that `cumCP` reads.

`klDivFinitePMF_nonneg` (Gibbs) is assembled from Mathlib `Real.log_le_sub_one_of_pos`.
`entropy_floor_budget` is the abstract budget that takes the floor as a hypothesis, reducing to
`cumCP_le_of_lb`.  The cross-entropy case is then mechanized end to end:
`crossEntropyFinitePMF_eq_entropy_add_kl` (`H(Q,P) = H(Q) + KL`) composed with
`klDivFinitePMF_nonneg` gives the derived floor `entropy_le_crossEntropyFinitePMF`
(`H(Q) ≤ H(Q,P)`), which `entropy_floor_budget_crossEntropy` discharges into the trajectory budget:
the floor is derived, not assumed.
-/

namespace AuditCP

/-- Given a positive-prior `P`, `0 ≤ klDivFinitePMF Q P`. -/
theorem klDivFinitePMF_nonneg {H : Type*} [Fintype H] (Q P : FinitePMF H)
    [HasPositivePrior P] : 0 ≤ klDivFinitePMF Q P := by
  have key : ∀ h : H,
      Q.prob h - P.prob h ≤
        (if Q.prob h = 0 then 0 else Q.prob h * Real.log (Q.prob h / P.prob h)) := by
    intro h
    have hppos : 0 < P.prob h := ‹HasPositivePrior P›.pos h
    by_cases hq : Q.prob h = 0
    · rw [if_pos hq, hq]; linarith
    · rw [if_neg hq]
      have hqpos : 0 < Q.prob h := lt_of_le_of_ne (Q.prob_nonneg h) (Ne.symm hq)
      have hqne : Q.prob h ≠ 0 := ne_of_gt hqpos
      have hlogqp : Real.log (Q.prob h / P.prob h)
          = Real.log (Q.prob h) - Real.log (P.prob h) :=
        Real.log_div hqne (ne_of_gt hppos)
      have hlogpq : Real.log (P.prob h / Q.prob h)
          = Real.log (P.prob h) - Real.log (Q.prob h) :=
        Real.log_div (ne_of_gt hppos) hqne
      have hb : Real.log (P.prob h / Q.prob h) ≤ P.prob h / Q.prob h - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlog : 1 - P.prob h / Q.prob h ≤ Real.log (Q.prob h / P.prob h) := by
        rw [hlogqp]; rw [hlogpq] at hb; linarith
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hqpos)
      have heq : Q.prob h * (1 - P.prob h / Q.prob h) = Q.prob h - P.prob h := by
        field_simp
      rw [heq] at hmul
      exact hmul
  calc (0 : ℝ)
      = ∑ h : H, (Q.prob h - P.prob h) := by
        rw [Finset.sum_sub_distrib, Q.prob_sum_one, P.prob_sum_one]; ring
    _ ≤ ∑ h : H, (if Q.prob h = 0 then 0 else Q.prob h * Real.log (Q.prob h / P.prob h)) :=
        Finset.sum_le_sum (fun h _ => key h)
    _ = klDivFinitePMF Q P := rfl

/-- If `HS ≤ E_S (g T)`, then `cumCP E_S g T ≤ E_S (g 0) - HS` (schmidhuber2010). -/
theorem entropy_floor_budget {ι : Type*} (E_S : AuditPotential ι) (g : AuditTrajectory ι) (T : ℕ)
    {HS : ℝ}
    (hfloor : HS ≤ E_S (g T)) : cumCP E_S g T ≤ E_S (g 0) - HS :=
  cumCP_le_of_lb E_S g T hfloor

/-- The Shannon entropy of the finite pmf `Q`, `∑ h, Q.prob h · log(1 / Q.prob h)`, with each term
taken to be `0` where `Q(h) = 0` (shannon1948). -/
noncomputable def entropyFinitePMF {H : Type*} [Fintype H] (Q : FinitePMF H) : ℝ :=
  ∑ h : H, if Q.prob h = 0 then 0 else Q.prob h * Real.log (1 / Q.prob h)

/-- Given a positive-prior `P`,
`crossEntropyFinitePMF Q P = entropyFinitePMF Q + klDivFinitePMF Q P` (shannon1948; kullback1951). -/
theorem crossEntropyFinitePMF_eq_entropy_add_kl {H : Type*} [Fintype H]
    (Q P : FinitePMF H) [HasPositivePrior P] :
    crossEntropyFinitePMF Q P = entropyFinitePMF Q + klDivFinitePMF Q P := by
  unfold crossEntropyFinitePMF entropyFinitePMF klDivFinitePMF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  by_cases hq : Q.prob h = 0
  · simp [hq]
  · have hppos : 0 < P.prob h := ‹HasPositivePrior P›.pos h
    rw [if_neg hq, if_neg hq, if_neg hq]
    simp only [one_div, Real.log_inv]
    rw [Real.log_div hq hppos.ne']
    ring

/-- Given a positive-prior `P`, `entropyFinitePMF Q ≤ crossEntropyFinitePMF Q P`. -/
theorem entropy_le_crossEntropyFinitePMF {H : Type*} [Fintype H]
    (Q P : FinitePMF H) [HasPositivePrior P] :
    entropyFinitePMF Q ≤ crossEntropyFinitePMF Q P := by
  have hkl := klDivFinitePMF_nonneg Q P
  rw [crossEntropyFinitePMF_eq_entropy_add_kl Q P]; linarith

/-- Given a positive prior at every `P θ`,
`cumCP (fun θ => crossEntropyFinitePMF Q (P θ)) g T ≤
crossEntropyFinitePMF Q (P (g 0)) - entropyFinitePMF Q` (schmidhuber2010). -/
theorem entropy_floor_budget_crossEntropy {ι H : Type*} [Fintype H]
    (Q : FinitePMF H) (P : ι → FinitePMF H) [∀ θ, HasPositivePrior (P θ)]
    (g : AuditTrajectory ι) (T : ℕ) :
    cumCP (fun θ => crossEntropyFinitePMF Q (P θ)) g T
      ≤ crossEntropyFinitePMF Q (P (g 0)) - entropyFinitePMF Q :=
  cumCP_le_of_lb (fun θ => crossEntropyFinitePMF Q (P θ)) g T
    (entropy_le_crossEntropyFinitePMF Q (P (g T)))

/-! ## Conditional (input-averaged) entropy floor — the form stated in the paper

Theorem 3 in the paper is stated for a conditional data distribution `Q(Y|X)` with conditional
entropy `H_{Q}(Y|X)` and an input-averaged log-loss risk `E_S(θ)`. The declarations above prove
the single-distribution (unconditional) case. The layer below lifts that case to the conditional
statement by averaging over a finite input space `X` against an input marginal `μ`: the per-input
Gibbs floor is combined under a nonnegative-weighted sum, which is exactly the paper's
`E_S(θ) = H(Y|X) + E_x KL`, `E_x KL ≥ 0`. No new analytic content is introduced; the lift is
monotonicity of a finite expectation. -/
section Conditional
variable {ι X H : Type*} [Fintype X] [Fintype H]

/-- The conditional Shannon entropy of `Q` given input marginal `μ`,
`∑ x, μ.prob x * entropyFinitePMF (Q x)` (shannon1948). -/
noncomputable def condEntropyFinitePMF (μ : FinitePMF X) (Q : X → FinitePMF H) : ℝ :=
  ∑ x : X, μ.prob x * entropyFinitePMF (Q x)

/-- The input-averaged cross-entropy of `Q` relative to `P` under `μ`,
`∑ x, μ.prob x * crossEntropyFinitePMF (Q x) (P x)`. -/
noncomputable def condCrossEntropyFinitePMF (μ : FinitePMF X) (Q P : X → FinitePMF H) : ℝ :=
  ∑ x : X, μ.prob x * crossEntropyFinitePMF (Q x) (P x)

/-- The input-averaged Kullback–Leibler divergence of `Q` from `P` under `μ`,
`∑ x, μ.prob x * klDivFinitePMF (Q x) (P x)` (kullback1951). -/
noncomputable def condKLDivFinitePMF (μ : FinitePMF X) (Q P : X → FinitePMF H) : ℝ :=
  ∑ x : X, μ.prob x * klDivFinitePMF (Q x) (P x)

/-- Given a positive prior at every `P x`,
`condCrossEntropyFinitePMF μ Q P = condEntropyFinitePMF μ Q + condKLDivFinitePMF μ Q P`. -/
theorem condCrossEntropyFinitePMF_eq_entropy_add_kl (μ : FinitePMF X) (Q P : X → FinitePMF H)
    [hP : ∀ x, HasPositivePrior (P x)] :
    condCrossEntropyFinitePMF μ Q P = condEntropyFinitePMF μ Q + condKLDivFinitePMF μ Q P := by
  unfold condCrossEntropyFinitePMF condEntropyFinitePMF condKLDivFinitePMF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  haveI := hP x
  rw [crossEntropyFinitePMF_eq_entropy_add_kl (Q x) (P x)]; ring

/-- Given a positive prior at every `P x`, `0 ≤ condKLDivFinitePMF μ Q P`. -/
theorem condKLDivFinitePMF_nonneg (μ : FinitePMF X) (Q P : X → FinitePMF H)
    [hP : ∀ x, HasPositivePrior (P x)] : 0 ≤ condKLDivFinitePMF μ Q P := by
  refine Finset.sum_nonneg (fun x _ => ?_)
  haveI := hP x
  exact mul_nonneg (μ.prob_nonneg x) (klDivFinitePMF_nonneg (Q x) (P x))

/-- Given a positive prior at every `P x`,
`condEntropyFinitePMF μ Q ≤ condCrossEntropyFinitePMF μ Q P`. -/
theorem condEntropy_le_condCrossEntropy (μ : FinitePMF X) (Q P : X → FinitePMF H)
    [∀ x, HasPositivePrior (P x)] :
    condEntropyFinitePMF μ Q ≤ condCrossEntropyFinitePMF μ Q P := by
  have h := condKLDivFinitePMF_nonneg μ Q P
  rw [condCrossEntropyFinitePMF_eq_entropy_add_kl μ Q P]; linarith

/-- Given a positive prior at every `P θ x`,
`cumCP (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) g T ≤
condCrossEntropyFinitePMF μ Q (P (g 0)) - condEntropyFinitePMF μ Q`. -/
theorem cond_entropy_floor_budget_crossEntropy (μ : FinitePMF X) (Q : X → FinitePMF H)
    (P : ι → X → FinitePMF H) [hP : ∀ θ, ∀ x, HasPositivePrior (P θ x)]
    (g : AuditTrajectory ι) (T : ℕ) :
    cumCP (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) g T
      ≤ condCrossEntropyFinitePMF μ Q (P (g 0)) - condEntropyFinitePMF μ Q := by
  haveI := hP (g T)
  exact cumCP_le_of_lb (fun θ => condCrossEntropyFinitePMF μ Q (P θ)) g T
    (condEntropy_le_condCrossEntropy μ Q (P (g T)))

end Conditional

end AuditCP
