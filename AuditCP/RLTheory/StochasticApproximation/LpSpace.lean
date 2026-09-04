/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.MoveAdd
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

import RLTheory.Defs
import RLTheory.Analysis.Normed.Group.Basic

open ENNReal NNReal Real Finset Filter Asymptotics RLTheory
open scoped Topology InnerProductSpace RealInnerProductSpace Gradient

lemma abs_eq_sign_mul_nhds
  {x : ℝ} (hx : x ≠ 0) :
  (fun y => |y|) =ᶠ[𝓝 x] fun y => x.sign * y := by
  have hfx : 0 < |x| := by simp [abs_pos.mpr hx]
  apply Metric.eventually_nhds_iff.mpr
  use |x| / 2
  constructor
  linarith
  intro y hy
  simp
  simp [dist] at hy
  by_cases hx0 : 0 < x
  case pos =>
    simp [Real.sign_of_pos hx0]
    simp [abs_of_pos hx0] at hy
    rw [←abs_neg, neg_sub] at hy
    have : x - y ≤ |x - y| := by
      apply le_abs_self
    linarith
  case neg =>
    simp at hx0
    have : x < 0 := by apply lt_of_le_of_ne hx0 hx
    simp [Real.sign_of_neg this]
    simp [abs_of_neg this] at hy
    have := le_abs_self (y - x)
    linarith

theorem hasDerivAt_abs_pow {x : ℝ} {n : ℕ} (hn : 2 ≤ n) :
  HasDerivAt (fun x => |x| ^ n)
  (n * |x| ^ (n - 2) * x) x := by
  by_cases hx : x ≠ 0
  case pos =>
    have := abs_eq_sign_mul_nhds hx
    have := EventuallyEq.pow_const this n
    apply HasDerivAt.congr_of_eventuallyEq (h₁ := this)
    have := ((hasDerivAt_id' x).const_mul (x.sign)).pow n
    apply HasDerivAt.congr_deriv this
    simp
    by_cases hx0 : 0 < x
    case pos =>
      simp [Real.sign_of_pos hx0, abs_of_pos hx0]
      rw [mul_assoc, ←pow_succ]
      simp
      apply Or.inl
      apply congrArg
      omega
    case neg =>
      simp at hx0
      have : x < 0 := by apply lt_of_le_of_ne hx0 hx
      simp [Real.sign_of_neg this, abs_of_neg this]
      conv_rhs =>
        rw [mul_assoc, ←neg_neg x, mul_neg, neg_neg, ←pow_succ, mul_neg]
      simp
      apply Or.inl
      have : n - 2 + 1 = n - 1 := by omega
      rw [this]
  case neg =>
    simp at hx
    simp [hx]
    apply hasDerivAt_iff_isLittleO.mpr
    simp
    apply isLittleO_iff.mpr
    simp
    intro c hc
    apply Metric.eventually_nhds_iff.mpr
    simp
    use min c 1
    constructor
    simp
    exact hc
    intro y hy
    rw [zero_pow (by linarith)]
    simp
    have : n = (n - 2) + 1 + 1 := by omega
    rw [this, pow_succ, pow_succ]
    grw [pow_le_one₀]
    rw [one_mul]
    apply mul_le_mul_of_nonneg_right
    apply le_of_lt
    exact hy.trans_le (by apply min_le_left)
    simp
    simp
    apply le_of_lt
    exact hy.trans_le (by apply min_le_right)

theorem hasDeriveAt_hasDerivAt_abs_pow {x : ℝ} {n : ℕ} (hn : 2 ≤ n) :
  HasDerivAt (fun x : ℝ => n * |x| ^ (n - 2) * x)
    (n * (n - 1) * |x| ^ (n - 2)) x := by
  by_cases hx : x ≠ 0
  case pos =>
    have heq := abs_eq_sign_mul_nhds hx
    -- We want to show: f(y) = n * |y|^(n-2) * y =ᶠ[𝓝 x] n * (sign x * y)^(n-2) * y
    --                       = n * sign^(n-2) * y^(n-2) * y = n * sign^(n-2) * y^(n-1)
    have heq_fn : (fun y => n * |y| ^ (n - 2) * y) =ᶠ[𝓝 x]
                  (fun y => n * x.sign ^ (n - 2) * y ^ (n - 1)) := by
      apply heq.mono
      intro y hy
      simp only at hy ⊢
      rw [hy, mul_pow]
      have hsub : n - 2 + 1 = n - 1 := by omega
      calc n * (x.sign ^ (n - 2) * y ^ (n - 2)) * y
          = n * x.sign ^ (n - 2) * (y ^ (n - 2) * y) := by ring
        _ = n * x.sign ^ (n - 2) * y ^ (n - 2 + 1) := by rw [pow_succ]
        _ = n * x.sign ^ (n - 2) * y ^ (n - 1) := by rw [hsub]
    rw [heq_fn.hasDerivAt_iff]
    -- Now prove HasDerivAt for n * sign^(n-2) * y^(n-1)
    have hderiv := ((hasDerivAt_id' x).pow (n - 1)).const_mul (n * x.sign ^ (n - 2))
    apply HasDerivAt.congr_deriv hderiv
    -- Show derivative values are equal: n * sign^(n-2) * (n-1) * x^(n-2) = n * (n-1) * |x|^(n-2)
    have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      simp
    by_cases hx0 : 0 < x
    case pos =>
      simp only [Real.sign_of_pos hx0, one_pow, abs_of_pos hx0]
      have h1 : n - 1 - 1 = n - 2 := by omega
      rw [h1, hn1_cast]
      ring
    case neg =>
      simp only [not_lt] at hx0
      have hxneg : x < 0 := lt_of_le_of_ne hx0 hx
      simp only [Real.sign_of_neg hxneg, abs_of_neg hxneg]
      have h1 : n - 1 - 1 = n - 2 := by omega
      rw [h1, neg_pow, neg_pow, hn1_cast]
      ring
  case neg =>
    simp only [not_not] at hx
    simp only [hx, abs_zero]
    by_cases hn₁ : n = 2
    case pos =>
      subst hn₁
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.cast_ofNat]
      have := (hasDerivAt_id' (0 : ℝ)).const_mul 2
      simp only [mul_one] at this
      apply HasDerivAt.congr_deriv this
      ring
    case neg =>
      have hn₂ : 2 < n := lt_of_le_of_ne hn (fun h => hn₁ h.symm)
      simp only [zero_pow (by omega : n - 2 ≠ 0), mul_zero]
      apply hasDerivAt_iff_isLittleO.mpr
      simp only [sub_zero]
      apply isLittleO_iff.mpr
      intro c hc
      apply Metric.eventually_nhds_iff.mpr
      simp only [dist_zero_right]
      refine ⟨(c / n) ^ (1 / ((n : ℝ) - 2)), by positivity, ?_⟩
      intro y hy
      simp only [mul_zero, smul_zero, sub_zero, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)),
          abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      -- Goal: n * |y|^(n-2) * |y| ≤ c * |y|
      -- Strategy: use mul_le_mul_of_nonneg_right to reduce to n * |y|^(n-2) ≤ c
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg y)
      -- Now need: n * |y|^(n-2) ≤ c
      -- From hy: |y| < (c/n)^(1/(n-2))
      -- So |y|^(n-2) < c/n, hence n * |y|^(n-2) < c
      have hynorm : |y| < (c / n) ^ (1 / ((n : ℝ) - 2)) := hy
      have habs_pow : |y| ^ (n - 2) < c / n := by
        have hne : ((n : ℝ) - 2) ≠ 0 := by
          have : (2 : ℝ) < n := by exact Nat.ofNat_lt_cast.mpr hn₂
          linarith
        have hpos : 0 < ((n : ℝ) - 2) := by
          have : (2 : ℝ) < n := by exact Nat.ofNat_lt_cast.mpr hn₂
          linarith
        have hn2cast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ n)]
          simp
        have hbase_pos : 0 < c / n := by positivity
        have hbase_nonneg : 0 ≤ (c / n) ^ (1 / ((n : ℝ) - 2)) := by positivity
        have h2 : ((c / n) ^ (1 / ((n : ℝ) - 2))) ^ (n - 2) = c / n := by
          rw [← Real.rpow_natCast ((c / n) ^ (1 / ((n : ℝ) - 2))) (n - 2)]
          rw [← Real.rpow_mul hbase_pos.le]
          rw [hn2cast, one_div, inv_mul_cancel₀ hne]
          simp
        calc |y| ^ (n - 2)
            < ((c / n) ^ (1 / ((n : ℝ) - 2))) ^ (n - 2) := pow_lt_pow_left₀ hynorm (abs_nonneg _) (by omega)
          _ = c / n := h2
      have hfinal : n * |y| ^ (n - 2) < c := by
        calc n * |y| ^ (n - 2) < n * (c / n) := by
                apply mul_lt_mul_of_pos_left habs_pow
                simp; linarith
          _ = c := by field_simp
      exact le_of_lt hfinal

namespace StochasticApproximation

variable {p : ℕ}
variable {d : ℕ}
abbrev LpSpace (p : ℕ) (d : ℕ) := PiLp p fun _ : Fin d => ℝ

def toL2 (x : LpSpace p d) : E d := WithLp.toLp 2 x.ofLp

noncomputable def half_sq_Lp : LpSpace p d → ℝ := fun x => 1 / 2 * ‖x‖ ^ 2

noncomputable def half_sq_Lp' : LpSpace p d → LpSpace p d :=
  fun x => WithLp.toLp p fun i => ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i

section smooth

variable [Fact (1 ≤ (p : ℝ≥0∞))]

lemma continuous_half_sq_Lp :
  Continuous (@half_sq_Lp p d) := by
  apply Continuous.mul
  apply continuous_const
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_id

noncomputable def path (x y : LpSpace p d) (t : ℝ) : LpSpace p d :=
  x + t • (y - x)

lemma continuousOn_path (x y : LpSpace p d) :
  ContinuousOn (path x y) (Set.Icc 0 1) := by
  apply ContinuousOn.add
  apply continuousOn_const
  apply ContinuousOn.smul
  apply continuousOn_id
  apply continuousOn_const

noncomputable def Lp_pow_p_path (x y : LpSpace p d) (t : ℝ) : ℝ :=
  ‖path x y t‖ ^ (p : ℝ)

lemma Lp_pow_p_path_ne_zero
  {x y : LpSpace p d} {t : ℝ} {ht : path x y t ≠ 0} :
  Lp_pow_p_path x y t ≠ 0 := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) := by infer_instance
  have hp := hp.elim
  simp at hp
  unfold Lp_pow_p_path
  apply (rpow_ne_zero ?_ ?_).mpr
  simp [ht]
  apply norm_nonneg
  simp
  linarith

lemma continuousOn_Lp_pow_p_path {x y : LpSpace p d} :
  ContinuousOn (Lp_pow_p_path x y) (Set.Icc 0 1) := by
  intro _
  unfold Lp_pow_p_path
  have := (continuousOn_path x y).norm.pow p
  apply ContinuousOn.congr this
  intro t ht
  simp

lemma unfold_Lp_pow_p_path (x y : LpSpace p d) :
  Lp_pow_p_path x y =
    fun t => (∑ i, |x i + t * (y i - x i)| ^ (p : ℝ)) := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) := by infer_instance
  have hp := hp.elim
  simp at hp

  ext t
  simp [Lp_pow_p_path]
  rw [PiLp.norm_eq_sum]
  simp
  rw [←Real.rpow_mul_natCast, inv_mul_cancel₀]
  simp [path]
  simp
  linarith
  apply sum_nonneg; intro i hi; apply pow_nonneg; apply abs_nonneg
  simp
  linarith

noncomputable def Lp_pow_p_path' (x y : LpSpace p d) : ℝ → ℝ :=
  fun t => ∑ i, p * |x.ofLp i + t * (y.ofLp i - x.ofLp i)| ^ (p - 2)
    * (x.ofLp i + t * (y.ofLp i - x.ofLp i)) * (y.ofLp i - x.ofLp i)

lemma continuousOn_Lp_pow_p_path' {x y : LpSpace p d} :
  ContinuousOn (Lp_pow_p_path' x y) (Set.Icc 0 1) := by
  unfold Lp_pow_p_path'
  -- Get component-wise continuity from path continuity
  have hpath := continuousOn_path x y
  -- For each component i, the function t ↦ (path x y t).ofLp i is continuous
  have hcomp : ∀ i, ContinuousOn (fun t => (path x y t).ofLp i) (Set.Icc 0 1) := by
    intro i
    simp only [path, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply ContinuousOn.add
    · apply continuousOn_const
    · apply ContinuousOn.mul
      · apply continuousOn_id
      · apply continuousOn_const
  -- Now prove the sum is continuous
  apply continuousOn_finsetSum
  intro i _
  -- Each term: p * |path_i(t)|^(p-2) * path_i(t) * (y_i - x_i)
  -- where path_i(t) = x.ofLp i + t * (y.ofLp i - x.ofLp i)
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  · apply continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.abs
    exact hcomp i
  · exact hcomp i
  · apply continuousOn_const

lemma hasDerivAt_Lp_pow_p_path (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t : ℝ,
    HasDerivAt (Lp_pow_p_path x y) (Lp_pow_p_path' x y t) t := by
  intro t
  simp [unfold_Lp_pow_p_path]
  apply HasDerivAt.fun_sum
  intro i hi
  set δ := y i - x i
  have h₁ : HasDerivAt (fun t => x i + t * δ) δ t := by
    apply HasDerivAt.const_add
    have := (hasDerivAt_id' t).mul_const δ
    simp at this
    exact this
  have h₂ := hasDerivAt_abs_pow (hn := hp) (x := x i + t * δ)
  have := HasDerivAt.comp t h₂ h₁
  apply HasDerivAt.congr ?_ this
  ext z
  simp

noncomputable def Lp_pow_p_path'' (x y : LpSpace p d) : ℝ → ℝ :=
  fun t => ∑ i, p * (p - 1) * |x i + t * (y i - x i)| ^ (p - 2)
    * (y i - x i) ^ 2

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
lemma hasDerivAt_Lp_pow_p_path' (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t : ℝ,
    HasDerivAt (Lp_pow_p_path' x y) (Lp_pow_p_path'' x y t) t := by
  intro t
  unfold Lp_pow_p_path'
  apply HasDerivAt.fun_sum
  intro i hi
  set δ := y i - x i
  let g₁ := fun y : ℝ => p * |y| ^ (p - 2) * y
  let g₁' := fun y : ℝ => p * (p - 1) * |y| ^ (p - 2)
  have hg₁ : ∀ y, HasDerivAt g₁ (g₁' y) y := by
    intro y
    apply hasDeriveAt_hasDerivAt_abs_pow
    linarith
  let g₂ := fun y : ℝ => δ
  have hg₂ : ∀ y, HasDerivAt g₂ 0 y := by
    intro y
    apply hasDerivAt_const
  let g₃ := fun t => x i + t * δ
  let g₃' := fun t : ℝ => δ
  have hg₃ : ∀ t, HasDerivAt g₃ (g₃' t) t := by
    intro t
    apply HasDerivAt.const_add
    have := (hasDerivAt_id' t).mul_const δ
    simp at this
    exact this

  apply HasDerivAt.congr (f := (g₁ ∘ g₃) * g₂)
  ext z
  simp [g₁, g₂, g₃]
  have := HasDerivAt.comp t (hg₁ (g₃ t)) (hg₃ t)
  have := HasDerivAt.mul this (hg₂ t)
  apply HasDerivAt.congr_deriv this
  simp [g₁, g₂, g₃, g₁', g₃']
  ring

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
lemma bdd_Lp_pow_path'' (x y : LpSpace p d) (t : ℝ) (hp : 2 < p) :
  Lp_pow_p_path'' x y t ≤
    p * (p - 1) * ‖path x y t‖ ^ (p - 2) * ‖y - x‖ ^ 2 := by
  simp [Lp_pow_p_path'']
  conv_lhs =>
    congr; rfl; ext i; rw [mul_assoc, mul_assoc]
  rw [←mul_sum, ←mul_sum, mul_assoc, mul_assoc]
  grw [Real.inner_le_Lp_mul_Lq (p := p / ↑(p - 2)) (q := p / (2 : ℕ))]
  apply le_of_eq
  simp
  apply Or.inl
  apply Or.inl
  have h₁ : ↑(p - 2) ≠ (0 : ℝ) := by apply ne_of_gt; simp; linarith
  have h₂ : ↑(2 : ℕ) ≠ (0 : ℝ) := by simp
  conv_lhs =>
    congr; congr; congr; rfl; ext i
    rw [←Real.rpow_natCast_mul, mul_div_cancel₀]
    rfl
    exact h₁
    apply abs_nonneg
    rw [div_eq_mul_inv, mul_comm]
    rfl
    congr; congr; rfl; ext i
    rw [←sq_abs, ←Real.rpow_natCast_mul]
    simp
    rw [mul_div_cancel₀]
    rfl
    exact h₂
    apply abs_nonneg
    rw [div_eq_mul_inv, mul_comm]
  rw [Real.rpow_mul, Real.rpow_mul]
  rw [PiLp.norm_eq_sum, PiLp.norm_eq_sum]
  simp [path]
  simp; linarith
  simp; linarith
  apply sum_nonneg; intro i hi; apply rpow_nonneg; apply abs_nonneg
  apply sum_nonneg; intro i hi; apply rpow_nonneg; apply abs_nonneg
  simp; linarith
  constructor
  simp
  rw [Nat.cast_sub]
  ring_nf
  apply mul_inv_cancel₀
  simp; linarith; linarith
  apply div_pos
  simp; linarith; simp; linarith
  apply div_pos
  simp; linarith; simp

lemma unfold_half_sq_Lp_path (x y : LpSpace p d) :
  half_sq_Lp ∘ path x y = (2⁻¹ : ℝ) • (Lp_pow_p_path x y) ^ (2 / (p : ℝ)) := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) := by infer_instance
  have hp := hp.elim
  simp at hp

  ext t
  simp [half_sq_Lp, Lp_pow_p_path]
  rw [←Real.rpow_natCast_mul, mul_div_cancel₀]
  simp

  simp
  linarith
  apply norm_nonneg

lemma continuousOn_half_sq_Lp_path {x y : LpSpace p d} :
  ContinuousOn (half_sq_Lp ∘ path x y) (Set.Icc 0 1) := by
  rw [unfold_half_sq_Lp_path x y]
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.rpow_const
  apply continuousOn_Lp_pow_p_path
  intro t ht
  apply Or.inr
  apply div_nonneg
  simp
  simp

noncomputable def half_sq_Lp_path' (x y : LpSpace p d) : ℝ → ℝ :=
  (p⁻¹ : ℝ) • Lp_pow_p_path x y ^ (2 / (p : ℝ) - 1) * Lp_pow_p_path' x y

lemma continuousOn_half_sq_Lp_path' {x y : LpSpace p d} :
  (∀ t ∈ Set.Icc (0 : ℝ) 1, path x y t ≠ 0) →
  ContinuousOn (half_sq_Lp_path' x y) (Set.Icc 0 1) := by
  intro ht
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.rpow_const
  apply continuousOn_Lp_pow_p_path
  intro t ht'
  apply Or.inl
  apply Lp_pow_p_path_ne_zero
  apply ht t ht'
  apply continuousOn_Lp_pow_p_path'

lemma hasDerivAt_half_sq_Lp_path (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t : ℝ, path x y t ≠ 0 → HasDerivAt
    (half_sq_Lp ∘ path x y) (half_sq_Lp_path' x y t) t := by
  intro t ht
  rw [unfold_half_sq_Lp_path x y]
  have := (hasDerivAt_Lp_pow_p_path hp x y t)
  have := this.rpow_const (p := 2 / (p : ℝ)) ?_
  have := this.const_mul (2⁻¹ : ℝ)
  apply HasDerivAt.congr_congr this
  ext t
  simp
  rw [half_sq_Lp_path']
  simp
  ring
  apply Or.inl
  apply Lp_pow_p_path_ne_zero
  exact ht

noncomputable def half_sq_Lp_path'' (x y : LpSpace p d) : ℝ → ℝ :=
  (p⁻¹ : ℝ) • ((2 / (p : ℝ) - 1) • Lp_pow_p_path x y ^ (2 / (p : ℝ) - 2) * Lp_pow_p_path' x y ^ 2 + Lp_pow_p_path x y ^ (2 / (p : ℝ) - 1) * Lp_pow_p_path'' x y)

lemma hasDerivAt_half_sq_Lp_path' (hp : 2 ≤ p) (x y : LpSpace p d) :
  ∀ t, path x y t ≠ 0 → HasDerivAt
    (half_sq_Lp_path' x y) (half_sq_Lp_path'' x y t) t := by
  intro t ht
  unfold half_sq_Lp_path'
  apply HasDerivAt.congr_deriv
  apply HasDerivAt.mul
  apply HasDerivAt.const_mul
  apply HasDerivAt.rpow_const
  apply hasDerivAt_Lp_pow_p_path
  exact hp
  apply Or.inl
  apply Lp_pow_p_path_ne_zero
  exact ht
  apply hasDerivAt_Lp_pow_p_path'
  exact hp
  rw [half_sq_Lp_path'']
  simp
  rw [mul_add]
  nth_rw 4 [←mul_assoc]
  simp
  rw [mul_assoc]
  simp
  apply Or.inl
  ring_nf

lemma bdd_half_sq_Lp_path'' (x y : LpSpace p d) (t : ℝ) (hp : 2 < p) :
  path x y t ≠ 0 → half_sq_Lp_path'' x y t ≤
    (p - 1) * 2 * half_sq_Lp (x - y) := by
  intro hxy
  simp [half_sq_Lp_path'']
  rw [mul_add, add_comm]
  apply add_le_of_le_of_nonpos
  grw [bdd_Lp_pow_path'']
  apply le_of_eq
  move_mul [←(p : ℝ)]
  rw [mul_inv_cancel₀]
  move_mul [(p : ℝ) - 1]
  simp
  apply Or.inl
  simp [Lp_pow_p_path]
  rw [←Real.rpow_natCast_mul, mul_sub, mul_div_cancel₀, ←Real.rpow_add_natCast]
  simp
  rw [Nat.cast_sub, sub_add_sub_cancel]
  simp [half_sq_Lp]
  rw [←neg_sub, norm_neg]
  linarith
  simp [hxy]
  simp; linarith
  apply norm_nonneg
  simp; linarith
  unfold Lp_pow_p_path
  apply rpow_nonneg
  apply rpow_nonneg
  apply norm_nonneg
  linarith
  apply le_of_neg_le_neg
  rw [neg_mul_eq_mul_neg, neg_mul_eq_neg_mul, neg_sub]
  simp
  apply mul_nonneg
  simp
  apply mul_nonneg
  rw [sub_div']
  apply div_nonneg
  simp; linarith
  simp
  simp; linarith
  apply mul_nonneg
  apply rpow_nonneg
  unfold Lp_pow_p_path
  apply rpow_nonneg
  apply norm_nonneg
  apply sq_nonneg

lemma smooth_half_sq_Lp_ne (hp : 2 < p) :
  ∀ (x y : LpSpace p d), (∀ t ∈ Set.Icc (0 : ℝ) 1, path x y t ≠ 0) →
    half_sq_Lp y ≤
      half_sq_Lp x + ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ + (p - 1) * half_sq_Lp (y - x) := by
  intro x y hxy
  have :
    half_sq_Lp_path' x y 0 = ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ := by
    -- Unfold LHS: half_sq_Lp_path' x y = (p⁻¹ : ℝ) • Lp_pow_p_path x y ^ (2 / p - 1) * Lp_pow_p_path' x y
    simp only [half_sq_Lp_path', Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.pow_apply]
    -- At t = 0: path x y 0 = x, Lp_pow_p_path x y 0 = ‖x‖^p
    have hpath0 : path x y 0 = x := by simp [path]
    have hLp_pow_0 : Lp_pow_p_path x y 0 = ‖x‖ ^ (p : ℝ) := by
      simp [Lp_pow_p_path, hpath0]
    have hLp_pow'_0 : Lp_pow_p_path' x y 0 =
        ∑ i, p * |x.ofLp i| ^ (p - 2) * x.ofLp i * (y.ofLp i - x.ofLp i) := by
      simp [Lp_pow_p_path']
    rw [hLp_pow_0, hLp_pow'_0]
    -- Simplify LHS: p⁻¹ * (‖x‖^p)^(2/p - 1) * (∑ i, p * |x.ofLp i|^(p-2) * x.ofLp i * (y.ofLp i - x.ofLp i))
    -- Use Real.rpow_mul to simplify (‖x‖ ^ p) ^ (2 / p - 1) = ‖x‖ ^ (p * (2/p - 1)) = ‖x‖ ^ (2 - p)
    have hp_ne : (p : ℝ) ≠ 0 := by simp; linarith
    rw [←Real.rpow_mul (norm_nonneg _)]
    have hexp : (p : ℝ) * (2 / (p : ℝ) - 1) = 2 - (p : ℝ) := by
      field_simp
    rw [hexp]
    -- Now LHS is: (↑p)⁻¹ * ‖x‖^(2 - p) * (∑ i, ↑p * |x.ofLp i|^(p-2) * x.ofLp i * (y.ofLp i - x.ofLp i))
    -- Unfold RHS using inner product
    rw [toL2, toL2, half_sq_Lp', PiLp.inner_apply]
    simp only [WithLp.ofLp_sub, Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    -- Distribute the scalar into the sum
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    -- Both sides have the same terms, just arranged differently
    -- Need to equate |x.ofLp i|^(p-2 : ℕ) with |x.ofLp i|^((p : ℝ) - 2)
    have hpow_eq : |x.ofLp i| ^ (p - 2) = |x.ofLp i| ^ ((p : ℝ) - 2) := by
      rw [← Real.rpow_natCast |x.ofLp i| (p - 2)]
      congr 1
      simp [Nat.cast_sub hp.le]
    simp only [hpow_eq]
    -- Goal: (↑p)⁻¹ * ‖x‖^(2-↑p) * (↑p * ... * (y.ofLp i - x.ofLp i)) = (y.ofLp i - x.ofLp i) * (...)
    field_simp
  rw [←this]

  let I := Set.Ioo (0 : ℝ) 1
  have hI : ∀ t ∈ I, path x y t ≠ 0 := by
    intro t ht
    apply hxy t ?_
    simp [I] at ht
    exact ⟨ht.1.le, ht.2.le⟩

  let φ := half_sq_Lp ∘ path x y
  let φ' := half_sq_Lp_path' x y
  let φ'' := half_sq_Lp_path'' x y
  let f := fun t => φ t - φ 0 - φ' 0 * t
  let f' := fun t => φ' t - φ' 0
  have hfDeriv : ∀ t ∈ I, HasDerivAt f (f' t) t := by
    intro t ht
    apply HasDerivAt.congr_deriv
    apply HasDerivAt.sub
    apply HasDerivAt.sub
    apply hasDerivAt_half_sq_Lp_path
    linarith
    apply hI t ht
    apply hasDerivAt_const
    apply HasDerivAt.const_mul
    apply hasDerivAt_id
    simp [f', φ']
  let C := φ 1 - φ 0 - φ' 0
  let g := fun t => f t - C * t ^2
  let g' := fun t => f' t - 2 * C * t
  have hgDeriv : ∀ t ∈ I, HasDerivAt g (g' t) t := by
    intro t ht
    apply HasDerivAt.congr_deriv
    apply HasDerivAt.sub
    apply hfDeriv t ht
    apply HasDerivAt.const_mul
    apply HasDerivAt.pow
    apply hasDerivAt_id
    simp [g', f', φ']
    ring

  have := exists_hasDerivAt_eq_slope g g' (a := 0) (b := 1) (by simp) ?_ hgDeriv
  obtain ⟨z₁, hz₁I, hz₁⟩ := this
  simp at hz₁I
  simp [g, f, C, g'] at hz₁

  let h := fun t => f' t - 2 * C * t
  let h' := fun t => φ'' t - 2 * C
  have hhDeriv : ∀ t ∈ Set.Ioo 0 z₁, HasDerivAt h (h' t) t := by
    intro t ht
    apply HasDerivAt.congr_deriv
    apply HasDerivAt.sub
    unfold f'
    apply HasDerivAt.sub
    apply hasDerivAt_half_sq_Lp_path'
    linarith
    apply hxy
    simp at ht ⊢
    constructor
    linarith
    linarith
    apply hasDerivAt_const
    apply HasDerivAt.const_mul
    apply hasDerivAt_id
    simp [h', φ'']

  have := exists_hasDerivAt_eq_slope h h' (a := 0) (b := z₁) hz₁I.1 ?_ hhDeriv
  obtain ⟨z₂, hz₂I, hz₂⟩ := this
  simp at hz₂I
  have : h 0 = 0 := by
    simp [h, f']
  rw [this] at hz₂
  have : h z₁ = 0 := by
    simp [h, C]
    exact hz₁
  rw [this] at hz₂
  simp at hz₂
  simp [h', C] at hz₂
  have := eq_of_sub_eq_zero hz₂
  have : φ 1 = φ 0 + φ' 0 * 1 + 1 / 2 * φ'' z₂ := by
    rw [this]
    ring
  simp [φ, φ', φ'', path] at this
  rw [this]
  apply add_le_add_three
  rfl
  rfl
  grw [bdd_half_sq_Lp_path'' x y z₂]
  unfold half_sq_Lp
  apply le_of_eq
  rw [←norm_neg, neg_sub]
  ring

  linarith
  apply hxy
  simp; constructor; linarith; linarith

  simp [h, f', φ']
  apply ContinuousOn.sub
  apply ContinuousOn.sub
  apply ContinuousOn.mono (by apply continuousOn_half_sq_Lp_path' hxy)
  intro t ht
  simp at ht ⊢
  constructor; linarith; linarith
  apply continuousOn_const
  apply ContinuousOn.mul
  apply continuousOn_const
  apply continuousOn_id
  simp [g, f, φ, φ']
  apply ContinuousOn.sub
  apply ContinuousOn.sub
  apply ContinuousOn.sub
  apply continuousOn_half_sq_Lp_path
  apply continuousOn_const
  apply ContinuousOn.mul
  apply continuousOn_const
  apply continuousOn_id
  apply ContinuousOn.mul
  apply continuousOn_const
  apply ContinuousOn.pow
  apply continuousOn_id

end smooth

theorem smooth_half_sq_Lp (hp : 2 ≤ p) :
  ∀ (x y : LpSpace p d),
    half_sq_Lp y ≤ half_sq_Lp x + ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ + (p - 1) * half_sq_Lp (y - x) := by
  have hFact : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  by_cases hp2 : 2 = p
  case pos =>
    -- Case p = 2: Use inner product space identity
    intro x y
    subst hp2
    simp only [half_sq_Lp, toL2, half_sq_Lp']
    apply (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp
    simp_rw [mul_add]
    simp only [Nat.cast_ofNat, sub_self, Real.rpow_zero, one_mul, mul_one]
    -- Simplify LHS and RHS
    have hlhs : 2 * (1 / 2 * ‖y‖ ^ 2) = ‖y‖ ^ 2 := by ring
    have hrhs1 : 2 * (1 / 2 * ‖x‖ ^ 2) = ‖x‖ ^ 2 := by ring
    have hrhs3 : 2 * ((2 - 1) * (1 / 2 * ‖y - x‖ ^ 2)) = ‖y - x‖ ^ 2 := by ring
    rw [hlhs, hrhs1, hrhs3]
    -- Key: y = x + (y - x), and for p=2 we use E d which has inner product structure
    have heq : y = x + (y - x) := by simp
    conv_lhs => rw [heq]
    -- Convert to E d where we have InnerProductSpace
    let x' : E d := WithLp.toLp 2 x.ofLp
    let y' : E d := WithLp.toLp 2 y.ofLp
    let diff' : E d := WithLp.toLp 2 (y - x).ofLp
    -- Use norm_add_sq_real on E d
    have hexpand := norm_add_sq_real (F := E d) x' diff'
    -- Norms are preserved: ‖x‖ = ‖x'‖, ‖y-x‖ = ‖diff'‖, ‖x+(y-x)‖ = ‖x'+diff'‖
    have hnorm_x : ‖x‖ = ‖x'‖ := by simp only [x', WithLp.toLp_ofLp]
    have hnorm_diff : ‖y - x‖ = ‖diff'‖ := by simp only [diff', WithLp.toLp_ofLp]
    have hnorm_sum : ‖x + (y - x)‖ = ‖x' + diff'‖ := by
      have heq_args : x + (y - x) = x' + diff' := by
        ext i
        simp only [x', diff', WithLp.ofLp_add, Pi.add_apply]
      rw [heq_args]
    -- The inner product in the goal uses toL2
    have hinner_eq : ⟪WithLp.toLp 2 (fun i => x.ofLp i), WithLp.toLp 2 (y - x).ofLp⟫ = ⟪x', diff'⟫_ℝ := by
      rfl
    rw [hinner_eq, hnorm_x, hnorm_diff, hnorm_sum]
    linarith
  case neg =>
    -- Case p > 2: Defer to smooth_half_sq_Lp_ne and limit argument
    have hp' : 2 < p := lt_of_le_of_ne hp hp2
    intro x y
    by_cases hxy : ∀ t ∈ Set.Icc (0 : ℝ) 1, path x y t ≠ 0
    case pos =>
      exact smooth_half_sq_Lp_ne hp' x y hxy
    -- If the path passes through 0, use a limiting argument
    push Not at hxy
    obtain ⟨t, htI, htx⟩ := hxy
    by_cases hx : x = 0
    case pos =>
      simp only [half_sq_Lp, toL2, half_sq_Lp']
      rw [hx]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        sub_zero, zero_add]
      have hp2_ne : 2 - (p : ℝ) ≠ 0 := by
        have : (2 : ℝ) < p := Nat.ofNat_lt_cast.mpr hp'
        linarith
      have hpp2_ne : (p : ℝ) - 2 ≠ 0 := by
        have : (2 : ℝ) < p := Nat.ofNat_lt_cast.mpr hp'
        linarith
      -- Simplify: 0^(2-p) = 0, |0|^(p-2) = 0, etc. All terms in the gradient become 0
      have hgrad_zero : (fun i => (0 : ℝ) ^ (2 - (p : ℝ)) * |WithLp.ofLp (0 : LpSpace p d) i| ^ ((p : ℝ) - 2) * WithLp.ofLp (0 : LpSpace p d) i) = fun _ => 0 := by
        ext i
        simp only [WithLp.ofLp_zero, Pi.zero_apply, abs_zero, Real.zero_rpow hpp2_ne, mul_zero]
      -- The gradient at 0 is the zero vector
      have hgrad_is_zero : (WithLp.toLp 2 fun i => (0 : ℝ) ^ (2 - (p : ℝ)) * |WithLp.ofLp (0 : LpSpace p d) i| ^ ((p : ℝ) - 2) * WithLp.ofLp (0 : LpSpace p d) i) = 0 := by
        rw [hgrad_zero]
        rfl
      rw [hgrad_is_zero]
      simp only [inner_zero_left, zero_add]
      apply le_mul_of_one_le_left
      · positivity
      · apply le_sub_iff_add_le.mpr
        rw [one_add_one_eq_two]
        have : (2 : ℝ) ≤ p := Nat.ofNat_le_cast.mpr hp
        linarith
    -- x ≠ 0 case with path through 0 - use perturbation argument
    have htpos : 0 < t := by
      by_contra h
      simp only [not_lt] at h
      simp only [Set.mem_Icc] at htI
      have ht0 := eq_of_le_of_ge htI.1 h
      simp only [path] at htx
      rw [← ht0] at htx
      simp only [zero_smul, add_zero] at htx
      exact hx htx
    by_cases hd0 : d = 0
    case pos =>
      subst hd0
      simp only [half_sq_Lp]
      -- For d = 0, all norms are 0
      have hp_real_pos : (0 : ℝ) < p := by simp; omega
      have hnorm0 : ∀ z : LpSpace p 0, ‖z‖ = 0 := by
        intro z
        rw [PiLp.norm_eq_sum (p := p) (by simp; linarith)]
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
        have h_toReal : (p : ℝ≥0∞).toReal = (p : ℝ) := by simp
        rw [h_toReal]
        have h_ne : 1 / (p : ℝ) ≠ 0 := by
          apply one_div_ne_zero
          linarith
        rw [Real.zero_rpow h_ne]
      rw [hnorm0, hnorm0, hnorm0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add]
      -- The inner product is also 0 for d = 0
      have hinner0 : ⟪toL2 (half_sq_Lp' x), toL2 (y - x)⟫ = 0 := by
        simp only [toL2, half_sq_Lp']
        -- For d = 0, the inner product on E 0 is trivially 0
        rw [PiLp.inner_apply]
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [hinner0]
      norm_num
    by_cases hd1 : d ≤ 1
    case pos =>
      -- d = 1 case: reduce to 1-dimensional problem
      have hd' : d = 1 := by omega
      subst hd'
      simp only [half_sq_Lp, toL2, half_sq_Lp']
      -- For d = 1, the unique index is 0 : Fin 1
      have hnorm_eq : ∀ z : LpSpace p 1, ‖z‖ = |z.ofLp 0| := by
        intro z
        rw [PiLp.norm_eq_sum (p := p) (by simp; linarith)]
        simp only [Fin.sum_univ_one, Fin.isValue]
        have h_toReal : (p : ℝ≥0∞).toReal = (p : ℝ) := by simp
        rw [h_toReal]
        have hp_ne : (p : ℝ) ≠ 0 := by simp; linarith
        have hp_pos : (0 : ℝ) < p := by simp; linarith
        -- (‖z.ofLp 0‖ ^ ↑p) ^ (1/↑p) = |z.ofLp 0| since ‖·‖ = |·| for reals
        have hnorm_abs : ‖z.ofLp 0‖ = |z.ofLp 0| := Real.norm_eq_abs _
        rw [hnorm_abs]
        -- (|z.ofLp 0| ^ ↑p) ^ (1/↑p) = |z.ofLp 0|
        rw [← Real.rpow_mul (abs_nonneg _)]
        simp only [mul_one_div_cancel hp_ne, Real.rpow_one]
      simp_rw [hnorm_eq, WithLp.ofLp_sub, Pi.sub_apply]
      apply (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp
      simp only [mul_add]
      have heq : |y.ofLp 0| = |x.ofLp 0 + (y.ofLp 0 - x.ofLp 0)| := by
        congr 1
        ring
      conv_lhs => rw [heq]
      -- Now goal is |x.ofLp 0 + (y.ofLp 0 - x.ofLp 0)|² ≤ ... with absolute values
      -- Use the fact that for p > 2, the inequality holds
      -- Simplify inner product for d=1
      have hinner : ⟪WithLp.toLp 2 fun i => |x.ofLp 0| ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i,
                     WithLp.toLp 2 (y.ofLp - x.ofLp)⟫ =
                    |x.ofLp 0| ^ (2 - (p : ℝ)) * |x.ofLp 0| ^ ((p : ℝ) - 2) * x.ofLp 0 * (y.ofLp 0 - x.ofLp 0) := by
        rw [PiLp.inner_apply, Fin.sum_univ_one]
        simp only [Fin.isValue, Pi.sub_apply, RCLike.inner_apply, conj_trivial]
        ring
      rw [hinner]
      -- Simplify |x.ofLp 0|^(2-p) * |x.ofLp 0|^(p-2) = 1 when x.ofLp 0 ≠ 0, or = 0 when x.ofLp 0 = 0
      by_cases hx0 : x.ofLp 0 = 0
      · -- x.ofLp 0 = 0 case
        simp only [hx0, abs_zero, zero_mul, mul_zero, zero_add, sub_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        have hp_minus_1_ge_1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (2 : ℝ) < p := Nat.ofNat_lt_cast.mpr hp'
          linarith
        -- Goal: 2 * (1/2 * |y.ofLp 0|²) ≤ 2 * ((p-1) * (1/2 * |y.ofLp 0|²))
        have h_simpl : 2 * (1 / 2 * |y.ofLp 0| ^ 2) = |y.ofLp 0| ^ 2 := by ring
        have h_simpl' : 2 * (((p : ℝ) - 1) * (1 / 2 * |y.ofLp 0| ^ 2)) = ((p : ℝ) - 1) * |y.ofLp 0| ^ 2 := by ring
        rw [h_simpl, h_simpl']
        apply le_mul_of_one_le_left (sq_nonneg _) hp_minus_1_ge_1
      · -- x.ofLp 0 ≠ 0 case
        have habs_pos : 0 < |x.ofLp 0| := abs_pos.mpr hx0
        have hpow_eq : |x.ofLp 0| ^ (2 - (p : ℝ)) * |x.ofLp 0| ^ ((p : ℝ) - 2) = 1 := by
          rw [← Real.rpow_add habs_pos]
          simp
        simp only [hpow_eq, one_mul]
        -- Now: |x + (y-x)|² ≤ |x|² + 2 * x * (y-x) + (p-1) * |y-x|²
        -- LHS = |y|², and we use the identity |y|² = |x|² + 2*x*(y-x) + |y-x|² for reals
        -- Since p > 2, we have (p-1) > 1, so (p-1)|y-x|² ≥ |y-x|²
        have h1D : |x.ofLp 0 + (y.ofLp 0 - x.ofLp 0)| ^ 2 =
                   |x.ofLp 0| ^ 2 + 2 * (x.ofLp 0 * (y.ofLp 0 - x.ofLp 0)) + |y.ofLp 0 - x.ofLp 0| ^ 2 := by
          have hy_eq : x.ofLp 0 + (y.ofLp 0 - x.ofLp 0) = y.ofLp 0 := by ring
          rw [hy_eq]
          have hx_eq : y.ofLp 0 = x.ofLp 0 + (y.ofLp 0 - x.ofLp 0) := by ring
          calc |y.ofLp 0| ^ 2 = y.ofLp 0 ^ 2 := sq_abs _
            _ = (x.ofLp 0 + (y.ofLp 0 - x.ofLp 0)) ^ 2 := by rw [← hx_eq]
            _ = x.ofLp 0 ^ 2 + 2 * (x.ofLp 0 * (y.ofLp 0 - x.ofLp 0)) + (y.ofLp 0 - x.ofLp 0) ^ 2 := by ring
            _ = |x.ofLp 0| ^ 2 + 2 * (x.ofLp 0 * (y.ofLp 0 - x.ofLp 0)) + |y.ofLp 0 - x.ofLp 0| ^ 2 := by
                rw [sq_abs, sq_abs]
        rw [h1D]
        have hp_minus_1_ge_1 : (1 : ℝ) ≤ p - 1 := by
          have : (2 : ℝ) < p := Nat.ofNat_lt_cast.mpr hp'
          linarith
        have h_last : |y.ofLp 0 - x.ofLp 0| ^ 2 ≤ ((p : ℝ) - 1) * (1 / 2 * |y.ofLp 0 - x.ofLp 0| ^ 2) * 2 := by
          have hrhs : ((p : ℝ) - 1) * (1 / 2 * |y.ofLp 0 - x.ofLp 0| ^ 2) * 2 =
                      ((p : ℝ) - 1) * |y.ofLp 0 - x.ofLp 0| ^ 2 := by ring
          rw [hrhs]
          apply le_mul_of_one_le_left (sq_nonneg _) hp_minus_1_ge_1
        linarith
    case neg =>
      -- d ≥ 2: Use perturbation and limiting argument
      -- This case uses the fact that for x ≠ 0 with d ≥ 2, we can perturb y slightly
      -- in a direction orthogonal to x's nonzero components, creating paths y' n → y
      -- where each path x → y' n doesn't pass through 0, allowing us to apply
      -- smooth_half_sq_Lp_ne and take the limit.
      have hxne : ∃ i, x.ofLp i ≠ 0 := by
        by_contra h
        push Not at h
        have hx' : x = 0 := by
          ext i
          simp only [WithLp.ofLp_zero, Pi.zero_apply]
          exact h i
        exact hx hx'
      obtain ⟨i, hi⟩ := hxne
      have hjne : ∃ j, j ≠ i := by
        by_cases hi0 : (i : ℕ) = 0
        case pos =>
          have hd2 : 2 ≤ d := by omega
          let j := Fin.mk (n := d) 1 hd2
          use j
          apply (Fin.ne_iff_vne j i).mpr
          simp [hi0]
        case neg =>
          let j := Fin.mk (n := d) 0 (by omega)
          use j
          apply (Fin.ne_iff_vne j i).mpr
          simp
          by_contra h
          exact hi0 h.symm
      obtain ⟨j, hj⟩ := hjne
      let u : LpSpace p d := WithLp.toLp p (fun k => if j = k then 1 else 0)
      let y' := fun k : ℕ => y + (1 / ((k : ℝ) + 1)) • u
      have hxy' : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) 1, path x (y' k) s ≠ 0 := by
        intro k
        by_contra h
        push Not at h
        obtain ⟨s', hs'I, hs'⟩ := h
        have h₁ := congrFun (congrArg WithLp.ofLp hs') i
        simp only [path, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub, Pi.add_apply,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul, WithLp.ofLp_zero, Pi.zero_apply] at h₁
        simp only [y', WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, u] at h₁
        rw [if_neg hj] at h₁
        simp only [mul_zero, add_zero] at h₁
        have h₂ := congrFun (congrArg WithLp.ofLp htx) i
        simp only [path, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub, Pi.add_apply,
          Pi.smul_apply, Pi.sub_apply, smul_eq_mul, WithLp.ofLp_zero, Pi.zero_apply] at h₂
        rw [mul_sub, add_sub, add_comm, sub_eq_iff_eq_add, zero_add] at h₂
        have h₂' := (sub_eq_iff_eq_add.mpr h₂.symm).symm
        have hinv := congrArg (fun z => t⁻¹ * z) h₂'
        rw [←mul_assoc, inv_mul_cancel₀ (htpos.ne')] at hinv
        simp only [one_mul] at hinv
        rw [hinv] at h₁
        -- h₁ : x.ofLp i + s' * (t⁻¹ * (t * x.ofLp i - x.ofLp i) - x.ofLp i) = 0
        -- Let a = x.ofLp i. Then hinv says y.ofLp i = t⁻¹ * (t * a - a) = a - t⁻¹ * a
        -- So h₁ says: a + s' * ((a - t⁻¹ * a) - a) = 0
        --           = a + s' * (-t⁻¹ * a) = 0
        --           = a - s' * t⁻¹ * a = 0
        --           = a * (1 - s' * t⁻¹) = 0
        have ht_ne : t ≠ 0 := htpos.ne'
        have h₁' : x.ofLp i * (1 - s' * t⁻¹) = 0 := by
          have hinv_simp : t⁻¹ * (t * x.ofLp i - x.ofLp i) = x.ofLp i - t⁻¹ * x.ofLp i := by
            field_simp
          rw [hinv_simp] at h₁
          linarith
        rw [mul_eq_zero] at h₁'
        rcases h₁' with hl | hr
        case inl => exact hi hl
        case inr =>
          have heq : s' * t⁻¹ = 1 := by linarith
          have hmul : s' = t := by field_simp at heq; linarith
          -- hmul : s' = t
          -- We have: hs' : path x (y' k) s' = 0 and htx : path x y t = 0
          -- With s' = t, we get path x (y' k) t = 0
          -- Subtracting, t • (y - y' k) = 0, so y = y' k
          -- But y' k = y + ε•u for ε > 0, contradiction
          rw [hmul] at hs'
          have hdiff : t • (y - y' k) = 0 := by
            simp only [path] at htx hs'
            have h1 : x + t • (y - x) = 0 := htx
            have h2 : x + t • (y' k - x) = 0 := hs'
            have hcalc : t • (y - y' k) = (x + t • (y - x)) - (x + t • (y' k - x)) := by
              simp only [smul_sub]
              abel
            rw [hcalc, h1, h2, sub_zero]
          rw [smul_eq_zero] at hdiff
          rcases hdiff with htfalse | hy_eq
          case inl => exact ht_ne htfalse
          case inr =>
            have hy'_def : y' k = y + (1 / ((k : ℝ) + 1)) • u := rfl
            rw [hy'_def, sub_add_cancel_left, neg_eq_zero, smul_eq_zero] at hy_eq
            rcases hy_eq with heps_zero | hu_zero
            case inl =>
              have hk_pos : 0 < 1 / ((k : ℝ) + 1) := by positivity
              linarith
            case inr =>
              have hu_j := congrFun (congrArg WithLp.ofLp hu_zero) j
              simp only [WithLp.ofLp_zero, Pi.zero_apply, u] at hu_j
              simp only [if_true] at hu_j
              exact one_ne_zero hu_j
      have hy' : Tendsto y' atTop (𝓝 y) := by
        apply tendsto_iff_norm_sub_tendsto_zero.mpr
        simp only [y']
        have heq : ∀ k : ℕ, ‖y + (1 / ((k : ℝ) + 1)) • u - y‖ = 1 / ((k : ℝ) + 1) * ‖u‖ := by
          intro k
          rw [add_sub_cancel_left, norm_smul, norm_eq_abs]
          have hk_nonneg : 0 ≤ 1 / ((k : ℝ) + 1) := by
            apply div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
            linarith [Nat.cast_nonneg (α := ℝ) k]
          rw [abs_of_nonneg hk_nonneg]
        simp_rw [heq]
        have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖u‖
        simp only [zero_mul] at this
        exact this
      have hlhs := (continuous_half_sq_Lp.tendsto y).comp hy'
      have hcont_toL2 : Continuous (toL2 (p := p) (d := d)) := by
        unfold toL2
        have h1 := (PiLp.lipschitzWith_ofLp p (fun _ : Fin d => ℝ)).continuous
        have h2 := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin d => ℝ)).continuous
        exact h2.comp h1
      have hcont : Continuous fun z => half_sq_Lp x +
        ⟪toL2 (half_sq_Lp' x), toL2 (z - x)⟫ +
        (p - 1) * half_sq_Lp (z - x) := by
        apply Continuous.add
        apply Continuous.add
        apply continuous_const
        apply Continuous.inner
        apply continuous_const
        apply hcont_toL2.comp
        apply Continuous.sub continuous_id continuous_const
        apply Continuous.mul
        apply continuous_const
        apply continuous_half_sq_Lp.comp
        apply Continuous.sub continuous_id continuous_const
      have hrhs := (hcont.tendsto y).comp hy'
      apply le_of_tendsto_of_tendsto' hlhs hrhs
      intro k
      exact smooth_half_sq_Lp_ne hp' x (y' k) (hxy' k)

section norm_equivalence

lemma Lp_le_L2 {x : LpSpace p d} (hp : 2 ≤ p) :
  ‖x‖ ≤ ‖toL2 x‖ := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  conv_rhs => rw [←one_mul (a := ‖toL2 x‖)]
  by_cases hx : ‖toL2 x‖ = 0
  case pos =>
    simp [toL2] at hx
    simp [hx]
  apply (inv_mul_le_iff₀' ?_).mp
  rw [PiLp.norm_eq_sum (p := p)]
  simp
  have : (‖toL2 x‖⁻¹ ^ p) ^ ((p : ℝ))⁻¹ = ‖toL2 x‖⁻¹ := by
    rw [←Real.rpow_natCast_mul, mul_inv_cancel₀]
    simp
    simp; linarith
    simp
  rw [←this]
  rw [←Real.mul_rpow, mul_sum]
  apply Real.rpow_le_one
  apply sum_nonneg; intro i hi; positivity
  conv_lhs => congr; rfl; ext i; rw [←mul_pow]

  have : ‖toL2 (‖toL2 x‖⁻¹ • x)‖ = 1 := by
    simp [toL2]
    rw [norm_smul]
    simp
    apply inv_mul_cancel₀
    simp [toL2] at hx
    simp [hx]
  rw [PiLp.norm_eq_sum] at this
  simp at this
  nth_rw 2 [←one_div] at this
  rw [←Real.sqrt_eq_rpow, Real.sqrt_eq_one] at this
  nth_rw 1 [toL2] at this

  rw [←this]
  apply sum_le_sum
  simp
  intro i
  rw [←sq_abs, abs_mul, abs_inv]
  simp
  apply pow_le_pow_of_le_one
  positivity
  apply (sq_le_one_iff₀ (by positivity)).mp
  rw [←this]
  conv_rhs =>
    congr; rfl; ext i; simp
    rw [←sq_abs, abs_mul, abs_inv]
    simp
  apply single_le_sum (f := fun i => (‖toL2 x‖⁻¹ * |x i|) ^ 2)
  intro i hi; positivity
  simp
  linarith
  simp
  positivity
  positivity
  positivity
  simp
  linarith
  simp
  simp at hx
  exact hx

lemma L2_le_Lp (hp : 2 ≤ p) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : LpSpace p d, ‖toL2 x‖ ≤ C * ‖x‖ := by
  use ((d : ℝ) ^ (((p : ℝ) - 2) / p)) ^ (2⁻¹ : ℝ)
  constructor
  · positivity
  intro x
  simp only [toL2]
  by_cases hp2 : 2 = p
  case pos =>
    subst hp2
    simp only [WithLp.toLp_ofLp]
    -- When p = 2, the constant is (d^((2-2)/2))^(1/2) = (d^0)^(1/2) = 1^(1/2) = 1
    have hconst : ((d : ℝ) ^ ((((2 : ℕ) : ℝ) - 2) / (2 : ℕ))) ^ (2⁻¹ : ℝ) = 1 := by
      simp only [Nat.cast_ofNat, sub_self, zero_div, Real.rpow_zero, Real.one_rpow]
    rw [hconst, one_mul]
  case neg =>
    -- Use PiLp.norm_eq_sum to expand both norms
    have hp_pos : (0 : ℝ) < p := by simp; omega
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have hp_ne : (p : ℝ) ≠ 0 := by linarith
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    have hp' : 2 < p := lt_of_le_of_ne hp hp2
    -- Expand ‖toL2 x‖ = ‖WithLp.toLp 2 x.ofLp‖
    have htoL2_norm : ‖WithLp.toLp 2 x.ofLp‖ = (∑ i, |x.ofLp i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [PiLp.norm_eq_sum (p := 2) (by simp)]
      simp only [ENNReal.toReal_ofNat, one_div, Real.norm_eq_abs]
    -- Expand ‖x‖
    have hx_norm : ‖x‖ = (∑ i, |x.ofLp i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
      rw [PiLp.norm_eq_sum (p := p) (by simp; linarith)]
      simp only [one_div, Real.norm_eq_abs, ENNReal.toReal_natCast]
    rw [htoL2_norm, hx_norm]
    -- Apply Hölder's inequality: ∑|x_i|^2 ≤ (∑|x_i|^p)^(2/p) * d^((p-2)/p)
    have hHolder := Real.inner_le_Lp_mul_Lq
      (p := (p : ℝ) / 2) (q := (p : ℝ) / (p - 2))
      (f := fun i => |x.ofLp i| ^ 2) (g := fun _ => (1 : ℝ)) Finset.univ ?hpq
    case hpq =>
      refine ⟨?_, ?_, ?_⟩
      · -- 2/p + (p-2)/p = p/p = 1
        field_simp
        ring
      · apply div_pos (by linarith) h2_pos
      · have hp_lt : (2 : ℝ) < p := Nat.ofNat_lt_cast.mpr hp'
        apply div_pos (by linarith) (by linarith)
    simp only [mul_one, abs_one, Real.one_rpow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hHolder
    -- Simplify |abs(x_i)^2| = |x_i|^2 since |x_i|^2 ≥ 0
    have habs_pow2 : ∀ i, |((|x.ofLp i|) ^ 2)| = |x.ofLp i| ^ 2 := by
      intro i
      apply abs_of_nonneg
      apply sq_nonneg
    simp only [habs_pow2] at hHolder
    -- Simplify (|x_i|^2)^(p/2) = |x_i|^p
    have hsimp_pow : ∀ i, (|x.ofLp i| ^ 2) ^ ((p : ℝ) / 2) = |x.ofLp i| ^ (p : ℝ) := by
      intro i
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      simp only [Nat.cast_ofNat]
      field_simp
    simp only [hsimp_pow] at hHolder
    -- Convert ℕ exponent to ℝ exponent in the sum
    have hnat_to_real_pow : ∀ i, |x.ofLp i| ^ (2 : ℕ) = |x.ofLp i| ^ (2 : ℝ) := by
      intro i
      rw [← Real.rpow_natCast]
      simp
    simp only [hnat_to_real_pow] at hHolder
    -- Now raise both sides to the power 1/2
    have hsum_nonneg : 0 ≤ ∑ i, |x.ofLp i| ^ (2 : ℝ) := by
      apply Finset.sum_nonneg
      intro i _
      apply Real.rpow_nonneg (abs_nonneg _)
    have hrhs_nonneg : 0 ≤ (∑ i, |x.ofLp i| ^ (p : ℝ)) ^ (2 / (p : ℝ)) * (d : ℝ) ^ (((p : ℝ) - 2) / (p : ℝ)) := by
      apply mul_nonneg
      · apply Real.rpow_nonneg
        apply Finset.sum_nonneg
        intro i _
        apply Real.rpow_nonneg (abs_nonneg _)
      · apply Real.rpow_nonneg
        simp
    have hpow_mono := Real.rpow_le_rpow hsum_nonneg hHolder (by norm_num : (0 : ℝ) ≤ 1 / 2)
    -- Simplify: (∑|x_i|^2)^(1/2) ≤ ((∑|x_i|^p)^(1/(p/2)) * d^(1/(p/(p-2))))^(1/2)
    rw [Real.mul_rpow (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) _)
        (Real.rpow_nonneg (by simp) _)] at hpow_mono
    -- (a^(1/(p/2)))^(1/2) = a^(1/p)
    have hexp1 : (1 / ((p : ℝ) / 2)) * (1 / 2) = 1 / (p : ℝ) := by field_simp
    rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)), hexp1] at hpow_mono
    -- (d^(1/(p/(p-2))))^(1/2) = (d^((p-2)/p))^(1/2)
    have hexp2_eq : (1 : ℝ) / ((p : ℝ) / (↑p - 2)) = (↑p - 2) / ↑p := by field_simp
    rw [hexp2_eq] at hpow_mono
    have hexp2 : (((p : ℝ) - 2) / (p : ℝ)) * (1 / 2) = ((p : ℝ) - 2) / (p : ℝ) * 2⁻¹ := by ring
    rw [← Real.rpow_mul (by simp : (0 : ℝ) ≤ d), hexp2, Real.rpow_mul (by simp : (0 : ℝ) ≤ d)] at hpow_mono
    rw [mul_comm] at hpow_mono
    exact hpow_mono

-- NOTE: This notation converts the underlying function to the L∞ space
local notation (priority := 2000) "‖" x "‖∞" =>
  ‖WithLp.toLp ⊤ (WithLp.ofLp x)‖

lemma nnreal_toReal_sup_eq_sup'
  {ι} {s : Finset ι} (hs : s.Nonempty) {x : ι → ℝ≥0} :
  (s.sup x).toReal = s.sup' hs (fun i => (x i).toReal) := by
  obtain ⟨i, his, hi⟩ := exists_mem_eq_sup' hs x
  apply le_antisymm
  simp
  use i
  constructor
  exact his
  rw [←hi]
  intro j hj
  apply (le_sup'_iff hs).mpr
  use j
  simp
  intro j hj
  apply le_sup_of_le hj
  rfl

lemma infty_norm_eq_norm {α} [Fintype α] [Nonempty α] {f : α → ℝ} :
  ‖WithLp.toLp ⊤ f‖ = ‖f‖ :=
  PiLp.norm_toLp f

lemma Linfty_le_Lp {x : LpSpace p d} (hp : 1 ≤ p) :
  ‖x‖∞ ≤ ‖x‖ := by
  have hfact : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  -- ‖x‖∞ = ‖WithLp.toLp ⊤ (WithLp.ofLp x)‖ = ‖x.ofLp‖_Pi
  -- We need to show ‖x.ofLp‖_Pi ≤ ‖x‖
  rw [PiLp.norm_toLp]
  -- Use pi_norm_le_iff_of_nonneg: ‖f‖ ≤ r ↔ ∀ i, ‖f i‖ ≤ r (when r ≥ 0)
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  -- Now we need: ∀ i, ‖x.ofLp i‖ ≤ ‖x‖
  intro i
  exact PiLp.norm_apply_le x i

lemma Lp_le_Linfty {x : LpSpace p d} (hp : 1 ≤ p) :
  ‖x‖ ≤ (d : ℝ) ^ (1 / (p : ℝ)) * ‖x‖∞ := by
  have hfact : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  have hp_pos : (0 : ℝ) < p := by
    have : (1 : ℕ) ≤ p := hp
    have : (1 : ℝ) ≤ (p : ℝ) := Nat.one_le_cast.mpr this
    linarith
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  -- ‖x‖ = (∑ᵢ ‖x.ofLp i‖^p)^(1/p)
  have hp_toReal_pos : 0 < (p : ℝ≥0∞).toReal := by simp [hp_pos]
  rw [PiLp.norm_eq_sum hp_toReal_pos]
  simp only [ENNReal.toReal_natCast]
  -- ‖x‖∞ = ‖x.ofLp‖_Pi = sup over components
  rw [PiLp.norm_toLp]
  -- Each component ‖x.ofLp i‖ ≤ ‖x.ofLp‖_Pi
  have hcomp_le : ∀ i, ‖x.ofLp i‖ ≤ ‖x.ofLp‖ := fun i => norm_le_pi_norm (x.ofLp) i
  -- Sum bound: ∑ᵢ ‖x.ofLp i‖^p ≤ ∑ᵢ ‖x.ofLp‖^p = d * ‖x.ofLp‖^p
  have hsum_le : ∑ i : Fin d, ‖x.ofLp i‖ ^ (p : ℝ) ≤ d * ‖x.ofLp‖ ^ (p : ℝ) := by
    calc ∑ i : Fin d, ‖x.ofLp i‖ ^ (p : ℝ)
        ≤ ∑ i : Fin d, ‖x.ofLp‖ ^ (p : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          apply Real.rpow_le_rpow (norm_nonneg _) (hcomp_le i) (by linarith)
      _ = d * ‖x.ofLp‖ ^ (p : ℝ) := by simp [Finset.sum_const]
  -- Take p-th root of both sides
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, ‖x.ofLp i‖ ^ (p : ℝ) := by
    apply Finset.sum_nonneg
    intro i _
    apply Real.rpow_nonneg (norm_nonneg _)
  have hrhs_nonneg : 0 ≤ d * ‖x.ofLp‖ ^ (p : ℝ) := by
    apply mul_nonneg (by simp) (Real.rpow_nonneg (norm_nonneg _) _)
  have hroot := Real.rpow_le_rpow hsum_nonneg hsum_le (by positivity : 0 ≤ 1 / (p : ℝ))
  -- Simplify RHS: (d * ‖x.ofLp‖^p)^(1/p) = d^(1/p) * ‖x.ofLp‖
  rw [Real.mul_rpow (by simp : (0 : ℝ) ≤ d) (Real.rpow_nonneg (norm_nonneg _) _)] at hroot
  rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp_ne, Real.rpow_one] at hroot
  exact hroot

end norm_equivalence

section inner

lemma inner_gradient_half_sq_Lp_self (hp : 1 ≤ p) (x : LpSpace p d) :
  ⟪toL2 (half_sq_Lp' x), toL2 x⟫ = ‖x‖ ^ 2 := by
  have hfact : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  have hp_pos : (0 : ℝ) < p := by
    have : (1 : ℕ) ≤ p := hp
    have : (1 : ℝ) ≤ (p : ℝ) := Nat.one_le_cast.mpr this
    linarith
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  -- Expand the inner product using PiLp.inner_apply
  simp only [toL2, half_sq_Lp']
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  -- The sum is: ∑ i, (‖x‖^(2-p) * |x.ofLp i|^(p-2) * x.ofLp i) * x.ofLp i
  -- = ∑ i, ‖x‖^(2-p) * |x.ofLp i|^(p-2) * (x.ofLp i)^2
  -- = ‖x‖^(2-p) * ∑ i, |x.ofLp i|^(p-2) * |x.ofLp i|^2  (since (x.ofLp i)^2 = |x.ofLp i|^2)
  -- = ‖x‖^(2-p) * ∑ i, |x.ofLp i|^p
  -- = ‖x‖^(2-p) * ‖x‖^p  (by definition of Lp norm)
  -- = ‖x‖^2
  have h1 : (p : ℝ) - 2 + 2 = p := by ring
  -- Simplify each term in the sum
  have hterm : ∀ i, ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i * x.ofLp i
      = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ (p : ℝ) := by
    intro i
    -- x.ofLp i * x.ofLp i = |x.ofLp i|^2
    have hsq : x.ofLp i * x.ofLp i = |x.ofLp i| ^ (2 : ℝ) := by
      have h1 : x.ofLp i * x.ofLp i = (x.ofLp i) ^ 2 := by ring
      have h2 : |x.ofLp i| ^ 2 = (x.ofLp i) ^ 2 := sq_abs _
      rw [h1, ← h2, ← Real.rpow_natCast]
      simp only [Nat.cast_ofNat]
    -- |x.ofLp i|^(p-2) * |x.ofLp i|^2 = |x.ofLp i|^p
    have hp_sum_ne : ((p : ℝ) - 2) + 2 ≠ 0 := by linarith
    calc ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i * x.ofLp i
        = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * (x.ofLp i * x.ofLp i) := by ring
      _ = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * |x.ofLp i| ^ (2 : ℝ) := by rw [hsq]
      _ = ‖x‖ ^ (2 - (p : ℝ)) * (|x.ofLp i| ^ ((p : ℝ) - 2) * |x.ofLp i| ^ (2 : ℝ)) := by ring
      _ = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2 + 2) := by
          rw [← Real.rpow_add' (abs_nonneg _) hp_sum_ne]
      _ = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ (p : ℝ) := by ring_nf
  -- The goal sum has form: ∑ i, x.ofLp i * (‖x‖ ^ (2 - p) * |x.ofLp i| ^ (p - 2) * x.ofLp i)
  -- which equals ∑ i, ‖x‖ ^ (2 - p) * |x.ofLp i| ^ p by ring + hterm
  have hterm' : ∀ i, x.ofLp i * (‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i)
      = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ (p : ℝ) := by
    intro i
    calc x.ofLp i * (‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i)
        = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i * x.ofLp i := by ring
      _ = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ (p : ℝ) := hterm i
  simp_rw [hterm']
  -- Factor out ‖x‖^(2-p)
  rw [← Finset.mul_sum]
  -- The sum ∑ i, |x.ofLp i|^p = ‖x‖^p
  have hp_toReal_pos : 0 < (p : ℝ≥0∞).toReal := by simp [hp_pos]
  have hnorm_sum : ∑ i : Fin d, |x.ofLp i| ^ (p : ℝ) = ‖x‖ ^ (p : ℝ) := by
    have hnorm_eq := PiLp.norm_eq_sum hp_toReal_pos x
    simp only [ENNReal.toReal_natCast] at hnorm_eq
    -- ‖x‖ = (∑ i, ‖x.ofLp i‖^p)^(1/p)
    -- So ‖x‖^p = ∑ i, ‖x.ofLp i‖^p = ∑ i, |x.ofLp i|^p
    have : ‖x‖ ^ (p : ℝ) = (∑ i : Fin d, ‖x.ofLp i‖ ^ (p : ℝ)) ^ ((1 / (p : ℝ)) * (p : ℝ)) := by
      rw [hnorm_eq]
      rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
    rw [one_div_mul_cancel hp_ne, Real.rpow_one] at this
    rw [this]
    simp only [Real.norm_eq_abs]
  rw [hnorm_sum]
  -- ‖x‖^(2-p) * ‖x‖^p = ‖x‖^2
  have h2_ne : (2 - (p : ℝ)) + p ≠ 0 := by norm_num
  rw [← Real.rpow_add' (norm_nonneg _) h2_ne]
  norm_num

lemma inner_abs_gradient_half_sq_Lp_le (hp : 2 ≤ p) (x y: LpSpace p d) :
  ∑ i, |(half_sq_Lp' x).ofLp i| * |y.ofLp i| ≤ ‖x‖ * ‖y‖ := by
  have hfact : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  have hp_pos : (0 : ℝ) < p := by
    have : (2 : ℕ) ≤ p := hp
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.ofNat_le_cast.mpr this
    linarith
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (2 : ℕ) ≤ p := hp
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.ofNat_le_cast.mpr this
    linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1_pos
  have hp2_add : (p : ℝ) - 2 + 1 = p - 1 := by ring
  have hpm1_ne : ((p : ℝ) - 2 + 1) ≠ 0 := by rw [hp2_add]; exact hp1_ne
  -- Expand (half_sq_Lp' x).ofLp i = ‖x‖^(2-p) * |x.ofLp i|^(p-2) * x.ofLp i
  have hgrad : ∀ i, (half_sq_Lp' x).ofLp i = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 2) * x.ofLp i := by
    intro i
    simp only [half_sq_Lp', WithLp.ofLp_toLp]
  -- Simplify |grad_i| = ‖x‖^(2-p) * |x_i|^(p-1)
  have habs_grad : ∀ i, |(half_sq_Lp' x).ofLp i| = ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 1) := by
    intro i
    rw [hgrad]
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    -- Goal: ‖x‖^(2-p) * |x_i|^(p-2) * |x_i| = ‖x‖^(2-p) * |x_i|^(p-1)
    rw [mul_assoc]
    congr 1
    rw [← Real.rpow_add_one' (abs_nonneg _) hpm1_ne, hp2_add]
  -- Rewrite the sum using habs_grad
  have hsum_eq : ∑ i, |(half_sq_Lp' x).ofLp i| * |y.ofLp i| =
      ∑ i, ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 1) * |y.ofLp i| := by
    congr 1
    funext i
    rw [habs_grad]
  rw [hsum_eq]
  -- Factor out ‖x‖^(2-p)
  have hfactor : ∑ i, ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 1) * |y.ofLp i| =
      ‖x‖ ^ (2 - (p : ℝ)) * ∑ i, |x.ofLp i| ^ ((p : ℝ) - 1) * |y.ofLp i| := by
    conv_lhs =>
      arg 2
      ext i
      rw [show ‖x‖ ^ (2 - (p : ℝ)) * |x.ofLp i| ^ ((p : ℝ) - 1) * |y.ofLp i| =
              ‖x‖ ^ (2 - (p : ℝ)) * (|x.ofLp i| ^ ((p : ℝ) - 1) * |y.ofLp i|) by ring]
    rw [← Finset.mul_sum]
  rw [hfactor]
  -- Apply Hölder's inequality with p' = p/(p-1) and q = p
  -- Note: 1/p' + 1/q = (p-1)/p + 1/p = 1
  have hHolder := Real.inner_le_Lp_mul_Lq
    (p := (p : ℝ) / ((p : ℝ) - 1)) (q := p)
    (f := fun i => |x.ofLp i| ^ ((p : ℝ) - 1)) (g := fun i => |y.ofLp i|) Finset.univ ?hpq
  case hpq =>
    refine ⟨?_, ?_, ?_⟩
    · -- (p-1)/p + 1/p = 1
      field_simp
      ring
    · apply div_pos hp_pos hp1_pos
    · exact hp_pos
  -- Simplify the absolute values in Hölder (they're already non-negative)
  have habs_f : ∀ i, |(|x.ofLp i| ^ ((p : ℝ) - 1))| = |x.ofLp i| ^ ((p : ℝ) - 1) := by
    intro i
    apply abs_of_nonneg
    apply Real.rpow_nonneg (abs_nonneg _)
  have habs_g : ∀ i, |(|y.ofLp i|)| = |y.ofLp i| := by
    intro i
    apply abs_abs
  simp only [habs_f, habs_g] at hHolder
  -- Simplify (|x_i|^(p-1))^(p/(p-1)) = |x_i|^p
  have hpow_f : ∀ i, (|x.ofLp i| ^ ((p : ℝ) - 1)) ^ ((p : ℝ) / ((p : ℝ) - 1)) = |x.ofLp i| ^ (p : ℝ) := by
    intro i
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  simp only [hpow_f] at hHolder
  -- Simplify 1/(p/(p-1)) = (p-1)/p in hHolder
  have hexp_simp : 1 / ((p : ℝ) / ((p : ℝ) - 1)) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
  simp only [hexp_simp] at hHolder
  -- Now hHolder says: ∑|x_i|^(p-1)*|y_i| ≤ (∑|x_i|^p)^((p-1)/p) * (∑|y_i|^p)^(1/p)
  -- The LHS multiplied by ‖x‖^(2-p) should be ≤ ‖x‖ * ‖y‖
  apply le_trans (mul_le_mul_of_nonneg_left hHolder (Real.rpow_nonneg (norm_nonneg _) _))
  -- Need to show: ‖x‖^(2-p) * (∑|x_i|^p)^((p-1)/p) * (∑|y_i|^p)^(1/p) ≤ ‖x‖ * ‖y‖
  -- Note: (∑|x_i|^p)^(1/p) = ‖x‖ and (∑|y_i|^p)^(1/p) = ‖y‖
  have hp_toReal_pos : 0 < (p : ℝ≥0∞).toReal := by simp [hp_pos]
  have hx_norm : ‖x‖ = (∑ i, |x.ofLp i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
    rw [PiLp.norm_eq_sum hp_toReal_pos]
    simp only [one_div, Real.norm_eq_abs, ENNReal.toReal_natCast]
  have hy_norm : ‖y‖ = (∑ i, |y.ofLp i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
    rw [PiLp.norm_eq_sum hp_toReal_pos]
    simp only [one_div, Real.norm_eq_abs, ENNReal.toReal_natCast]
  -- (∑|x_i|^p)^((p-1)/p) = ‖x‖^(p-1)
  have hsum_x_pow : (∑ i, |x.ofLp i| ^ (p : ℝ)) ^ (((p : ℝ) - 1) / (p : ℝ)) = ‖x‖ ^ ((p : ℝ) - 1) := by
    rw [hx_norm]
    rw [← Real.rpow_mul (by apply Finset.sum_nonneg; intro i _; apply Real.rpow_nonneg (abs_nonneg _))]
    congr 1
    field_simp
  rw [hsum_x_pow, hy_norm]
  -- Now need: ‖x‖^(2-p) * (‖x‖^(p-1) * ‖y‖) ≤ ‖x‖ * ‖y‖
  -- i.e., ‖x‖^(2-p+p-1) * ‖y‖ ≤ ‖x‖ * ‖y‖
  -- i.e., ‖x‖^1 * ‖y‖ ≤ ‖x‖ * ‖y‖ ✓
  have hexp_sum : (2 - (p : ℝ)) + ((p : ℝ) - 1) = 1 := by ring
  have hexp_ne : (2 - (p : ℝ)) + ((p : ℝ) - 1) ≠ 0 := by rw [hexp_sum]; norm_num
  -- Rewrite a * (b * c) to (a * b) * c
  rw [← mul_assoc (‖x‖ ^ (2 - (p : ℝ))) (‖x‖ ^ ((p : ℝ) - 1))]
  rw [← Real.rpow_add' (norm_nonneg _) hexp_ne]
  rw [hexp_sum, Real.rpow_one]

end inner

section measurable

lemma measurable_of_half_sq_Lp (hp : 1 ≤ p) : Measurable (half_sq_Lp : LpSpace p d → ℝ) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  apply Continuous.measurable
  apply Continuous.mul
  apply continuous_const
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_id

lemma measurable_of_gradient_half_sq_Lp (hp : 2 ≤ p) :
  Measurable (half_sq_Lp' : LpSpace p d → LpSpace p d) := by
  have hfact : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  have hp_pos : (0 : ℝ) < p := by
    have : (2 : ℕ) ≤ p := hp
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.ofNat_le_cast.mpr this
    linarith
  have hp2_nonneg : (0 : ℝ) ≤ (p : ℝ) - 2 := by
    have : (2 : ℕ) ≤ p := hp
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.ofNat_le_cast.mpr this
    linarith
  -- half_sq_Lp' x = WithLp.toLp p (fun i => ‖x‖^(2-p) * |x.ofLp i|^(p-2) * x.ofLp i)
  -- Use the measurable equivalence between (Fin d → ℝ) and LpSpace p d
  -- half_sq_Lp' = (MeasurableEquiv.toLp p (Fin d → ℝ)) ∘ f ∘ (MeasurableEquiv.toLp p (Fin d → ℝ)).symm
  -- where f : (Fin d → ℝ) → (Fin d → ℝ) is measurable
  have heq : half_sq_Lp' = (MeasurableEquiv.toLp (p : ℝ≥0∞) (Fin d → ℝ)) ∘
      (fun v : Fin d → ℝ => fun i => ‖WithLp.toLp p v‖ ^ (2 - (p : ℝ)) * |v i| ^ ((p : ℝ) - 2) * v i) ∘
      (MeasurableEquiv.toLp (p : ℝ≥0∞) (Fin d → ℝ)).symm := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.toLp_apply, MeasurableEquiv.toLp_symm_apply,
      half_sq_Lp', WithLp.ofLp_toLp]
  rw [heq]
  apply Measurable.comp
  · exact (MeasurableEquiv.toLp (p : ℝ≥0∞) (Fin d → ℝ)).measurable
  apply Measurable.comp
  · -- Show the middle function is measurable
    apply measurable_pi_iff.mpr
    intro i
    apply Measurable.mul
    apply Measurable.mul
    -- ‖WithLp.toLp p v‖^(2-p) is measurable
    -- Rewrite 2-p = (-1) * (p-2) to use Measurable.pow_const for integer powers
    · have h2p : 2 - (p : ℝ) = (-1 : ℤ) * ((p : ℝ) - 2) := by ring
      rw [h2p]
      apply Measurable.pow_const
      apply Measurable.norm
      exact (PiLp.continuous_toLp p (fun _ : Fin d => ℝ)).measurable
    -- |v i|^(p-2) is measurable (use continuity since |v i| ≥ 0 and p-2 ≥ 0)
    · apply Continuous.measurable
      apply Continuous.rpow_const
      · apply Continuous.abs
        apply continuous_apply
      · intro v
        apply Or.inr
        exact hp2_nonneg
    -- v i is measurable
    · apply measurable_pi_apply
  · exact (MeasurableEquiv.toLp (p : ℝ≥0∞) (Fin d → ℝ)).symm.measurable

end measurable

end StochasticApproximation
