import AuditCP.FiniteBlackwell
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Chapter 9 — what sealing means to a decision maker, and where the order stops working

Two things happen here.  The first is the decision-theoretic reading of Chapter 8: a B6
`AuditChannel` is sealed exactly when every equal-prior binary experiment between two protected
audit states has Bayes error one half.  This is not a definition that names `(1 - TV)/2` "risk": it
defines the error of every deterministic decision rule, proves a universal lower bound, constructs
an attaining rule, and only then derives the total-variation formula.

The second is a limit, and it is the reason the thesis has a THEORY part at all.  Data processing
orders each divergence and constrains no *difference* of two, while a progress report is exactly
such a difference.  A deterministic coarse-graining can therefore weakly contract both endpoint
divergences and still reverse the sign of their difference.  The explicit `3 → 2` merge below does
so, with exact rational arithmetic.

The finite total-variation convention is the standard half `ℓ¹` distance.  See, for example,
Le Cam and Yang, *Asymptotics in Statistics*, 2000, Chapter 2.  The `PMF` representation and point
masses come from Mathlib `ProbabilityMassFunction.Basic`.

**Carrier note.**  This chapter straddles the two discrete law carriers named in `AuditCP.Base`:
the decision half lives on B5/B6 (Mathlib `PMF`), and the garbling and event-transfer half on the
vendored `FinitePMF`, which is the simplex-constrained refinement of B2 `AuditPotential`.  Every
statement below keeps the carrier it is written on, and nothing here is restated.

The two carriers are nonetheless one carrier.  Chapter 9½, `AuditCP.LawBridge`, supplies the
transport, and supplies it in both directions: on a finite type `finitePMFOfPMF` and
`FinitePMF.toPMF` are mutually inverse — `finitePMFOfPMF_toPMF` and `toPMF_finitePMFOfPMF` are both
identities, so the pair is an isomorphism and not a retraction with its section.  The two total
variations of this chapter are one functional: `finiteTotalVariation_eq_finitePMFTotalVariation`
holds by `rfl`, and `finitePMFTotalVariation_eq_finiteTotalVariation` reads it back across the
`ℝ≥0∞`/`ℝ` joint.  And coarse-graining is one operation:
`pushforwardFinitePMF_finitePMFOfPMF` commutes `pushforwardFinitePMF` with Mathlib's `PMF.map`
through the bridge.  A statement proved below on either carrier may therefore be read on the other,
and the number it reports is the same number.

Two limits on that licence, both structural.  `LawBridge` imports this module, so no declaration
below may cite it; the transport is exercised downstream, in
`deterministicGarbling_reverses_signedProgress_pmf` and in
`finiteBrierPosteriorGain_eq_zero_iff_auditSealed`.  And it is finite-type-only: `Fintype` on one
side and `FinitePMF.prob_nonneg` on the other are what make both directions available, and dropping
either drops a direction.
-/

namespace AuditCP

universe uS uA uY

open Finset

/-- The real-valued point mass of `y` under the Mathlib `PMF` `p`, `(p y).toReal`. -/
noncomputable def pmfMass {Y : Type uY} (p : PMF Y) (y : Y) : ℝ :=
  (p y).toReal

/-- On a finite type, the real point masses of `p` sum to `1`. -/
theorem sum_pmfMass_eq_one {Y : Type uY} [Fintype Y] (p : PMF Y) :
    ∑ y, pmfMass p y = 1 := by
  calc
    ∑ y, pmfMass p y = (∑ y, p y).toReal := by
      symm
      exact ENNReal.toReal_sum fun y _ => p.apply_ne_top y
    _ = (∑' y, p y).toReal := by rw [tsum_fintype]
    _ = 1 := by rw [p.tsum_coe]; norm_num

/-- The total variation distance between `p` and `q`, half the `ℓ¹` distance of their point
masses, `(1/2) * ∑ y, |pmfMass p y - pmfMass q y|`. -/
noncomputable def finiteTotalVariation {Y : Type uY} [Fintype Y]
    (p q : PMF Y) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |pmfMass p y - pmfMass q y|

/-- The equal-prior error of the deterministic decision rule `decision` between `p` (label
`false`) and `q` (label `true`), `(1/2) * ∑ y, if decision y then pmfMass p y else pmfMass q y`. -/
noncomputable def equalPriorBinaryError {Y : Type uY} [Fintype Y]
    (p q : PMF Y) (decision : Y → Bool) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, if decision y then pmfMass p y else pmfMass q y

/-- The equal-prior Bayes error between `p` and `q`, `(1/2) * ∑ y, min (pmfMass p y) (pmfMass q y)`. -/
noncomputable def equalPriorBayesError {Y : Type uY} [Fintype Y]
    (p q : PMF Y) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, min (pmfMass p y) (pmfMass q y)

/-- Every deterministic decision rule has error at least the equal-prior Bayes error:
`equalPriorBayesError p q ≤ equalPriorBinaryError p q decision`. -/
theorem equalPriorBayesError_le_ruleError {Y : Type uY} [Fintype Y]
    (p q : PMF Y) (decision : Y → Bool) :
    equalPriorBayesError p q ≤ equalPriorBinaryError p q decision := by
  unfold equalPriorBayesError equalPriorBinaryError
  gcongr with y
  cases h : decision y
  · simp
  · simp

/-- The likelihood-comparison decision rule, guessing `q` exactly where its point mass is at
least `p`'s, `fun y => decide (pmfMass p y ≤ pmfMass q y)`. -/
noncomputable def equalPriorBayesRule {Y : Type uY} (p q : PMF Y) : Y → Bool :=
  fun y => decide (pmfMass p y ≤ pmfMass q y)

/-- The likelihood-comparison rule attains the equal-prior Bayes error:
`equalPriorBinaryError p q (equalPriorBayesRule p q) = equalPriorBayesError p q`. -/
theorem equalPriorBayesRule_attains {Y : Type uY} [Fintype Y] (p q : PMF Y) :
    equalPriorBinaryError p q (equalPriorBayesRule p q) = equalPriorBayesError p q := by
  unfold equalPriorBinaryError equalPriorBayesError
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases h : pmfMass p y ≤ pmfMass q y
  · simp [equalPriorBayesRule, h]
  · have h' : pmfMass q y ≤ pmfMass p y := le_of_not_ge h
    simp [equalPriorBayesRule, h, min_eq_right h']

/-- `min x y = (x + y - |x - y|) / 2`. -/
theorem min_eq_add_sub_abs_div_two (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
    ring

/-- F3a — `equalPriorBayesError p q = (1 - finiteTotalVariation p q) / 2`. -/
theorem equalPriorBayesError_eq_half_one_sub_tv
    {Y : Type uY} [Fintype Y] (p q : PMF Y) :
    equalPriorBayesError p q = (1 - finiteTotalVariation p q) / 2 := by
  unfold equalPriorBayesError finiteTotalVariation
  simp_rw [min_eq_add_sub_abs_div_two, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_pmfMass_eq_one p, sum_pmfMass_eq_one q]
  ring

/-- `finiteTotalVariation p q = 0 ↔ p = q`. -/
theorem finiteTotalVariation_eq_zero_iff {Y : Type uY} [Fintype Y] (p q : PMF Y) :
    finiteTotalVariation p q = 0 ↔ p = q := by
  constructor
  · intro htv
    have hsum : ∑ y, |pmfMass p y - pmfMass q y| = 0 := by
      unfold finiteTotalVariation at htv
      linarith
    have hpoint : (fun y => |pmfMass p y - pmfMass q y|) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg fun y => abs_nonneg _).1 hsum
    apply PMF.ext
    intro y
    apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top y) (q.apply_ne_top y)).1
    exact sub_eq_zero.1 (abs_eq_zero.1 (congrFun hpoint y))
  · rintro rfl
    simp [finiteTotalVariation]

/-- F3b — `equalPriorBayesError p q = 1/2 ↔ p = q`. -/
theorem equalPriorBayesError_eq_half_iff {Y : Type uY} [Fintype Y] (p q : PMF Y) :
    equalPriorBayesError p q = 1 / 2 ↔ p = q := by
  rw [equalPriorBayesError_eq_half_one_sub_tv]
  constructor
  · intro h
    apply (finiteTotalVariation_eq_zero_iff p q).1
    linarith
  · intro hpq
    rw [(finiteTotalVariation_eq_zero_iff p q).2 hpq]
    norm_num

/-- F3 — `AuditSealed K ↔ ∀ s a a', equalPriorBayesError (K (s, a)) (K (s, a')) = 1/2`. -/
theorem auditSealed_iff_no_binary_decision_advantage
    {S : Type uS} {A : Type uA} {Y : Type uY} [Fintype Y]
    (K : AuditChannel S A Y) :
    AuditSealed K ↔
      ∀ s a a', equalPriorBayesError (K (s, a)) (K (s, a')) = 1 / 2 := by
  constructor
  · intro hsealed s a a'
    exact (equalPriorBayesError_eq_half_iff _ _).2 (hsealed s a a')
  · intro hnoAdvantage s a a'
    exact (equalPriorBayesError_eq_half_iff _ _).1 (hnoAdvantage s a a')

/-! ## Explicit signed-progress reversal under a deterministic garbling -/

/-- The three-symbol observation type `Option Bool` used in the deterministic reversal witness
below. -/
abbrev BlackwellFineSymbol := Option Bool

/-- The pushforward of the finite pmf `p` through `f`, with mass `∑ x, if f x = y then p.prob x
else 0` at each `y`. -/
noncomputable def pushforwardFinitePMF
    {X : Type*} {Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : FinitePMF X) : FinitePMF Y := by
  classical
  refine
    { prob := fun y => ∑ x, if f x = y then p.prob x else 0
      prob_nonneg := ?_
      prob_sum_one := ?_ }
  · intro y
    apply Finset.sum_nonneg
    intro x _hx
    by_cases h : f x = y
    · simp [h, p.prob_nonneg x]
    · simp [h]
  · calc
      (∑ y, ∑ x, if f x = y then p.prob x else 0) =
          ∑ x, ∑ y, if f x = y then p.prob x else 0 := Finset.sum_comm
      _ = ∑ x, p.prob x := by simp
      _ = 1 := p.prob_sum_one

/-- The total variation distance between the finite pmfs `p` and `q`,
`(1/2) * ∑ x, |p.prob x - q.prob x|`. -/
noncomputable def finitePMFTotalVariation
    {X : Type*} [Fintype X] (p q : FinitePMF X) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x|

/-- The reference law of the reversal witness, with mass `8/10` at `none`, `1/10` at
`some false`, `1/10` at `some true`. -/
noncomputable def blackwellFineTarget : FinitePMF BlackwellFineSymbol where
  prob
    | none => 8 / 10
    | some false => 1 / 10
    | some true => 1 / 10
  prob_nonneg := by intro x; rcases x with _ | (_ | _) <;> norm_num
  prob_sum_one := by norm_num [Fintype.sum_option, Fintype.sum_bool]

/-- The initial-endpoint law of the reversal witness, with mass `1/10` at `none`, `8/10` at
`some false`, `1/10` at `some true`. -/
noncomputable def blackwellFineInitial : FinitePMF BlackwellFineSymbol where
  prob
    | none => 1 / 10
    | some false => 8 / 10
    | some true => 1 / 10
  prob_nonneg := by intro x; rcases x with _ | (_ | _) <;> norm_num
  prob_sum_one := by norm_num [Fintype.sum_option, Fintype.sum_bool]

/-- The terminal-endpoint law of the reversal witness, with mass `7/10` at `none`, `1/10` at
`some false`, `2/10` at `some true`. -/
noncomputable def blackwellFineTerminal : FinitePMF BlackwellFineSymbol where
  prob
    | none => 7 / 10
    | some false => 1 / 10
    | some true => 2 / 10
  prob_nonneg := by intro x; rcases x with _ | (_ | _) <;> norm_num
  prob_sum_one := by norm_num [Fintype.sum_option, Fintype.sum_bool]

/-- The deterministic garbling merging `none` and `some false` to `false` and mapping
`some true` to `true`. -/
def blackwellMerge : BlackwellFineSymbol → Bool
  | none => false
  | some false => false
  | some true => true

/-- For the explicit laws `blackwellFineTarget`, `blackwellFineInitial`, `blackwellFineTerminal`
and their pushforwards under `blackwellMerge`, the two fine total variations from the target are
`7/10` and `1/10`, the two coarse total variations are `0` and `1/10`, each coarse total variation
is at most the corresponding fine one, and the fine difference `3/5` reverses sign to the coarse
difference `-(1/10)`. -/
theorem deterministicGarbling_reverses_signedProgress :
    let P := blackwellFineTarget
    let Q₀ := blackwellFineInitial
    let Q₁ := blackwellFineTerminal
    let PG := pushforwardFinitePMF blackwellMerge P
    let Q₀G := pushforwardFinitePMF blackwellMerge Q₀
    let Q₁G := pushforwardFinitePMF blackwellMerge Q₁
    finitePMFTotalVariation P Q₀ = 7 / 10 ∧
    finitePMFTotalVariation P Q₁ = 1 / 10 ∧
    finitePMFTotalVariation PG Q₀G = 0 ∧
    finitePMFTotalVariation PG Q₁G = 1 / 10 ∧
    finitePMFTotalVariation P Q₀ - finitePMFTotalVariation P Q₁ = 3 / 5 ∧
    finitePMFTotalVariation PG Q₀G - finitePMFTotalVariation PG Q₁G = -(1 / 10) ∧
    finitePMFTotalVariation PG Q₀G ≤ finitePMFTotalVariation P Q₀ ∧
    finitePMFTotalVariation PG Q₁G ≤ finitePMFTotalVariation P Q₁ := by
  norm_num [finitePMFTotalVariation, pushforwardFinitePMF, blackwellFineTarget,
    blackwellFineInitial, blackwellFineTerminal, blackwellMerge, Fintype.sum_option,
    Fintype.sum_bool, abs_of_nonneg, abs_of_nonpos]

/-! ## Approximate-seal event transfer -/

/-- The probability of the event `E` under the finite pmf `p`,
`∑ x, if x ∈ E then p.prob x else 0`. -/
noncomputable def finitePMFEventProb
    {X : Type*} [Fintype X] (p : FinitePMF X) (E : Set X) : ℝ := by
  classical
  exact ∑ x, if x ∈ E then p.prob x else 0

/-- `finitePMFEventProb q E - finitePMFEventProb p E ≤ finitePMFTotalVariation p q`. -/
theorem finitePMFEventProb_sub_le_totalVariation
    {X : Type*} [Fintype X] (p q : FinitePMF X) (E : Set X) :
    finitePMFEventProb q E - finitePMFEventProb p E ≤ finitePMFTotalVariation p q := by
  classical
  let d : X → ℝ := fun x => q.prob x - p.prob x
  have hsumd : ∑ x, d x = 0 := by
    simp only [d, Finset.sum_sub_distrib, q.prob_sum_one, p.prob_sum_one, sub_self]
  have habs (x : X) : |d x| = 2 * max (d x) 0 - d x := by
    rcases le_total (d x) 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]
      ring
    · rw [max_eq_left h, abs_of_nonneg h]
      ring
  have htv : finitePMFTotalVariation p q = ∑ x, max (d x) 0 := by
    unfold finitePMFTotalVariation
    have hsumabs : ∑ x, |p.prob x - q.prob x| = ∑ x, |d x| := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [d, abs_sub_comm]
    rw [hsumabs]
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumd]
    ring
  have hevent :
      finitePMFEventProb q E - finitePMFEventProb p E =
        ∑ x, if x ∈ E then d x else 0 := by
    unfold finitePMFEventProb
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hxE : x ∈ E <;> simp [hxE, d]
  rw [hevent, htv]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases hxE : x ∈ E
  · simp [hxE]
  · simp [hxE]

/-- If the reference law's `E`-probability is at most `δ` and `actual` lies within total variation
`ε` of `reference`, then `actual`'s `E`-probability is at most `δ + ε`. -/
theorem approximateSeal_event_le
    {X : Type*} [Fintype X]
    (reference actual : FinitePMF X) (E : Set X) (δ ε : ℝ)
    (href : finitePMFEventProb reference E ≤ δ)
    (hleak : finitePMFTotalVariation reference actual ≤ ε) :
    finitePMFEventProb actual E ≤ δ + ε := by
  have hchange := finitePMFEventProb_sub_le_totalVariation reference actual E
  linarith

end AuditCP
