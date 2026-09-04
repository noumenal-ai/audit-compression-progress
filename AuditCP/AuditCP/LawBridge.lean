import AuditCP.FiniteBlackwellDecision
import AuditCP.Vendored.FinitePMF
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Chapter 9½ — one law carrier

`AuditCP.Base` names three probability-law carriers and records that the closure relates none of
them: B5 `AuditExperiment` on Mathlib's `PMF`, the vendored `FinitePMF` (B2 `AuditPotential`
constrained to the simplex), and B7 `AuditSampleLaw` on Mathlib's `Measure`.  Chapter 9 is where
the split hurts most: `FiniteBlackwellDecision` uses `PMF` for the whole decision half and
`FinitePMF` for the whole garbling half, and its own carrier warning says that no statement there
may be read as if the two halves shared an object.

This chapter removes that warning's cause.  On a finite type the two discrete carriers are
*mutually inverse images* of each other — not a one-way retraction — and the two functionals the
thesis actually reads off them, total variation and deterministic pushforward, commute with the
bridge.  The consequence is that `PMF` may be taken as the single law carrier: `FinitePMF` is its
image under `finitePMFOfPMF` (with `FinitePMF.toPMF` the inverse image), and `Measure` is its
image under Mathlib's `PMF.toMeasure`.

The joint being crossed is `ℝ≥0∞` against `ℝ`.  It is crossable in both directions here, and only
here, for two reasons that are hypotheses and not conveniences: `Fintype` makes the summability
field of a `PMF` a finite sum, and `FinitePMF.prob_nonneg` makes `ENNReal.ofReal` lossless.  Drop
either and one direction of the bridge fails.

Nothing below changes a type, a definition body, or a name.  Every statement of the existing
closure keeps the carrier it was written on; what is added is the licence to move a statement
across, and the two commutation laws that say the move preserves what the thesis reads.

## What this chapter does not give

The `Measure` leg is one-directional.  `PMF.toMeasure` carries every discrete law to a σ-additive
one; the return trip needs countability and a singleton-measurable structure, and even with those
it is a fact about Mathlib's `Measure.toPMF`, not about anything the audit development needs.  The
thesis therefore reads: one carrier, `PMF`, with `FinitePMF` an isomorphic image on finite types
and `Measure` a faithful but one-way image.

The vocabulary is the thesis vocabulary: the audit yields a *slack* and a *lower bound on
improvement*, never a certificate.
-/

namespace AuditCP

universe u v

open Finset

/-! ## The bridge, forward -/

/-- The finite pmf reading of a Mathlib `PMF` `p` on a finite type, with
`prob := fun h => pmfMass p h`. -/
noncomputable def finitePMFOfPMF {H : Type u} [Fintype H] (p : PMF H) : FinitePMF H where
  prob := fun h => pmfMass p h
  prob_nonneg := fun _ => ENNReal.toReal_nonneg
  prob_sum_one := sum_pmfMass_eq_one p

/-! ## The bridge, backward -/

/-- The Mathlib `PMF` reading of a finite pmf `q`, with mass `ENNReal.ofReal (q.prob h)` at
each `h`. -/
noncomputable def FinitePMF.toPMF {H : Type u} [Fintype H] (q : FinitePMF H) : PMF H :=
  PMF.ofFintype (fun h => ENNReal.ofReal (q.prob h)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun h _ => q.prob_nonneg h, q.prob_sum_one,
      ENNReal.ofReal_one]

/-! ## The two round trips -/

/-- If two finite pmfs on `H` agree pointwise on `prob`, they are equal. -/
theorem FinitePMF.ext {H : Type u} [Fintype H] {p q : FinitePMF H}
    (h : ∀ x, p.prob x = q.prob x) : p = q := by
  have hprob : p.prob = q.prob := funext h
  cases p
  cases q
  subst hprob
  rfl

/-- `finitePMFOfPMF (FinitePMF.toPMF q) = q`. -/
theorem finitePMFOfPMF_toPMF {H : Type u} [Fintype H] (q : FinitePMF H) :
    finitePMFOfPMF (FinitePMF.toPMF q) = q := by
  apply FinitePMF.ext
  intro x
  simp only [finitePMFOfPMF, pmfMass, FinitePMF.toPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (q.prob_nonneg x)

/-- `FinitePMF.toPMF (finitePMFOfPMF p) = p`. -/
theorem toPMF_finitePMFOfPMF {H : Type u} [Fintype H] (p : PMF H) :
    FinitePMF.toPMF (finitePMFOfPMF p) = p := by
  apply PMF.ext
  intro x
  simp only [FinitePMF.toPMF, PMF.ofFintype_apply, finitePMFOfPMF, pmfMass]
  exact ENNReal.ofReal_toReal (p.apply_ne_top x)

/-! ## Total variation commutes with the bridge -/

/-- `finiteTotalVariation p q = finitePMFTotalVariation (finitePMFOfPMF p) (finitePMFOfPMF q)`. -/
theorem finiteTotalVariation_eq_finitePMFTotalVariation
    {Y : Type u} [Fintype Y] (p q : PMF Y) :
    finiteTotalVariation p q =
      finitePMFTotalVariation (finitePMFOfPMF p) (finitePMFOfPMF q) := rfl

/-- `finitePMFTotalVariation p q = finiteTotalVariation (FinitePMF.toPMF p) (FinitePMF.toPMF q)`. -/
theorem finitePMFTotalVariation_eq_finiteTotalVariation
    {Y : Type u} [Fintype Y] (p q : FinitePMF Y) :
    finitePMFTotalVariation p q =
      finiteTotalVariation (FinitePMF.toPMF p) (FinitePMF.toPMF q) := by
  rw [finiteTotalVariation_eq_finitePMFTotalVariation, finitePMFOfPMF_toPMF,
    finitePMFOfPMF_toPMF]

/-! ## Deterministic pushforward commutes with the bridge -/

/-- `pushforwardFinitePMF f (finitePMFOfPMF p) = finitePMFOfPMF (PMF.map f p)`. -/
theorem pushforwardFinitePMF_finitePMFOfPMF
    {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] (f : X → Y) (p : PMF X) :
    pushforwardFinitePMF f (finitePMFOfPMF p) = finitePMFOfPMF (PMF.map f p) := by
  classical
  apply FinitePMF.ext
  intro y
  have hmap : pmfMass (PMF.map f p) y = ∑ x, (if y = f x then p x else 0).toReal := by
    rw [pmfMass, PMF.map_apply, tsum_fintype]
    refine ENNReal.toReal_sum ?_
    intro x _hx
    by_cases h : y = f x
    · simpa [h] using p.apply_ne_top x
    · simp [h]
  show (∑ x, if f x = y then pmfMass p x else 0) = pmfMass (PMF.map f p) y
  rw [hmap]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases h : f x = y
  · subst h
    simp [pmfMass]
  · rw [if_neg h, if_neg fun hy : y = f x => h hy.symm]
    simp

/-! ## F12 on the experiment carrier -/

/-- The eight `deterministicGarbling_reverses_signedProgress` (F12) conjuncts hold with
`blackwellFineTarget`, `blackwellFineInitial`, `blackwellFineTerminal` lifted to `PMF` by
`FinitePMF.toPMF` and coarse-grained by `PMF.map blackwellMerge`, using `finiteTotalVariation` in
place of `finitePMFTotalVariation`. -/
theorem deterministicGarbling_reverses_signedProgress_pmf :
    let P := FinitePMF.toPMF blackwellFineTarget
    let Q₀ := FinitePMF.toPMF blackwellFineInitial
    let Q₁ := FinitePMF.toPMF blackwellFineTerminal
    let PG := PMF.map blackwellMerge P
    let Q₀G := PMF.map blackwellMerge Q₀
    let Q₁G := PMF.map blackwellMerge Q₁
    finiteTotalVariation P Q₀ = 7 / 10 ∧
    finiteTotalVariation P Q₁ = 1 / 10 ∧
    finiteTotalVariation PG Q₀G = 0 ∧
    finiteTotalVariation PG Q₁G = 1 / 10 ∧
    finiteTotalVariation P Q₀ - finiteTotalVariation P Q₁ = 3 / 5 ∧
    finiteTotalVariation PG Q₀G - finiteTotalVariation PG Q₁G = -(1 / 10) ∧
    finiteTotalVariation PG Q₀G ≤ finiteTotalVariation P Q₀ ∧
    finiteTotalVariation PG Q₁G ≤ finiteTotalVariation P Q₁ := by
  have hfine : ∀ a b : FinitePMF BlackwellFineSymbol,
      finiteTotalVariation (FinitePMF.toPMF a) (FinitePMF.toPMF b)
        = finitePMFTotalVariation a b := fun a b =>
    (finitePMFTotalVariation_eq_finiteTotalVariation a b).symm
  have hlift : ∀ a : FinitePMF BlackwellFineSymbol,
      finitePMFOfPMF (PMF.map blackwellMerge (FinitePMF.toPMF a))
        = pushforwardFinitePMF blackwellMerge a := by
    intro a
    rw [← pushforwardFinitePMF_finitePMFOfPMF, finitePMFOfPMF_toPMF]
  have hcoarse : ∀ a b : FinitePMF BlackwellFineSymbol,
      finiteTotalVariation (PMF.map blackwellMerge (FinitePMF.toPMF a))
          (PMF.map blackwellMerge (FinitePMF.toPMF b))
        = finitePMFTotalVariation (pushforwardFinitePMF blackwellMerge a)
            (pushforwardFinitePMF blackwellMerge b) := by
    intro a b
    rw [finiteTotalVariation_eq_finitePMFTotalVariation, hlift, hlift]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := deterministicGarbling_reverses_signedProgress
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfine]; exact h1
  · rw [hfine]; exact h2
  · rw [hcoarse]; exact h3
  · rw [hcoarse]; exact h4
  · rw [hfine, hfine]; exact h5
  · rw [hcoarse, hcoarse]; exact h6
  · rw [hcoarse, hfine]; exact h7
  · rw [hcoarse, hfine]; exact h8

/-! ## The third carrier -/

open MeasureTheory in
/-- `expectFinitePMF q f = ∫ h, f h ∂(FinitePMF.toPMF q).toMeasure`. -/
theorem expectFinitePMF_eq_integral_toMeasure {H : Type u} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (q : FinitePMF H) (f : H → ℝ) :
    expectFinitePMF q f = ∫ h, f h ∂(FinitePMF.toPMF q).toMeasure := by
  have hmass : ∀ h : H, ((FinitePMF.toPMF q) h).toReal = q.prob h := by
    intro h
    have hround := congrArg (fun r : FinitePMF H => r.prob h) (finitePMFOfPMF_toPMF q)
    simpa [finitePMFOfPMF, pmfMass] using hround
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  rw [smul_eq_mul, hmass h]

end AuditCP
