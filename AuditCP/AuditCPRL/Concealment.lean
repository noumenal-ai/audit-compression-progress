import AuditCP.FiniteBlackwell
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

/-!
# Target 4 — per-step marginals cannot certify concealment of a hidden kernel parameter

`AuditCP.xorTranscriptChannel` is a one-shot parity channel whose two coordinate marginals are
audit-sealed while its joint is not (`AuditCP.xorTranscript_marginals_sealed`,
`AuditCP.xorTranscript_not_sealed`).  The in-scope audit corpus has no time-homogeneous dynamics at
all, so carrying that obstruction into a Markov chain is a construction, not a retyping.

The construction is a **phase** coordinate.  A memoryless chain cannot hold a one-time pad across a
step; the state must record whether the pad is about to be spent.  On `Bool × Bool` with
`(phase, data)`:

* from `(true, u)` the chain moves deterministically to `(false, xor u h)` — the pad is spent, and
  the hidden bit `h` enters here and only here;
* from `(false, _)` the chain re-randomizes uniformly — which is what buys ergodicity.

The initial law is `AuditCP.fairBool` pushed onto the phase-`true` fibre, so it does not mention
`h`: the hidden bit lives in the dynamics, which is the honest reading of concealment.

## What is proved

* the witness carries a `ReinforcementLearning.FiniteMRP` for **both** values of `h`, so the
  result is not a periodicity artifact and sits inside the ergodicity hypotheses under which the
  RL library's own convergence theorems hold;
* the **entire** time-`n` state law is the same for `h = false` and `h = true`, for every `n` — so
  no one-time marginal separates the hypotheses, not even one that observes the full state;
* the two-step observed joint is exactly `AuditCP.xorTranscriptChannel ((), h)`, so
  `AuditCP.xorTranscript_decodes_audit` recovers `h` with probability one and
  `AuditCP.xorTranscript_not_sealed` shows the two joints differ.

Concealment must therefore be tested on the joint transcript.  The obstruction is equality of
laws, not a failure of a particular decoder, so it survives every decoder and every statistic
computed downstream of the one-time marginals.

## Named obligation

`AuditCPRL.stateLaw` is the finite-dimensional time-`n` marginal `init * Pⁿ`.  Identifying it with
the time-`n` marginal of `ProbabilityTheory.MarkovChain.traj_prob` is proved in neither corpus, so
it is carried as an explicit **named hypothesis** on
`AuditCPRL.marginal_tests_cannot_certify_concealment_traj` rather than assumed silently or
fabricated.  Every other statement in this file is unconditional.

## Not witnessed here

The state-abstraction reading.  Above, `h` indexes the kernel family; it is not a state
coordinate.  "Marginal tests cannot certify a state abstraction" needs `h` folded into the state as
a frozen coordinate together with an explicit map forgetting it, and a definition of what it means
for that map to be audited.  Named obligation.

-/

namespace AuditCPRL

open AuditCP ReinforcementLearning StochasticMatrix MeasureTheory ProbabilityTheory

universe u

section Chain
variable {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The homogeneous Markov chain on `S` built from row family `row` and initial law `init`, both
read as Mathlib `PMF`s. -/
noncomputable def pmfChain (row : S → PMF S) (init : PMF S) :
    MarkovChain.HomMarkovChainSpec S where
  kernel := Kernel.ofFunOfCountable fun s => (row s).toMeasure
  markov_kernel := ⟨fun s => PMF.toMeasure.isProbabilityMeasure (row s)⟩
  init := ⟨init.toMeasure, PMF.toMeasure.isProbabilityMeasure init⟩

/-- `MarkovChain.Finite.kernel_mat (pmfChain row init) s t = (row s t).toReal`. -/
theorem kernel_mat_pmfChain (row : S → PMF S) (init : PMF S) (s t : S) :
    MarkovChain.Finite.kernel_mat (pmfChain row init) s t = (row s t).toReal := by
  simp only [MarkovChain.Finite.kernel_mat, Matrix.of_apply, pmfChain]
  show ((row s).toMeasure {t}).toReal = ((row s) t).toReal
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)]

/-- `MarkovChain.Finite.init_vec (pmfChain row init) s = (init s).toReal`. -/
theorem init_vec_pmfChain (row : S → PMF S) (init : PMF S) (s : S) :
    MarkovChain.Finite.init_vec (pmfChain row init) s = (init s).toReal := by
  have hcoe := ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (pmfChain row init).init {s}
  have hval : ((pmfChain row init).init : Measure S) {s} = init s :=
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)
  simp only [MarkovChain.Finite.init_vec]
  rw [← ENNReal.coe_toReal, hcoe, hval]

end Chain

/-! ### The witness.  State `(phase, data)`; the hidden bit enters only through the kernel. -/

section Witness

/-- The pad-chain transition row at hidden bit `h`: from `(true, u)` deterministically to
`(false, u xor h)`, and from `(false, _)` uniformly over `Bool × Bool`. -/
noncomputable def padRow (h : Bool) : Bool × Bool → PMF (Bool × Bool)
  | (true , u) => PMF.pure (false, Bool.xor u h)
  | (false, _) => PMF.uniformOfFintype (Bool × Bool)

/-- The pad chain's initial law, `fairBool` pushed onto the phase-`true` fibre,
`fun u => (true, u)`. -/
noncomputable def padInit : PMF (Bool × Bool) := fairBool.map fun u => (true, u)

/-- The concealment witness chain at hidden bit `h`, `pmfChain (padRow h) padInit`. -/
noncomputable def padChain (h : Bool) : MarkovChain.HomMarkovChainSpec (Bool × Bool) :=
  pmfChain (padRow h) padInit

/-- `MarkovChain.Finite.kernel_mat (padChain h) s t = if s.1 = true then
(if t = (false, s.2 xor h) then 1 else 0) else 1/4`. -/
theorem padMat (h : Bool) (s t : Bool × Bool) :
    MarkovChain.Finite.kernel_mat (padChain h) s t
      = if s.1 = true then (if t = (false, Bool.xor s.2 h) then 1 else 0) else 1 / 4 := by
  rw [padChain, kernel_mat_pmfChain]
  obtain ⟨c, u⟩ := s
  cases c <;>
    simp [padRow, PMF.pure_apply, PMF.uniformOfFintype_apply, apply_ite ENNReal.toReal]

/-- `MarkovChain.Finite.init_vec (padChain h) s = if s.1 = true then 1/2 else 0`. -/
theorem padInitVec (h : Bool) (s : Bool × Bool) :
    MarkovChain.Finite.init_vec (padChain h) s = if s.1 = true then 1 / 2 else 0 := by
  rw [padChain, init_vec_pmfChain]
  obtain ⟨c, u⟩ := s
  cases c <;> cases u <;> simp [padInit, PMF.map_apply, fairBool_apply]

/-! ### Ergodicity.  This is where the phase coordinate pays for itself. -/

/-- `0 < (MarkovChain.Finite.kernel_mat (padChain h) ^ 2) i j`. -/
theorem padMat_two_pos (h : Bool) (i j : Bool × Bool) :
    0 < ((MarkovChain.Finite.kernel_mat (padChain h)) ^ 2) i j := by
  obtain ⟨c, u⟩ := i
  have key : ∀ k : Bool × Bool,
      ((MarkovChain.Finite.kernel_mat (padChain h)) ^ 2) (c, u) j
        ≥ MarkovChain.Finite.kernel_mat (padChain h) (c, u) k
            * MarkovChain.Finite.kernel_mat (padChain h) k j := by
    intro k
    simpa using
      chapman_kolmogorov_eq_ge (MarkovChain.Finite.kernel_mat (padChain h)) 1 1 (c, u) j k
  cases c
  · have hb := key (false, false)
    rw [padMat, padMat] at hb
    simp only [Bool.false_eq_true, if_false] at hb
    linarith
  · have hb := key (false, Bool.xor u h)
    rw [padMat, padMat] at hb
    simp only [if_true, Bool.false_eq_true, if_false, one_mul] at hb
    linarith

/-- `padChain h`'s transition matrix is irreducible. -/
theorem irreducible_padChain (h : Bool) :
    StochasticMatrix.Irreducible (MarkovChain.Finite.kernel_mat (padChain h)) :=
  ⟨fun i j => ⟨2, padMat_two_pos h i j⟩⟩

/-- `padChain h`'s transition matrix is aperiodic. -/
theorem aperiodic_padChain (h : Bool) :
    Aperiodic (MarkovChain.Finite.kernel_mat (padChain h)) := by
  refine ⟨fun i => ?_⟩
  obtain ⟨c, u⟩ := i
  cases c
  · refine Nat.dvd_one.mp (Nat.setGcd_dvd_of_mem (n := 1) ⟨le_rfl, ?_⟩)
    rw [pow_one, padMat]
    norm_num
  · have hthree : 0 < ((MarkovChain.Finite.kernel_mat (padChain h)) ^ 3) (true, u) (true, u) := by
      have hb := chapman_kolmogorov_eq_ge (MarkovChain.Finite.kernel_mat (padChain h)) 2 1
        (true, u) (true, u) (false, false)
      have hstep : MarkovChain.Finite.kernel_mat (padChain h) (false, false) (true, u) = 1 / 4 := by
        rw [padMat]; norm_num
      rw [pow_one, hstep] at hb
      have := padMat_two_pos h (true, u) (false, false)
      norm_num at hb ⊢
      linarith
    have d2 := Nat.setGcd_dvd_of_mem (s := return_times (MarkovChain.Finite.kernel_mat
      (padChain h)) (true, u)) (n := 2) ⟨by norm_num, padMat_two_pos h (true, u) (true, u)⟩
    have d3 := Nat.setGcd_dvd_of_mem (s := return_times (MarkovChain.Finite.kernel_mat
      (padChain h)) (true, u)) (n := 3) ⟨by norm_num, hthree⟩
    exact Nat.dvd_one.mp (by simpa using Nat.dvd_sub d3 d2)

/-- The pad chain at hidden bit `h` packaged as a `FiniteMRP` with zero discount and zero
reward. -/
noncomputable def padMRP (h : Bool) : FiniteMRP (S := Bool × Bool) where
  M := padChain h
  hM := ⟨irreducible_padChain h, aperiodic_padChain h⟩
  γ := 0
  hγ := ⟨le_rfl, zero_lt_one⟩
  r := fun _ => 0

end Witness

/-! ### Time-`n` marginals.

`AuditCPRL.stateLaw` is the finite-dimensional time-`n` marginal.  Identifying it with the
time-`n` marginal of `ProbabilityTheory.MarkovChain.traj_prob` is an open obligation, carried as a
named hypothesis where it is used and discharged nowhere. -/

section Marginal
variable {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The law of `M`'s state at time `n`,
`Matrix.vecMul (MarkovChain.Finite.init_vec M) (MarkovChain.Finite.kernel_mat M ^ n)`. -/
noncomputable def stateLaw (M : MarkovChain.HomMarkovChainSpec S) (n : ℕ) : S → ℝ :=
  Matrix.vecMul (MarkovChain.Finite.init_vec M) ((MarkovChain.Finite.kernel_mat M) ^ n)

omit [MeasurableSingletonClass S] in
/-- `stateLaw M (n + 1) = Matrix.vecMul (stateLaw M n) (MarkovChain.Finite.kernel_mat M)`. -/
theorem stateLaw_succ (M : MarkovChain.HomMarkovChainSpec S) (n : ℕ) :
    stateLaw M (n + 1) = Matrix.vecMul (stateLaw M n) (MarkovChain.Finite.kernel_mat M) := by
  simp only [stateLaw, pow_succ, Matrix.vecMul_vecMul]

end Marginal

/-! ### What no one-time marginal can see. -/

section Sealed

/-- For every `n`, there exist `a b : ℝ` such that
`stateLaw (padChain h) n = fun s => if s.1 = true then a else b` for both values of `h`. -/
theorem stateLaw_padChain_phaseOnly (n : ℕ) : ∃ a b : ℝ,
    ∀ h : Bool, stateLaw (padChain h) n = fun s => if s.1 = true then a else b := by
  induction n with
  | zero =>
      refine ⟨1 / 2, 0, fun h => ?_⟩
      funext s
      simp [stateLaw, padInitVec]
  | succ n ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨b / 2, a + b / 2, fun h => ?_⟩
      rw [stateLaw_succ, hab h]
      funext t
      show ∑ s : Bool × Bool, (if s.1 = true then a else b)
        * MarkovChain.Finite.kernel_mat (padChain h) s t = _
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, padMat]
      obtain ⟨tc, tu⟩ := t
      cases h <;> cases tc <;> cases tu <;> norm_num <;> ring

/-- `stateLaw (padChain false) n = stateLaw (padChain true) n`. -/
theorem stateLaw_padChain_eq (n : ℕ) :
    stateLaw (padChain false) n = stateLaw (padChain true) n := by
  obtain ⟨a, b, hab⟩ := stateLaw_padChain_phaseOnly n
  rw [hab false, hab true]

/-- The law of the two observed data bits at times `0` and `1`,
`padInit.bind (fun s => (padRow h s).map (fun t => (s.2, t.2)))`. -/
noncomputable def padTwoStep (h : Bool) : PMF (Bool × Bool) :=
  padInit.bind fun s => (padRow h s).map fun t => (s.2, t.2)

/-- `padTwoStep h = xorTranscriptChannel ((), h)`. -/
theorem padTwoStep_eq_xorTranscript (h : Bool) :
    padTwoStep h = xorTranscriptChannel ((), h) := by
  rw [padTwoStep, padInit, PMF.bind_map, xorTranscriptChannel, ← PMF.bind_pure_comp]
  congr 1
  funext u
  simp [padRow, PMF.pure_map]

/-- `(padTwoStep h).map xorTranscriptDecoder = PMF.pure h`. -/
theorem padTwoStep_decodes (h : Bool) :
    (padTwoStep h).map xorTranscriptDecoder = PMF.pure h := by
  rw [padTwoStep_eq_xorTranscript]
  exact xorTranscript_decodes_audit h

/-- Both marginals of `padTwoStep`, `fun sa => (padTwoStep sa.2).map Prod.fst` and `Prod.snd`,
are audit-sealed. -/
theorem padTwoStep_marginals_sealed :
    AuditSealed (fun sa : Unit × Bool => (padTwoStep sa.2).map Prod.fst) ∧
      AuditSealed (fun sa : Unit × Bool => (padTwoStep sa.2).map Prod.snd) := by
  refine ⟨fun s a a' => ?_, fun s a a' => ?_⟩
  · simpa only [padTwoStep_eq_xorTranscript] using xorTranscript_marginals_sealed.1 s a a'
  · simpa only [padTwoStep_eq_xorTranscript] using xorTranscript_marginals_sealed.2 s a a'

/-- `fun sa : Unit × Bool => padTwoStep sa.2` is not audit-sealed. -/
theorem padTwoStep_not_sealed : ¬ AuditSealed fun sa : Unit × Bool => padTwoStep sa.2 := by
  intro hs
  refine xorTranscript_not_sealed fun s a a' => ?_
  simpa only [padTwoStep_eq_xorTranscript] using hs s a a'

/-- `padTwoStep false ≠ padTwoStep true`. -/
theorem padTwoStep_ne : padTwoStep false ≠ padTwoStep true := by
  intro hEq
  have hmap := congrArg (fun p : PMF (Bool × Bool) => p.map xorTranscriptDecoder) hEq
  rw [padTwoStep_decodes false, padTwoStep_decodes true] at hmap
  exact Bool.false_ne_true (pmf_pure_injective hmap)

/-- `padChain false` and `padChain true` share the same initial vector, each admits a `FiniteMRP`
packaging, their time-`n` state laws agree for every `n`, `padTwoStep h` decodes `h` with
probability one for both values, and `padTwoStep false ≠ padTwoStep true`. -/
theorem marginal_tests_cannot_certify_concealment :
    (∀ s, MarkovChain.Finite.init_vec (padChain false) s
        = MarkovChain.Finite.init_vec (padChain true) s)
      ∧ (∀ h : Bool, ∃ MRP : FiniteMRP (S := Bool × Bool), MRP.M = padChain h)
      ∧ (∀ n : ℕ, stateLaw (padChain false) n = stateLaw (padChain true) n)
      ∧ (∀ h : Bool, (padTwoStep h).map xorTranscriptDecoder = PMF.pure h)
      ∧ padTwoStep false ≠ padTwoStep true :=
  ⟨fun s => by rw [padInitVec, padInitVec], fun h => ⟨padMRP h, rfl⟩,
    stateLaw_padChain_eq, padTwoStep_decodes, padTwoStep_ne⟩

/-- If the time-`n` marginal of `MarkovChain.traj_prob M` equals `stateLaw M n` for every `M`,
`n`, `s` (`hmarg`), then `(MarkovChain.traj_prob (padChain false)).toMeasure.real {w | w n = s} =
(MarkovChain.traj_prob (padChain true)).toMeasure.real {w | w n = s}`. -/
theorem marginal_tests_cannot_certify_concealment_traj
    (hmarg : ∀ (M : MarkovChain.HomMarkovChainSpec (Bool × Bool)) (n : ℕ) (s : Bool × Bool),
      (MarkovChain.traj_prob M).toMeasure.real {w | w n = s} = stateLaw M n s)
    (n : ℕ) (s : Bool × Bool) :
    (MarkovChain.traj_prob (padChain false)).toMeasure.real {w | w n = s}
      = (MarkovChain.traj_prob (padChain true)).toMeasure.real {w | w n = s} := by
  rw [hmarg, hmarg, stateLaw_padChain_eq]

end Sealed

end AuditCPRL
