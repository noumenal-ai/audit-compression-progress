import AuditCP.FiniteBlackwellDecision
import RLTheory.MarkovDecisionProcess.MarkovRewardProcess

/-!
# Target 2 — a state aggregation reverses signed progress between realizable occupancies

`AuditCP.deterministicGarbling_reverses_signedProgress` exhibits three laws on three symbols and a
deterministic `3 → 2` merge for which total-variation progress toward the target is `+3/5` before
the merge and `−1/10` after it, while both endpoint divergences weakly contract exactly as data
processing requires.  Data processing is monotone in each divergence separately and constrains no
difference of two; a progress report between checkpoints is exactly such a difference.

The RL question is whether that witness is reachable: occupancy measures are not arbitrary laws,
so a realizability constraint might rule the three laws out.  It does not, and the reason is an
exact characterization proved here.

* `finiteMRP_occupancy_iff_fullSupport` — on a finite state space the stationary occupancies of
  **irreducible aperiodic** chains are **exactly** the full-support laws.  Forward is
  `StochasticMatrix.pos_of_stationary`; backward is the rank-one i.i.d.-resampling chain
  `AuditCPRL.iidChain`, whose every entry is already positive at `n = 1`, so it is irreducible and
  aperiodic at once.
* `stateAggregation_reverses_occupancy_progress` — the three witness laws are realized as
  `ReinforcementLearning.FiniteMRP.μ` of three ergodic chains, so the reversal survives inside the
  hypotheses under which the RL library's own convergence results hold.

Consequently no structural assumption on the MRP restores the sign: the realizability constraint
excludes nothing.  For divergence-to-target evaluation a coarsened state space is safe for
single-point separation and unsafe for signed comparison of checkpoints.

## Scope, stated rather than assumed

This does **not** extend to return-based evaluation.  The functional `∑ s, μ s * r s` is linear in
`μ` and is governed by the reward-respecting-abstraction condition instead;
the reward field of `ReinforcementLearning.FiniteMRP` is never read below.  Which garblings preserve the sign of
a divergence difference is open and is not claimed here.

-/

namespace AuditCPRL

open AuditCP ReinforcementLearning StochasticMatrix MeasureTheory ProbabilityTheory

universe u

section IID
variable {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The finite pmf `p` read as a Mathlib `PMF`, with mass `ENNReal.ofReal (p.prob s)` at each
`s`. -/
noncomputable def finiteToPMF (p : FinitePMF S) : PMF S :=
  PMF.ofFintype (fun s => ENNReal.ofReal (p.prob s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => p.prob_nonneg s), p.prob_sum_one,
      ENNReal.ofReal_one])

/-- The rank-one i.i.d.-resampling chain on `S`: every step redraws the state from `p`,
independent of the current state. -/
noncomputable def iidChain (p : FinitePMF S) : MarkovChain.HomMarkovChainSpec S where
  kernel := Kernel.const S (finiteToPMF p).toMeasure
  markov_kernel := inferInstance
  init := ⟨(finiteToPMF p).toMeasure, inferInstance⟩

/-- `MarkovChain.Finite.kernel_mat (iidChain p) s t = p.prob t`. -/
theorem kernel_mat_iidChain (p : FinitePMF S) (s t : S) :
    MarkovChain.Finite.kernel_mat (iidChain p) s t = p.prob t := by
  have h : (iidChain p).kernel s {t} = ENNReal.ofReal (p.prob t) := by
    simp only [iidChain, Kernel.const_apply]
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)]
    rfl
  simp only [MarkovChain.Finite.kernel_mat, Matrix.of_apply, h,
    ENNReal.toReal_ofReal (p.prob_nonneg t)]

end IID

/-! ### Ergodicity of the rank-one chain.  `DecidableEq S` enters only here, with matrix powers. -/

section Ergodic
variable {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- If `p` has full support, then `iidChain p`'s transition matrix is irreducible. -/
theorem irreducible_iidChain (p : FinitePMF S) (hpos : ∀ s, 0 < p.prob s) :
    StochasticMatrix.Irreducible (MarkovChain.Finite.kernel_mat (iidChain p)) :=
  ⟨fun _ j => ⟨1, by simpa only [pow_one, kernel_mat_iidChain] using hpos j⟩⟩

/-- If `p` has full support, then `iidChain p`'s transition matrix is aperiodic. -/
theorem aperiodic_iidChain (p : FinitePMF S) (hpos : ∀ s, 0 < p.prob s) :
    Aperiodic (MarkovChain.Finite.kernel_mat (iidChain p)) := by
  refine ⟨fun i => Nat.dvd_one.mp (Nat.setGcd_dvd_of_mem ?_)⟩
  exact ⟨le_rfl, by simpa only [pow_one, kernel_mat_iidChain] using hpos i⟩

omit [DecidableEq S] in
/-- `p.prob` is stationary for `iidChain p`'s transition matrix. -/
theorem stationary_iidChain (p : FinitePMF S) :
    Stationary p.prob (MarkovChain.Finite.kernel_mat (iidChain p)) := by
  refine ⟨?_⟩
  funext j
  show ∑ i, p.prob i * MarkovChain.Finite.kernel_mat (iidChain p) i j = p.prob j
  simp only [kernel_mat_iidChain, ← Finset.sum_mul, p.prob_sum_one, one_mul]

end Ergodic

/-! ### Realization.  `ReinforcementLearning.FiniteMRP` enters here. -/

section Realize
variable {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The i.i.d.-resampling chain at a full-support `p` packaged as a `FiniteMRP` with zero
discount and zero reward. -/
noncomputable def iidMRP (p : FinitePMF S) (hpos : ∀ s, 0 < p.prob s) : FiniteMRP (S := S) where
  M := iidChain p
  hM := ⟨irreducible_iidChain p hpos, aperiodic_iidChain p hpos⟩
  γ := 0
  hγ := ⟨le_rfl, zero_lt_one⟩
  r := fun _ => 0

/-- If `p` has full support, then `FiniteMRP.μ (MRP := iidMRP p hpos) = p.prob`. -/
theorem mu_iidMRP (p : FinitePMF S) (hpos : ∀ s, 0 < p.prob s) :
    FiniteMRP.μ (MRP := iidMRP p hpos) = p.prob := by
  haveI : Aperiodic (FiniteMRP.P (MRP := iidMRP p hpos)) := (iidMRP p hpos).hM.2
  obtain ⟨ν, -, huniq⟩ :=
    stationary_distribution_uniquely_exists (FiniteMRP.P (MRP := iidMRP p hpos))
  rw [huniq (FiniteMRP.μ (MRP := iidMRP p hpos)) ⟨inferInstance, inferInstance⟩,
    huniq p.prob ⟨⟨p.prob_nonneg, p.prob_sum_one⟩, stationary_iidChain p⟩]

/-- `(∃ MRP : FiniteMRP (S := S), FiniteMRP.μ (MRP := MRP) = p.prob) ↔ ∀ s, 0 < p.prob s`. -/
theorem finiteMRP_occupancy_iff_fullSupport (p : FinitePMF S) :
    (∃ MRP : FiniteMRP (S := S), FiniteMRP.μ (MRP := MRP) = p.prob) ↔ ∀ s, 0 < p.prob s := by
  refine ⟨fun h s => ?_, fun hpos => ⟨iidMRP p hpos, mu_iidMRP p hpos⟩⟩
  obtain ⟨MRP, hMRP⟩ := h
  rw [← hMRP]
  exact pos_of_stationary (FiniteMRP.μ (MRP := MRP)) (FiniteMRP.P (MRP := MRP)) s

end Realize

/-! ### The witness, packaged as three ergodic MRPs. -/

section Reversal

/-- The discrete σ-algebra on `BlackwellFineSymbol`. -/
scoped instance : MeasurableSpace BlackwellFineSymbol := ⊤

/-- Singletons are measurable in the discrete σ-algebra on `BlackwellFineSymbol`. -/
scoped instance : MeasurableSingletonClass BlackwellFineSymbol :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- There exist `FiniteMRP`s `Mt, M0, M1` on `BlackwellFineSymbol` whose occupancies are
`blackwellFineTarget.prob`, `blackwellFineInitial.prob`, and `blackwellFineTerminal.prob`, for
which the fine total-variation difference toward the target is strictly positive, the merged
total-variation difference is strictly negative, and each merged total variation is at most the
corresponding fine one. -/
theorem stateAggregation_reverses_occupancy_progress :
    ∃ Mt M0 M1 : FiniteMRP (S := BlackwellFineSymbol),
      FiniteMRP.μ (MRP := Mt) = blackwellFineTarget.prob ∧
      FiniteMRP.μ (MRP := M0) = blackwellFineInitial.prob ∧
      FiniteMRP.μ (MRP := M1) = blackwellFineTerminal.prob ∧
      0 < finitePMFTotalVariation blackwellFineTarget blackwellFineInitial
            - finitePMFTotalVariation blackwellFineTarget blackwellFineTerminal ∧
      finitePMFTotalVariation (pushforwardFinitePMF blackwellMerge blackwellFineTarget)
              (pushforwardFinitePMF blackwellMerge blackwellFineInitial)
          - finitePMFTotalVariation (pushforwardFinitePMF blackwellMerge blackwellFineTarget)
              (pushforwardFinitePMF blackwellMerge blackwellFineTerminal) < 0 ∧
      finitePMFTotalVariation (pushforwardFinitePMF blackwellMerge blackwellFineTarget)
              (pushforwardFinitePMF blackwellMerge blackwellFineInitial)
          ≤ finitePMFTotalVariation blackwellFineTarget blackwellFineInitial ∧
      finitePMFTotalVariation (pushforwardFinitePMF blackwellMerge blackwellFineTarget)
              (pushforwardFinitePMF blackwellMerge blackwellFineTerminal)
          ≤ finitePMFTotalVariation blackwellFineTarget blackwellFineTerminal := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ := deterministicGarbling_reverses_signedProgress
  have hT : ∀ s, 0 < blackwellFineTarget.prob s := by
    rintro (_ | (_ | _)) <;> norm_num [blackwellFineTarget]
  have h0 : ∀ s, 0 < blackwellFineInitial.prob s := by
    rintro (_ | (_ | _)) <;> norm_num [blackwellFineInitial]
  have h1 : ∀ s, 0 < blackwellFineTerminal.prob s := by
    rintro (_ | (_ | _)) <;> norm_num [blackwellFineTerminal]
  exact ⟨iidMRP _ hT, iidMRP _ h0, iidMRP _ h1, mu_iidMRP _ hT, mu_iidMRP _ h0, mu_iidMRP _ h1,
    by rw [h5]; norm_num, by rw [h6]; norm_num, h7, h8⟩

end Reversal

end AuditCPRL
