import AuditCP.EntropyFloor

/-!
# Chapter 12 — reading the instrument

The last chapter says what a number coming out of the argument means, and what it does not mean.
Three things are kept apart that a single symbol would fuse.

*The evaluated-set factor and the envelope radius.*  `resolution` is `2 * deltaFiniteExperts …`.
The `2` counts endpoints — two readings of a B2 potential, by Chapter 2's identity — and carries no
statistics at all.  The `deltaFiniteExperts` factor carries all of it, and inside it `log N` is the
price of the declared B4 envelope.  `PairwiseDesign` shows the same fact from the other side: when
the audited random variable is already a paired difference, the endpoint factor is absent and the
radius is unchanged.

*Demonstrated and true.*  `DemonstratedAtResolution` is a predicate about evidence at a declared
resolution.  `NotDemonstratedAtResolution` does not assert that the true gain is zero.  The
transport lemma `evidenceLowerBound_le_true` is the only bridge between them, and it needs the
one-sided inequality as a hypothesis.

*Declared and realized.*  Every design record below is a declaration.  Validity of a declaration is
a numerical side condition; whether an actual experiment meets it is not a theorem of this file.

`deltaFiniteExperts` and `finite_audit_goodhart` are the native formal sources for the finite-panel
radius and the signed endpoint guarantee.
-/

namespace AuditCP

/-! ## Evidence semantics -/

/-- The conservative effect estimate, `measuredGain - slack`. -/
def evidenceLowerBound (measuredGain slack : ℝ) : ℝ :=
  measuredGain - slack

/-- The gain is demonstrated at the declared resolution: `0 < evidenceLowerBound measuredGain slack`. -/
def DemonstratedAtResolution (measuredGain slack : ℝ) : Prop :=
  0 < evidenceLowerBound measuredGain slack

/-- The gain is not demonstrated at the declared resolution:
`evidenceLowerBound measuredGain slack ≤ 0`. -/
def NotDemonstratedAtResolution (measuredGain slack : ℝ) : Prop :=
  evidenceLowerBound measuredGain slack ≤ 0

/-- The measured gain in units of the uncertainty slack, `measuredGain / slack`. -/
noncomputable def discriminationRatio (measuredGain slack : ℝ) : ℝ :=
  measuredGain / slack

/-- If `measuredGain ≤ trueGain + slack`, then `evidenceLowerBound measuredGain slack ≤ trueGain`. -/
theorem evidenceLowerBound_le_true {measuredGain trueGain slack : ℝ}
    (h : measuredGain ≤ trueGain + slack) :
    evidenceLowerBound measuredGain slack ≤ trueGain := by
  unfold evidenceLowerBound
  linarith

/-- `DemonstratedAtResolution measuredGain slack ↔ slack < measuredGain`. -/
theorem demonstratedAtResolution_iff_slack_lt_gain {measuredGain slack : ℝ} :
    DemonstratedAtResolution measuredGain slack ↔ slack < measuredGain := by
  unfold DemonstratedAtResolution evidenceLowerBound
  constructor <;> intro h <;> linarith

/-- If `measuredGain ≤ slack`, then `NotDemonstratedAtResolution measuredGain slack`. -/
theorem notDemonstrated_of_measuredGain_le_slack {measuredGain slack : ℝ}
    (h : measuredGain ≤ slack) :
    NotDemonstratedAtResolution measuredGain slack := by
  unfold NotDemonstratedAtResolution evidenceLowerBound
  linarith

/-- Given `0 < slack`, `1 < discriminationRatio measuredGain slack ↔
DemonstratedAtResolution measuredGain slack`. -/
theorem one_lt_discriminationRatio_iff {measuredGain slack : ℝ} (hslack : 0 < slack) :
    1 < discriminationRatio measuredGain slack ↔
      DemonstratedAtResolution measuredGain slack := by
  rw [show (1 < discriminationRatio measuredGain slack) ↔ slack < measuredGain by
    simpa [discriminationRatio] using (one_lt_div hslack)]
  exact demonstratedAtResolution_iff_slack_lt_gain.symm

/-! ## Route-specific declarations -/

/-- A numeric declaration for a fixed finite candidate family evaluated on one sealed panel:
`candidateBound`, `panelSize`, `lossRange`, and `failureProbability`. -/
structure FinitePanelDesign where
  candidateBound : ℕ
  panelSize : ℕ
  lossRange : ℝ
  failureProbability : ℝ

/-- The numerical side conditions on a `FinitePanelDesign`: all four fields positive and
`failureProbability ≤ 1`. -/
def FinitePanelDesign.Valid (d : FinitePanelDesign) : Prop :=
  0 < d.candidateBound ∧ 0 < d.panelSize ∧ 0 < d.lossRange ∧
    0 < d.failureProbability ∧ d.failureProbability ≤ 1

/-- The signed two-endpoint resolution of `d`,
`2 * deltaFiniteExperts d.candidateBound d.panelSize d.lossRange d.failureProbability`. -/
noncomputable def FinitePanelDesign.resolution (d : FinitePanelDesign) : ℝ :=
  2 * deltaFiniteExperts d.candidateBound d.panelSize d.lossRange d.failureProbability

/-- If `0 < exactCount ≤ candidateBound`, `0 < panelSize`, `0 ≤ lossRange`, and
`0 < failureProbability`, then
`deltaFiniteExperts exactCount panelSize lossRange failureProbability ≤
deltaFiniteExperts candidateBound panelSize lossRange failureProbability`. -/
theorem deltaFiniteExperts_mono_candidateBound
    {exactCount candidateBound panelSize : ℕ} {lossRange failureProbability : ℝ}
    (hexact : 0 < exactCount) (hbound : exactCount ≤ candidateBound)
    (hpanel : 0 < panelSize) (hloss : 0 ≤ lossRange)
    (hfailure : 0 < failureProbability) :
    deltaFiniteExperts exactCount panelSize lossRange failureProbability ≤
      deltaFiniteExperts candidateBound panelSize lossRange failureProbability := by
  have hexactR : (0 : ℝ) < exactCount := by exact_mod_cast hexact
  have hcandidate : 0 < candidateBound := hexact.trans_le hbound
  have hcandidateR : (0 : ℝ) < candidateBound := by exact_mod_cast hcandidate
  have hboundR : (exactCount : ℝ) ≤ candidateBound := by exact_mod_cast hbound
  have hargExact : (0 : ℝ) < 2 * (exactCount : ℝ) / failureProbability :=
    div_pos (mul_pos (by norm_num) hexactR) hfailure
  have hargBound : (0 : ℝ) < 2 * (candidateBound : ℝ) / failureProbability :=
    div_pos (mul_pos (by norm_num) hcandidateR) hfailure
  have hargLe :
      2 * (exactCount : ℝ) / failureProbability ≤
        2 * (candidateBound : ℝ) / failureProbability :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hboundR (by norm_num)) hfailure.le
  have hlog :
      Real.log (2 * (exactCount : ℝ) / failureProbability) ≤
        Real.log (2 * (candidateBound : ℝ) / failureProbability) :=
    Real.strictMonoOn_log.monotoneOn hargExact hargBound hargLe
  unfold deltaFiniteExperts
  apply mul_le_mul_of_nonneg_left _ hloss
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right hlog
  positivity

/-- A numeric declaration for a reused panel whose transcript has at most `2^transcriptBits`
states, each enabling at most `localCandidateBound` candidates (dwork2015adaptive). -/
structure ReusedPanelDesign where
  transcriptBits : ℕ
  localCandidateBound : ℕ
  panelSize : ℕ
  lossRange : ℝ
  failureProbability : ℝ

/-- The numerical side conditions on a `ReusedPanelDesign`: `localCandidateBound`, `panelSize`,
`lossRange`, `failureProbability` positive and `failureProbability ≤ 1`. -/
def ReusedPanelDesign.Valid (d : ReusedPanelDesign) : Prop :=
  0 < d.localCandidateBound ∧ 0 < d.panelSize ∧ 0 < d.lossRange ∧
    0 < d.failureProbability ∧ d.failureProbability ≤ 1

/-- The maximum reachable class size of `d`, `2 ^ d.transcriptBits * d.localCandidateBound`. -/
def ReusedPanelDesign.masterCandidateBound (d : ReusedPanelDesign) : ℕ :=
  2 ^ d.transcriptBits * d.localCandidateBound

/-- The signed two-endpoint resolution of `d` after pricing its master candidate bound,
`2 * deltaFiniteExperts d.masterCandidateBound d.panelSize d.lossRange d.failureProbability`. -/
noncomputable def ReusedPanelDesign.resolution (d : ReusedPanelDesign) : ℝ :=
  2 * deltaFiniteExperts d.masterCandidateBound d.panelSize d.lossRange d.failureProbability

/-- A numeric declaration for a family of paired comparisons: `comparisonCount`, `panelSize`,
`differenceWidth`, and `failureProbability`. -/
structure PairwiseDesign where
  comparisonCount : ℕ
  panelSize : ℕ
  differenceWidth : ℝ
  failureProbability : ℝ

/-- The numerical side conditions on a `PairwiseDesign`: all four fields positive and
`failureProbability ≤ 1`. -/
def PairwiseDesign.Valid (d : PairwiseDesign) : Prop :=
  0 < d.comparisonCount ∧ 0 < d.panelSize ∧ 0 < d.differenceWidth ∧
    0 < d.failureProbability ∧ d.failureProbability ≤ 1

/-- The simultaneous paired-comparison radius of `d`,
`deltaFiniteExperts d.comparisonCount d.panelSize d.differenceWidth d.failureProbability`. -/
noncomputable def PairwiseDesign.radius (d : PairwiseDesign) : ℝ :=
  deltaFiniteExperts d.comparisonCount d.panelSize d.differenceWidth d.failureProbability

/-! ## Transport and design equations -/

/-- Under `UniformDev F Ehat E Δ` and `Admissible g F`,
`evidenceLowerBound (cumCP Ehat g T) (2Δ) ≤ cumCP E g T` at every horizon `T`. -/
theorem goodhart_evidenceLowerBound
    {Candidate : Type*} {F : AuditEnvelope Candidate} {Ehat E : AuditPotential Candidate} {Δ : ℝ}
    (hUD : UniformDev F Ehat E Δ) {g : AuditTrajectory Candidate} (hg : Admissible g F) (T : ℕ) :
    evidenceLowerBound (cumCP Ehat g T) (2 * Δ) ≤ cumCP E g T := by
  exact evidenceLowerBound_le_true (finite_audit_goodhart hUD hg T)

/-- The panel size obtained by inverting the finite-experts resolution formula at
`targetResolution`,
`2 * lossRange ^ 2 * log(2 * candidateBound / failureProbability) / targetResolution ^ 2`. -/
noncomputable def panelSizeForResolution
    (candidateBound : ℕ) (lossRange failureProbability targetResolution : ℝ) : ℝ :=
  2 * lossRange ^ 2 * Real.log (2 * (candidateBound : ℝ) / failureProbability) /
    targetResolution ^ 2

/-- If `targetResolution ≠ 0`, then
`panelSizeForResolution candidateBound lossRange failureProbability targetResolution *
targetResolution ^ 2 = 2 * lossRange ^ 2 * log(2 * candidateBound / failureProbability)`. -/
theorem panelSizeForResolution_mul_sq
    (candidateBound : ℕ) (lossRange failureProbability targetResolution : ℝ)
    (hresolution : targetResolution ≠ 0) :
    panelSizeForResolution candidateBound lossRange failureProbability targetResolution *
        targetResolution ^ 2 =
      2 * lossRange ^ 2 * Real.log (2 * (candidateBound : ℝ) / failureProbability) := by
  unfold panelSizeForResolution
  field_simp

/-- The direct information-bit budget at normalized tolerance `normalizedTolerance`,
`(panelSize * normalizedTolerance ^ 2 / 2 - log(1 / failureProbability)) / log 2` (dwork2015adaptive). -/
noncomputable def reuseBitBudget
    (panelSize : ℕ) (normalizedTolerance failureProbability : ℝ) : ℝ :=
  ((panelSize : ℝ) * normalizedTolerance ^ 2 / 2 -
      Real.log (1 / failureProbability)) / Real.log 2

/-- If `log 2 ≠ 0`, then `reuseBitBudget panelSize normalizedTolerance failureProbability * log 2
+ log(1 / failureProbability) = panelSize * normalizedTolerance ^ 2 / 2`. -/
theorem reuseBitBudget_mul_log_two
    (panelSize : ℕ) (normalizedTolerance failureProbability : ℝ)
    (hlog : Real.log 2 ≠ 0) :
    reuseBitBudget panelSize normalizedTolerance failureProbability * Real.log 2 +
        Real.log (1 / failureProbability) =
      (panelSize : ℝ) * normalizedTolerance ^ 2 / 2 := by
  unfold reuseBitBudget
  field_simp
  ring

/-- The transcript-bit budget of `d` at normalized tolerance `normalizedTolerance` for the finite
reachable-envelope route,
`(d.panelSize * normalizedTolerance ^ 2 / 2 -
log(2 * d.localCandidateBound / d.failureProbability)) / log 2`. -/
noncomputable def ReusedPanelDesign.finiteEnvelopeTranscriptBitBudget
    (d : ReusedPanelDesign) (normalizedTolerance : ℝ) : ℝ :=
  ((d.panelSize : ℝ) * normalizedTolerance ^ 2 / 2 -
      Real.log (2 * (d.localCandidateBound : ℝ) / d.failureProbability)) / Real.log 2

/-- If `log 2 ≠ 0`, then `d.finiteEnvelopeTranscriptBitBudget normalizedTolerance * log 2 +
log(2 * d.localCandidateBound / d.failureProbability) =
d.panelSize * normalizedTolerance ^ 2 / 2`. -/
theorem ReusedPanelDesign.finiteEnvelopeTranscriptBitBudget_mul_log_two
    (d : ReusedPanelDesign) (normalizedTolerance : ℝ) (hlog : Real.log 2 ≠ 0) :
    d.finiteEnvelopeTranscriptBitBudget normalizedTolerance * Real.log 2 +
        Real.log (2 * (d.localCandidateBound : ℝ) / d.failureProbability) =
      (d.panelSize : ℝ) * normalizedTolerance ^ 2 / 2 := by
  unfold ReusedPanelDesign.finiteEnvelopeTranscriptBitBudget
  field_simp
  ring

/-- If `weight` is nonnegative and `measured j ≤ truth j + slack j` at every component `j`, then
`∑ j, weight j * measured j ≤ (∑ j, weight j * truth j) + ∑ j, weight j * slack j`. -/
theorem weightedBattery_bound
    {Component : Type*} [Fintype Component]
    (weight measured truth slack : Component → ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (hcomponent : ∀ j, measured j ≤ truth j + slack j) :
    (∑ j, weight j * measured j) ≤
      (∑ j, weight j * truth j) + ∑ j, weight j * slack j := by
  calc
    (∑ j, weight j * measured j) ≤ ∑ j, weight j * (truth j + slack j) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hcomponent j) (hweight j)
    _ = (∑ j, weight j * truth j) + ∑ j, weight j * slack j := by
      simp only [mul_add, Finset.sum_add_distrib]

end AuditCP
