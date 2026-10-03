import AuditCP

/-!
# Axiom audit

Every declaration cited in the paper is listed below, grouped by the chapter that proves it, in the
order of `AuditCP/Paper.lean`.  Each must depend only on the three standard Lean/Mathlib axioms
`[propext, Classical.choice, Quot.sound]`.  A line that additionally reported `sorryAx` would mark
an unfinished proof.  None does.

Run after `lake build` with:  `lake env lean Check.lean`
-/

-- Chapter 2, `Telescope`: the ledger is exact.
#print axioms AuditCP.cumCP_telescope
#print axioms AuditCP.cumCP_le_of_lb

-- Chapter 2½, `CyberneticCocycle`: exact change laws are potential differences.
#print axioms AuditCP.isChangeCocycle_iff_exists_potential
#print axioms AuditCP.IsChangeCocycle.closed_path_eq_zero
#print axioms AuditCP.clipped_change_closed_loop_counterexample

-- Chapter 3, `FiniteAudit`: the slack `2Δ`.
#print axioms AuditCP.finite_audit_goodhart

-- Chapter 4, `FiniteExperts`: the finite-class radius.
#print axioms AuditCP.deltaFiniteExperts
#print axioms AuditCP.finite_experts_iid_uniformDev
#print axioms AuditCP.finite_experts_iid_badEvent_le

-- Chapter 7, `FilteredAudit`: the transcript envelope.
#print axioms AuditCP.reachableEnvelope_card_le_of_disclosureBudget

-- Chapters 8 to 10, `FiniteBlackwell`, `FiniteBlackwellDecision`, `LawBridge`,
-- `FiniteBlackwellBrier`: sealing as a property of the interface.
#print axioms AuditCP.auditSealed_iff_factorsThroughPublic
#print axioms AuditCP.learner_blackwellBelow_publicOnly_iff_auditSealed
#print axioms AuditCP.deterministicAuditChannel_sealed_iff
#print axioms AuditCP.auditSealed_iff_no_binary_decision_advantage
#print axioms AuditCP.deterministicGarbling_reverses_signedProgress_pmf
#print axioms AuditCP.finiteBrierPosteriorGain_eq_zero_iff_auditSealed

-- Chapter 11, `EntropyFloor`: the entropy floor.
#print axioms AuditCP.klDivFinitePMF_nonneg
#print axioms AuditCP.entropy_floor_budget
#print axioms AuditCP.crossEntropyFinitePMF_eq_entropy_add_kl
#print axioms AuditCP.entropy_le_crossEntropyFinitePMF
#print axioms AuditCP.entropy_floor_budget_crossEntropy
#print axioms AuditCP.condCrossEntropyFinitePMF_eq_entropy_add_kl
#print axioms AuditCP.condKLDivFinitePMF_nonneg
#print axioms AuditCP.condEntropy_le_condCrossEntropy
#print axioms AuditCP.cond_entropy_floor_budget_crossEntropy

-- Chapter 12, `PaperMetrology`: the printed interval.
#print axioms AuditCP.auditBlind_pairwise_evidenceInterval

-- Chapter 13, `AuditCPRL.L0`: the Goodhart gap is the centered endpoint increment.
#print axioms AuditCPRL.cumCP_sub_cumCP_eq_centered_increment
#print axioms AuditCPRL.cumCP_sub_cumCP_le_of_endpoints
#print axioms AuditCPRL.abs_cumCP_sub_cumCP_le_of_endpoints
#print axioms AuditCPRL.finite_audit_goodhart_twoPoint

-- Chapter 14, `AuditCPRL.Shaping`: shaping with an estimated potential.
#print axioms AuditCPRL.approx_shaping_single
#print axioms AuditCPRL.approx_shaping_pairwise
#print axioms AuditCPRL.approx_shaping_order_preserved
#print axioms AuditCPRL.approx_shaping_argmax_preserved
#print axioms AuditCPRL.approx_shaping_ranking_preserved
#print axioms AuditCPRL.approx_shaping_slack_tendsto
#print axioms AuditCPRL.cumCP_shapePot_const_shift
#print axioms AuditCPRL.shaping_from_panel_trained_potential

-- Chapter 15, `AuditCPRL.Convergence`: a convergent run exhausts its ledger.
#print axioms AuditCPRL.iteratesOfResidual_ledger_capped_and_exhausted
#print axioms AuditCPRL.iteratesOfResidual_lifetime_credit

-- Chapter 17, `AuditCPRL.BellmanLadder`: a predeclared Q-function ladder on one panel.
#print axioms AuditCPRL.qlearning_ladder_sealedPanel_goodhart
#print axioms AuditCPRL.populationLoss_update_sq_eq_bellman_sq_add_var

-- Chapter 18, `AuditCPRL.ReusedPanel`: policy improvement on a reused panel.
#print axioms AuditCPRL.policyImprovement_reusedPanel_goodhart
#print axioms AuditCPRL.policyImprovement_reusedPanel_allHorizons
#print axioms AuditCPRL.policyImprovement_reusedPanel_bitPriced

-- Chapter 19, `AuditCPRL.SelfModification`: the self-modifying learner.
#print axioms AuditCPRL.transcriptEndpoints_bitPriced_goodhart
#print axioms AuditCPRL.qBall_invariant_of_stepSize_mem_Icc
#print axioms AuditCPRL.qBall_budget_of_reward_cap
#print axioms AuditCPRL.selfModifying_qlearning_audit_goodhart
#print axioms AuditCPRL.selfModifying_qlearning_audit_goodhart_twoPoint
#print axioms AuditCPRL.selfModifying_qlearning_audit_goodhart_bitPriced
#print axioms AuditCPRL.selfModifying_stepSize_audit_goodhart_fixedWorld

-- Chapter 20, `AuditCPRL.Concealment`: marginal tests cannot certify concealment.
#print axioms AuditCPRL.stateLaw_padChain_eq
#print axioms AuditCPRL.padTwoStep_decodes
#print axioms AuditCPRL.padTwoStep_marginals_sealed
#print axioms AuditCPRL.padTwoStep_not_sealed
#print axioms AuditCPRL.marginal_tests_cannot_certify_concealment

-- Chapter 21, `AuditCPRL.Occupancy`: state aggregation can reverse occupancy progress.
#print axioms AuditCPRL.finiteMRP_occupancy_iff_fullSupport
#print axioms AuditCPRL.stateAggregation_reverses_occupancy_progress

-- Chapter 22, `AuditCPRL.IntrinsicBudget`: an audited intrinsic reward is budgeted.
#print axioms AuditCPRL.intrinsic_return_le_condKL
#print axioms AuditCPRL.mrp_intrinsic_return_budget
#print axioms AuditCPRL.mrp_no_unaudited_state

-- Chapter 23, `AuditCPRL.Disclosure`: disclosure and panel size exchange.
#print axioms AuditCPRL.sealed_adaptiveEndpoints_goodhart
#print axioms AuditCPRL.sealed_adaptiveEndpoints_goodhart_iidPanel
#print axioms AuditCPRL.reachableEnvelope_card_eq_two_pow_bits_mul
#print axioms AuditCPRL.panelSize_affine_in_disclosureBits

-- Chapter 24, `AuditCPRL.VersionedTarget`: a bridge state across a target version.
#print axioms AuditCPRL.versioned_ledger_eq_product_add_bridge
#print axioms AuditCPRL.versioned_bridge_vanishes_of_constant_version
#print axioms AuditCPRL.versioned_product_goodhart

-- Chapter 25, `AuditCPRL.Milestone`: demonstrable milestones.
#print axioms AuditCPRL.demonstrable_milestone_count_le
