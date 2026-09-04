import AuditCP.PaperMetrology

/-!
# Target 13 — a moving target, and what the product index costs

A benchmark whose target is versioned reports a ledger version by version.  That ledger is **not**
conservative: reading the potential of version `v j` at the candidate the learner occupies when the
target moves to `v (j+1)` leaves a residue.  This module states the residue exactly, and prices the
index that removes it.

## The defect is a sum of bridge terms

    ∑ⱼ (E (v j) (g j) − E (v j) (g (j+1)))
      = cumCP Ê ĝ k  +  ∑ⱼ (E (v (j+1)) − E (v j)) (g (j+1))

with `Ê (c, w) := E w c` and `ĝ j := (g j, v j)`.  The first term is the ledger on the product index
`Candidate × Version`, where `AuditCP.cumCP_telescope` runs across version boundaries; the second is
one term per version transition, each the disagreement of consecutive targets at the candidate the
learner occupied when the target moved.  That candidate is the bridge state, and the sum vanishes
exactly when the target holds still.

## The product index is a price, not a relabelling

`Candidate × Version` is a `Fintype` when both factors are, with cardinality `N * K`, and
cardinality is precisely what a finite-experts declaration reads.  The discounted-shaping crossover
in this library records the negative case in the same vocabulary: a step-dependent generator on
`ℕ × S` is priced by no lemma in either corpus, because `ℕ` carries no `Fintype` instance and the
lifted index therefore has no cardinality to charge.  So the missing link is the instance, not the
arithmetic.

## Named here, deliberately not used below

* `AuditCPRL.shapePot` and `AuditCP.finite_experts_uniformDev` — the negative case just described.
  `shapePot`'s index `ℕ × S` is the one the second of these cannot price, and neither declaration is
  needed for anything proved here.
* `AuditCPRL.panelSize_affine_in_disclosureBits` — the class-growth arithmetic, banked in
  `AuditCPRL/Disclosure.lean` and not restated below.

## The route comparison is a single factor

Both routes declare the same product class — a simultaneous guarantee over `K` version-targets has
no choice about that — so the class term `2 L² log K / ε²` is paid by both and cancels.  Stating the
comparison at `candidateBound := N * K` on *both* sides is what makes the cancellation visible in
the statement rather than in this prose.  What survives is the `K`-fold endpoint factor:
`panelSize_segmented_eq_sq_mul` says the segmented route costs exactly `K²`.

Tasks and candidates are one currency.  Both are indices, both are paid in log-cardinality of the
declared class, and neither is paid in occurrences.

-/

namespace AuditCPRL

open AuditCP

/-- `∑_{j<k} (E (v j) (g j) - E (v j) (g (j+1))) = cumCP (fun p => E p.2 p.1) (fun j => (g j, v j))
k + ∑_{j<k} (E (v (j+1)) (g (j+1)) - E (v j) (g (j+1)))`. -/
theorem versioned_ledger_eq_product_add_bridge
    {Candidate Version : Type*} (E : Version → AuditPotential Candidate)
    (g : AuditTrajectory Candidate) (v : ℕ → Version) (k : ℕ) :
    (∑ j ∈ Finset.range k, (E (v j) (g j) - E (v j) (g (j + 1))))
      = cumCP (fun p : Candidate × Version => E p.2 p.1) (fun j => (g j, v j)) k
        + ∑ j ∈ Finset.range k, (E (v (j + 1)) (g (j + 1)) - E (v j) (g (j + 1))) := by
  have key : (∑ j ∈ Finset.range k, (E (v j) (g j) - E (v j) (g (j + 1))))
      - (∑ j ∈ Finset.range k, (E (v (j + 1)) (g (j + 1)) - E (v j) (g (j + 1))))
      = E (v 0) (g 0) - E (v k) (g k) := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : ∀ j ∈ Finset.range k,
        (E (v j) (g j) - E (v j) (g (j + 1)))
            - (E (v (j + 1)) (g (j + 1)) - E (v j) (g (j + 1)))
          = (fun i => E (v i) (g i)) j - (fun i => E (v i) (g i)) (j + 1) := by
      intro j _; simp only; ring
    rw [Finset.sum_congr rfl hcongr]
    exact Finset.sum_range_sub' (fun i => E (v i) (g i)) k
  rw [cumCP_telescope]
  simp only
  linarith [key]

/-- If the version schedule is constant through `k` (`∀ j < k, v (j+1) = v j`), then
`∑_{j<k} (E (v (j+1)) (g (j+1)) - E (v j) (g (j+1))) = 0`. -/
theorem versioned_bridge_vanishes_of_constant_version
    {Candidate Version : Type*} (E : Version → AuditPotential Candidate)
    (g : AuditTrajectory Candidate) (v : ℕ → Version) (k : ℕ)
    (hconst : ∀ j < k, v (j + 1) = v j) :
    (∑ j ∈ Finset.range k, (E (v (j + 1)) (g (j + 1)) - E (v j) (g (j + 1)))) = 0 :=
  Finset.sum_eq_zero fun j hj => by
    rw [hconst j (Finset.mem_range.1 hj), sub_self]

/-- `Fintype.card (Candidate × Version) = Fintype.card Candidate * Fintype.card Version`. -/
theorem versionedClass_card {Candidate Version : Type*} [Fintype Candidate] [Fintype Version] :
    Fintype.card (Candidate × Version) = Fintype.card Candidate * Fintype.card Version :=
  Fintype.card_prod Candidate Version

/-- If `K ≠ 0`, then `panelSizeForResolution (N * K) L δ (ε / K) =
K ^ 2 * panelSizeForResolution (N * K) L δ ε`. -/
theorem panelSize_segmented_eq_sq_mul (N K : ℕ) (L δ ε : ℝ) (hK : (K : ℝ) ≠ 0) :
    panelSizeForResolution (N * K) L δ (ε / (K : ℝ))
      = (K : ℝ) ^ 2 * panelSizeForResolution (N * K) L δ ε := by
  unfold panelSizeForResolution
  field_simp

/-- If `UniformDev F Ehat E Δ` and `Admissible (fun j => (g j, v j)) F`, then
`cumCP Ehat (fun j => (g j, v j)) k ≤ cumCP E (fun j => (g j, v j)) k + 2Δ`. -/
theorem versioned_product_goodhart
    {Candidate Version : Type*} {F : AuditEnvelope (Candidate × Version)}
    {Ehat E : AuditPotential (Candidate × Version)} {Δ : ℝ}
    (hUD : UniformDev F Ehat E Δ)
    (g : AuditTrajectory Candidate) (v : ℕ → Version)
    (hadm : Admissible (fun j => (g j, v j)) F) (k : ℕ) :
    cumCP Ehat (fun j => (g j, v j)) k ≤ cumCP E (fun j => (g j, v j)) k + 2 * Δ :=
  finite_audit_goodhart hUD hadm k

end AuditCPRL
