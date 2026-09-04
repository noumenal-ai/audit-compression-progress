import AuditCP.Vendored.FinitePMF
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Base — the degenerate base of the Audit-CP thesis

This module declares the base types of the whole argument.  Every declaration in the paper closure
(`Basic`, `Telescope`, `FiniteAudit`, `FiniteExperts`, `StructuralAudit`, `ConditionalAudit`,
`FilteredAudit`, `FiniteBlackwell`, `FiniteBlackwellDecision`, `FiniteBlackwellBrier`,
`EntropyFloor`, `PaperMetrology`) is a refinement of one of these, and no module redefines any of
them.

## The independence result

Dependency analysis of the 178 declarations (what each unfolds to, and what each module imports)
leaves exactly **four independent base types**, distinguished by their *value* carrier:

| base | value carrier | why irreducible |
| --- | --- | --- |
| `AuditIndex` | none (a bare sort) | carries no structure; every other base is built over it |
| `AuditPotential` | `ℝ` | a real reading of an index; not derivable from a law |
| `AuditExperiment` | `PMF` | `PMF X` is `X → ℝ≥0∞` with a summability field, not `X → ℝ` |
| `AuditSampleLaw` | `MeasureTheory.Measure` | a σ-additive law on a σ-algebra, not a discrete law |

Three further types are declared here because more than one module consumes them, but they are
**refinements, not independent bases**: `AuditTrajectory` (index + the stage carrier `ℕ`),
`AuditEnvelope` (index + `Prop`), and `AuditChannel` (an experiment whose parameter carries a
permitted/protected product split).

Everything else in the closure is a refinement of one of these seven.  In particular the vendored
`FinitePMF Y` is `AuditPotential Y` constrained to the simplex (its `prob` field is exactly a real
reading, its two other fields are the constraint), and Mathlib's `ProbabilityTheory.Kernel` is
`AuditSampleLaw` made into a measurable family.

## The three law carriers, and how they are related

`AuditExperiment` and `AuditSampleLaw` are two law carriers, and `AuditPotential`-constrained
`FinitePMF` is a third representation of a discrete law.  The sealing development (`AuditSealed`,
`BlackwellBelow`, `equalPriorBayesError`) is written on `PMF`, the scoring and total-variation
development (`finitePMFTotalVariation`, `finiteBrierPosteriorGain`, `finitePMFEventProb`) on
`FinitePMF`, and the concentration development on `Measure`.

`AuditCP.LawBridge` relates them, and B5 is the one they are related to.  On a finite type `PMF`
and `FinitePMF` are mutually inverse images of each other, and total variation and deterministic
pushforward commute with that pair; `Measure` is the image of `PMF` under Mathlib's `PMF.toMeasure`,
and the vendored expectation is the integral against it.  The `Measure` leg is one-directional and
stays so: the thesis needs no `PMF` built from an arbitrary `Measure`, because B7 carries the panel
and training laws, which are not discrete by construction.

Naming the three as separate bases here remains correct, because the bridge relates carriers and
does not merge types: the value carriers `ℝ`, `PMF` and `Measure` are still three, and the
independence argument above is untouched.  What has closed is the *transport* obligation — a
statement proved on one discrete carrier is now a statement about the other.  Each base type below
is grounded and witnessed in the section that follows.

## The seven base types, grounded

Each base type is witnessed by a concrete, non-vacuous instance elsewhere in the closure.

**B1 — `AuditIndex`.** Every carrier in the closure is this sort in one of its roles — audited
candidate (`ι`, `Candidate`), experiment parameter (`Θ`), permitted public state (`S`), protected
audit state (`A`), released observation (`Y`), transcript alphabet (`Transcript`), audit item (`Z`),
sample space (`Ω`, `Ωtrain`, `Ωaudit`), interaction history (`H`), control (`U`), response (`O`),
battery component (`Component`).  The roles are positional and instance-carried, not type-formed: no
theorem in the closure needs two *different* bare sorts, only the same sort in two positions.
**Grounds:** every other base type below, hence every refinement in the closure. **Witnessed by:**
`AuditCP.BlackwellFineSymbol` ( = `Option Bool`, `FiniteBlackwellDecision`) and `Bool` in
`boolAuditDisclosure` (`FilteredAudit`), inhabited instantiations used in theorems with non-trivial
numerical content, so the sort is not vacuous.

**B2 — `AuditPotential`.** Independent of B5 and B7 because its value carrier is `ℝ`, which is
neither `PMF` nor `Measure`. **Grounds:** the measured potential `Ehat` and the population potential
`E` throughout the closure; `cumCP`; both arguments of `UniformDev`; `populationLoss Q loss` and
`empiricalLoss loss · panel` (`FiniteExperts`); `fun θ => crossEntropyFinitePMF Q (P θ)` and its
conditional form (`EntropyFloor`); the `prob` field of the vendored `FinitePMF`, hence
`finitePMFTotalVariation`, `finiteExpectedBrier`, `finiteBrierPosteriorGain` and
`finitePMFEventProb`; the measured/true/slack coordinates of `PaperMetrology`. **Witnessed by:**
`auditCE ε p` (`Basic`), which `auditCE_mem_Icc` places in `Set.Icc 0 (-log ε)` — a bounded,
non-constant reading — with `deltaFiniteExperts N n L δ` (`FiniteExperts`) supplying the matching
numerical `Δ` slot.

**B3 — `AuditTrajectory`.** A refinement of B1, not an independent base: it is B1 read off the stage
carrier `ℕ`. **Grounds:** the trajectory `g` in `cumCP`, `Admissible`, `finite_audit_goodhart` and
every random/kernel/adaptive lift of it; `endpointPairPath` (`FiniteBlackwell`);
`FilteredDisclosure.candidateProcess policy · ω` (`FilteredAudit`); the transcript process
`ℕ → Ω → Transcript` is this type at the reading `Ω → Transcript`. **Witnessed by:**
`endpointPairPath endpoints`, whose exact ledger value is computed by `cumCP_endpointPairPath`, and
`boolAuditDisclosure.candidateProcess (fun τ _ => τ)`, whose two audit-conditioned values are proved
distinct by `boolAuditDisclosure_is_auditDependent`.

**B4 — `AuditEnvelope`.** A refinement of B1: B1 read into `Prop`. **Grounds:** `F` in `UniformDev`
and `Admissible`; the random class `F : Ωtrain → Set ι` (`StructuralAudit`, `ConditionalAudit`); the
reachable envelope `↑(reachableEnvelope choices)` (`FilteredAudit`); `Set.univ` in the
finite-experts route. **Witnessed by:** `reachableEnvelope choices` (`FilteredAudit`), a `Finset`
whose cardinality is priced by `reachableEnvelope_card_le_of_disclosureBudget` at `2 ^ bits * M`, so
the envelope is inhabited, finite and priced, not a formal placeholder.

**B5 — `AuditExperiment`.** Independent of B2 and B7 because its value carrier is Mathlib's `PMF`, a
map into `ℝ≥0∞` bundled with a summability field, and is therefore neither an `AuditPotential` nor
an `AuditSampleLaw`. **Grounds:** `BlackwellBelow` and `BlackwellEquivalent` and their reflexivity,
transitivity and decision-simulation lemmas; `publicOnlyExperiment`; `learnerExperiment`; and,
through the split refinement B6, the whole sealing development. **Witnessed by:** `fairBool`
( = `PMF.uniformOfFintype Bool`, with `fairBool_apply` giving mass `1/2` at each point), a non-Dirac
experiment, against `publicOnlyExperiment`, a Dirac one, so the type is inhabited by laws that are
provably not Blackwell-equivalent whenever `xorTranscript_not_sealed` applies. This base is the
closure's single law carrier: on a finite type the vendored `FinitePMF` is a proven image of `PMF`,
in both directions and not merely as a retraction — `AuditCP.LawBridge` constructs
`finitePMFOfPMF` and `FinitePMF.toPMF` and proves both round trips (`finitePMFOfPMF_toPMF`,
`toPMF_finitePMFOfPMF`). The two functionals the thesis reads off a law commute with that image —
total variation by `finiteTotalVariation_eq_finitePMFTotalVariation` and its converse, deterministic
coarse-graining by `pushforwardFinitePMF_finitePMFOfPMF` — so a statement proved on either carrier
is a statement about the other, and `deterministicGarbling_reverses_signedProgress_pmf` is the
Chapter 9 reversal witness carried onto this base. B7 `AuditSampleLaw` is reached from here by
Mathlib's `PMF.toMeasure`, and `expectFinitePMF_eq_integral_toMeasure` identifies the vendored
expectation with the integral against that measure. The bridge relates the carriers; it does not
merge the base *types*: a `PMF` is still not an `AuditPotential` and still not a `Measure`, and B2
is still not derivable from a law — what the bridge relates to B5 is B2 *constrained to the simplex
on a finite type*, which is the only place either direction is available. See the joint's price in
`AuditCP.LawBridge`: `Fintype` on one side, `prob_nonneg` on the other.

**B6 — `AuditChannel`.** A refinement of B5, not an independent base: `AuditChannel S A Y` is
definitionally `AuditExperiment (S × A) Y`. The split is positional — the protected coordinate is
the one `AuditSealed` quantifies over — which is why the sealing predicate is a property of the
interface and not of the learner. **Grounds:** `AuditSealed` and `FactorsThroughPublic` and their
equivalence (F1); `auditBlindPostprocess` and downstream closure (F9); `deterministicAuditChannel`
and F5; `testedResponseChannel` and the F8 converse; the interactive step and `iterateInteraction`;
`auditSealed_iff_no_binary_decision_advantage` (F3); the candidate channel `C : S × A → PMF G` of
F10 and the endpoint-pair channel of F14. **Witnessed by:**
`xorTranscriptChannel : Unit × Bool → PMF (Bool × Bool)`, proved *not* sealed
(`xorTranscript_not_sealed`) while every time-marginal is sealed (`xorTranscript_marginals_sealed`)
and the protected bit is decoded exactly (`xorTranscript_decodes_audit`); and the deterministic
`3 → 2` garbling `blackwellMerge`, whose exact numerics are computed in
`deterministicGarbling_reverses_signedProgress`.

**B7 — `AuditSampleLaw`.** Independent of B5 because a `Measure` is σ-additive on a σ-algebra rather
than a discrete mass function, and the closure contains no map either way. Mathlib's
`ProbabilityTheory.Kernel` is this base made into a measurable family and is used unchanged; the
closure declares no law type of its own. **Grounds:** the audit distribution `Q` and the panel law
`Measure.pi (fun _ : Fin n => Q)` (`FiniteExperts`); `μtrain`, `μaudit` and the product law
(`StructuralAudit`); the kernel composition `μtrain.compProd κ` (`ConditionalAudit`, `FilteredAudit`,
`FiniteBlackwell`'s endpoint theorem); every `ENNReal`-valued failure bound in the closure.
**Witnessed by:** `Measure.pi (fun _ : Fin n => Q)` with `finite_experts_iid_uniformDev`, which gives
that law an explicit lower bound `1 - δ` on the uniform-deviation event at the radius
`deltaFiniteExperts (Fintype.card ι) n (b - a) δ`; the numerical content is therefore realized, not
assumed.
-/

universe u v w

namespace AuditCP

/-! ## B1 — the degenerate carrier -/

/-- B1 — `AuditIndex` is the bare sort `Type u`, with no additional structure. -/
abbrev AuditIndex : Type (u + 1) := Type u

/-! ## B2 — the real reading -/

/-- B2 — `AuditPotential ι` is the type of real-valued readings `ι → ℝ` of the index `ι`. -/
abbrev AuditPotential (ι : AuditIndex.{u}) : Type u := ι → ℝ

/-! ## B3, B4 — refinements of B1 consumed by more than one module -/

/-- B3 — `AuditTrajectory ι` is the type of stage-indexed selections `ℕ → ι` of the index `ι`. -/
abbrev AuditTrajectory (ι : AuditIndex.{u}) : Type u := ℕ → ι

/-- B4 — `AuditEnvelope ι` is the type of subsets `Set ι` of the index `ι`. -/
abbrev AuditEnvelope (ι : AuditIndex.{u}) : Type u := Set ι

/-! ## B5, B6 — the discrete interface -/

/-- B5 — `AuditExperiment Θ X` is the type of parameter-indexed discrete observation laws
`Θ → PMF X`. -/
abbrev AuditExperiment (Θ : AuditIndex.{u}) (X : AuditIndex.{v}) : Type (max u v) := Θ → PMF X

/-- B6 — `AuditChannel S A Y` is `AuditExperiment (S × A) Y`, an experiment whose parameter is
split into a public coordinate `S` and an audit coordinate `A`. -/
abbrev AuditChannel (S : AuditIndex.{u}) (A : AuditIndex.{v}) (Y : AuditIndex.{w}) :
    Type (max u v w) :=
  AuditExperiment (S × A) Y

/-! ## B7 — the measured law -/

/-- B7 — `AuditSampleLaw Ω` is `MeasureTheory.Measure Ω`, a σ-additive probability law on the
measurable space `Ω`. -/
abbrev AuditSampleLaw (Ω : AuditIndex.{u}) [MeasurableSpace Ω] : Type u :=
  MeasureTheory.Measure Ω

end AuditCP
