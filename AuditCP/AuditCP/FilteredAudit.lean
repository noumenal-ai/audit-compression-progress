import AuditCP.ConditionalAudit
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Probability.Process.Adapted

/-!
# Chapter 7 — the learner adapts and the interface discloses

Chapters 3 to 6 let the learner adapt inside a declared B4 envelope (dwork2015adaptive; blum2015ladder).  This chapter lets the
*interface* move too, and prices it.  A filtration records what a world-agent system may know at
each stage; an adapted transcript supplies the observable history; a measurable policy then induces
an adapted candidate process, which is a B3 `AuditTrajectory` read off the transcript rather than
chosen in advance.

Two obligations that look like one are separated here and never recombined.  Non-anticipation is
adaptedness and is proved from measurability of the policy.  Statistical reuse is a capacity
obligation and is proved from cardinality: every transcript-conditioned candidate must lie inside a
predeclared reachable B4 envelope, whose size is bounded by `2 ^ bits * M`.  Measurability buys
nothing statistical, and cardinality buys nothing about anticipation.

This is where the price of the audit becomes visible as a channel capacity of the disclosure
interface, measured in bits, rather than as a model capacity of the learner.  The boundary is
stated honestly by the same arithmetic: a loop leaking `b` bits per round for `T` rounds has
`bits = T * b`, and the radius returns to `√T`.
-/

open MeasureTheory ProbabilityTheory

namespace AuditCP

universe u v w

/-- A staged information interface: a measurable transcript `ℕ → Ω → Transcript` adapted to a
filtration on `Ω`. -/
structure FilteredDisclosure
    (Ω : Type u) (Transcript : Type v)
    [MeasurableSpace Ω] [MeasurableSpace Transcript] where
  filtration : Filtration ℕ ‹MeasurableSpace Ω›
  transcript : ℕ → Ω → Transcript
  adapted : Adapted filtration transcript

/-- The candidate process induced by applying `policy` to the transcript disclosed at each stage,
`fun n ω => policy (D.transcript n ω) n`. -/
def FilteredDisclosure.candidateProcess
    {Ω : Type u} {Transcript : Type v} {Candidate : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Transcript]
    (D : FilteredDisclosure Ω Transcript)
    (policy : Transcript → AuditTrajectory Candidate) : ℕ → Ω → Candidate :=
  fun n ω => policy (D.transcript n ω) n

/-- If every stage coordinate of `policy` is measurable, the induced candidate process
`D.candidateProcess policy` is adapted to `D.filtration`. -/
theorem FilteredDisclosure.candidateProcess_adapted
    {Ω : Type u} {Transcript : Type v} {Candidate : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Transcript] [MeasurableSpace Candidate]
    (D : FilteredDisclosure Ω Transcript)
    (policy : Transcript → AuditTrajectory Candidate)
    (hpolicy : ∀ n, Measurable (fun τ => policy τ n)) :
    Adapted D.filtration (D.candidateProcess policy) := by
  intro n
  exact (hpolicy n).comp (D.adapted n)

/-- The transcript alphabet has at most `2^bits` observable states (dwork2015adaptive; blum2015ladder). -/
def HasDisclosureBudget (Transcript : Type v) [Fintype Transcript] (bits : ℕ) : Prop :=
  Fintype.card Transcript ≤ 2 ^ bits

/-- The union over all transcripts of their enabled candidate sets, `⋃ τ, choices τ` (dwork2015adaptive; blum2015ladder). -/
noncomputable def reachableEnvelope
    {Transcript : Type v} {Candidate : Type w} [Fintype Transcript]
    (choices : Transcript → Finset Candidate) : Finset Candidate := by
  classical
  exact Finset.univ.biUnion choices

/-- If `candidate ∈ choices τ` for some `τ`, then `candidate ∈ reachableEnvelope choices`. -/
theorem mem_reachableEnvelope
    {Transcript : Type v} {Candidate : Type w} [Fintype Transcript]
    (choices : Transcript → Finset Candidate) (τ : Transcript) {candidate : Candidate}
    (hcandidate : candidate ∈ choices τ) :
    candidate ∈ reachableEnvelope choices := by
  classical
  exact Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ τ, hcandidate⟩

/-- If every stage of `policy` selects from `choices` at its transcript, then the realized
candidate process at `ω` is admissible for `reachableEnvelope choices`. -/
theorem FilteredDisclosure.candidateProcess_admissible
    {Ω : Type u} {Transcript : Type v} {Candidate : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Transcript] [Fintype Transcript]
    (D : FilteredDisclosure Ω Transcript)
    (choices : Transcript → Finset Candidate)
    (policy : Transcript → AuditTrajectory Candidate)
    (hpolicy : ∀ τ n, policy τ n ∈ choices τ) (ω : Ω) :
    Admissible (fun n => D.candidateProcess policy n ω) ↑(reachableEnvelope choices) := by
  intro n
  exact mem_reachableEnvelope choices (D.transcript n ω)
    (hpolicy (D.transcript n ω) n)

/-- If each transcript enables at most `M` candidates, then
`(reachableEnvelope choices).card ≤ Fintype.card Transcript * M`. -/
theorem reachableEnvelope_card_le
    {Transcript : Type v} {Candidate : Type w} [Fintype Transcript]
    (choices : Transcript → Finset Candidate) (M : ℕ)
    (hlocal : ∀ τ, (choices τ).card ≤ M) :
    (reachableEnvelope choices).card ≤ Fintype.card Transcript * M := by
  classical
  simpa [reachableEnvelope] using
    (Finset.card_biUnion_le_card_mul (Finset.univ : Finset Transcript) choices M
      (fun τ _ => hlocal τ))

/-- If the transcript alphabet has a `bits`-bit disclosure budget and each transcript enables at
most `M` candidates, then `(reachableEnvelope choices).card ≤ 2^bits * M` (dwork2015adaptive; blum2015ladder). -/
theorem reachableEnvelope_card_le_of_disclosureBudget
    {Transcript : Type v} {Candidate : Type w} [Fintype Transcript]
    (choices : Transcript → Finset Candidate) (bits M : ℕ)
    (hbudget : HasDisclosureBudget Transcript bits)
    (hlocal : ∀ τ, (choices τ).card ≤ M) :
    (reachableEnvelope choices).card ≤ 2 ^ bits * M := by
  exact (reachableEnvelope_card_le choices M hlocal).trans
    (Nat.mul_le_mul_right M hbudget)

/-- If `UniformDev` holds at radius `Δ` on `reachableEnvelope choices`, then along the realized
candidate process at any `ω`, `cumCP Ehat (D.candidateProcess policy · ω) T ≤
cumCP E (D.candidateProcess policy · ω) T + 2Δ` for every horizon `T` (dwork2015adaptive; blum2015ladder). -/
theorem FilteredDisclosure.filteredPolicy_goodhart
    {Ω : Type u} {Transcript : Type v} {Candidate : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Transcript] [Fintype Transcript]
    (D : FilteredDisclosure Ω Transcript)
    (choices : Transcript → Finset Candidate)
    (policy : Transcript → AuditTrajectory Candidate)
    (hpolicy : ∀ τ n, policy τ n ∈ choices τ)
    (Ehat E : AuditPotential Candidate) (Δ : ℝ)
    (hUD : UniformDev ↑(reachableEnvelope choices) Ehat E Δ)
    (ω : Ω) (T : ℕ) :
    cumCP Ehat (fun n => D.candidateProcess policy n ω) T ≤
      cumCP E (fun n => D.candidateProcess policy n ω) T + 2 * Δ := by
  exact finite_audit_goodhart hUD
    (D.candidateProcess_admissible choices policy hpolicy ω) T

/-- If every audit-dependent trajectory `g t a` is admissible for the training-declared envelope
`F t`, the uniform-deviation failure event is measurable, and its kernel fiber has probability at
most `δ` for `μtrain`-almost every training state, then measured cumulative compression progress
exceeds population progress by more than `2Δ` with probability at most `δ` under
`μtrain.compProd κ`. -/
theorem kernel_adaptiveTrajectory_goodhart
    {Ωtrain Ωaudit Candidate : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (F : Ωtrain → AuditEnvelope Candidate)
    (g : Ωtrain → Ωaudit → AuditTrajectory Candidate)
    (Ehat : Ωtrain → Ωaudit → AuditPotential Candidate)
    (E : Ωtrain → AuditPotential Candidate)
    (Δ : ℝ) (δ : ENNReal)
    (hadm : ∀ t a, Admissible (g t a) (F t))
    (hBad : MeasurableSet
      {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ)
    (T : ℕ) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        cumCP (Ehat p.1 p.2) (g p.1 p.2) T >
          cumCP (E p.1) (g p.1 p.2) T + 2 * Δ} ≤ δ := by
  calc
    (μtrain.compProd κ)
        {p : Ωtrain × Ωaudit |
          cumCP (Ehat p.1 p.2) (g p.1 p.2) T >
            cumCP (E p.1) (g p.1 p.2) T + 2 * Δ}
        ≤ (μtrain.compProd κ)
            {p : Ωtrain × Ωaudit |
              ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ} := by
          apply measure_mono
          intro p hp
          simp only [Set.mem_setOf_eq] at hp ⊢
          intro hUD
          exact (not_lt_of_ge (finite_audit_goodhart hUD (hadm p.1 p.2) T)) hp
    _ ≤ δ := by
      have h := compProd_badEvent_le_mul μtrain κ
        {p : Ωtrain × Ωaudit |
          ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ}
        hBad δ hfiber
      simpa [IsProbabilityMeasure.measure_univ] using h

/-- If `policy` is measurable at each stage and reachable through `choices`, the induced candidate
process is adapted to `D.filtration`, and, provided the uniform-deviation failure event on
`reachableEnvelope choices` is measurable with kernel fiber at most `δ` for `μtrain`-almost every
training state, measured cumulative compression progress along the realized process exceeds
population progress by more than `2Δ` with probability at most `δ` under `μtrain.compProd κ`. -/
theorem FilteredDisclosure.adapted_and_kernel_goodhart
    {Ωtrain Ωaudit Transcript Candidate : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    [MeasurableSpace Transcript] [MeasurableSpace Candidate]
    [Fintype Transcript]
    (D : FilteredDisclosure (Ωtrain × Ωaudit) Transcript)
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (choices : Transcript → Finset Candidate)
    (policy : Transcript → AuditTrajectory Candidate)
    (hpolicyMeasurable : ∀ n, Measurable (fun τ => policy τ n))
    (hpolicyReachable : ∀ τ n, policy τ n ∈ choices τ)
    (Ehat : Ωtrain → Ωaudit → AuditPotential Candidate)
    (E : Ωtrain → AuditPotential Candidate)
    (Δ : ℝ) (δ : ENNReal)
    (hBad : MeasurableSet
      {p : Ωtrain × Ωaudit |
        ¬ UniformDev ↑(reachableEnvelope choices) (Ehat p.1 p.2) (E p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {a |
        ¬ UniformDev ↑(reachableEnvelope choices) (Ehat t a) (E t) Δ} ≤ δ)
    (T : ℕ) :
    Adapted D.filtration (D.candidateProcess policy) ∧
      (μtrain.compProd κ)
        {p : Ωtrain × Ωaudit |
          cumCP (Ehat p.1 p.2)
              (fun n => D.candidateProcess policy n p) T >
            cumCP (E p.1)
              (fun n => D.candidateProcess policy n p) T + 2 * Δ} ≤ δ := by
  constructor
  · exact D.candidateProcess_adapted policy hpolicyMeasurable
  · exact kernel_adaptiveTrajectory_goodhart μtrain κ
      (fun _t => ↑(reachableEnvelope choices))
      (fun t a n => D.candidateProcess policy n (t, a))
      Ehat E Δ δ
      (fun t a => D.candidateProcess_admissible choices policy hpolicyReachable (t, a))
      hBad hfiber T

/-- The disclosure `D` is audit-sealed through `T`: every transcript at stage `n ≤ T` is unchanged
by varying the audit coordinate. -/
def AuditSealedUntil
    {Ωtrain : Type u} {Ωaudit : Type v} {Transcript : Type w}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [MeasurableSpace Transcript]
    (D : FilteredDisclosure (Ωtrain × Ωaudit) Transcript) (T : ℕ) : Prop :=
  ∀ n ≤ T, ∀ t a₁ a₂, D.transcript n (t, a₁) = D.transcript n (t, a₂)

/-- If `D` is audit-sealed through `T` and `n ≤ T`, then the candidate process at stage `n` agrees
on `(t, a₁)` and `(t, a₂)` for any audit outcomes `a₁, a₂`. -/
theorem FilteredDisclosure.candidateProcess_eq_of_auditSealedUntil
    {Ωtrain : Type u} {Ωaudit : Type v} {Transcript : Type w} {Candidate : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [MeasurableSpace Transcript]
    (D : FilteredDisclosure (Ωtrain × Ωaudit) Transcript)
    (policy : Transcript → AuditTrajectory Candidate) {T n : ℕ}
    (hsealed : AuditSealedUntil D T) (hn : n ≤ T)
    (t : Ωtrain) (a₁ a₂ : Ωaudit) :
    D.candidateProcess policy n (t, a₁) =
      D.candidateProcess policy n (t, a₂) := by
  exact congrArg (fun τ => policy τ n) (hsealed n hn t a₁ a₂)

/-- The disclosure on `Unit × Bool` whose transcript is the audit coordinate itself under the
constant full-information filtration. -/
def boolAuditDisclosure : FilteredDisclosure (Unit × Bool) Bool where
  filtration := Filtration.const ℕ inferInstance le_rfl
  transcript := fun _ p => p.2
  adapted := fun _ => measurable_snd

/-- The identity transcript policy on `boolAuditDisclosure` selects distinct candidates at the two
audit outcomes at stage `0`, and `boolAuditDisclosure` is not audit-sealed through `0`. -/
theorem boolAuditDisclosure_is_auditDependent :
    boolAuditDisclosure.candidateProcess (fun τ _ => τ) 0 ((), false) ≠
        boolAuditDisclosure.candidateProcess (fun τ _ => τ) 0 ((), true) ∧
      ¬ AuditSealedUntil boolAuditDisclosure 0 := by
  constructor
  · exact Bool.false_ne_true
  · intro hsealed
    exact Bool.false_ne_true (hsealed 0 le_rfl () false true)

end AuditCP
