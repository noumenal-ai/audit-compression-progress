import AuditCP.FilteredAudit
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Chapter 8 — sealing is a property of the interface

This chapter introduces the second irreducible base type, B5 `AuditExperiment`, and its split
refinement B6 `AuditChannel`.  Everything here is stated at B5/B6 and nothing else: no learner, no
loss, no panel, no horizon.  That is the content — "the learner did not look at the audit" becomes
a predicate on a channel, with three provably equivalent readings (factorization through the
permitted public coordinate, being the Blackwell bottom relative to public information, and zero
equal-prior binary decision advantage, the last in Chapter 9).

The protected parameter is the audit state `A`, the second coordinate of the B6 split.  It is
*not* an MDP action: `AuditSealed` protects that coordinate, it does not condition on it.  The
learner's complete observation is sealed exactly when it is Blackwell-equivalent to observing the
permitted public state and nothing more about `A`.

Two boundaries are kept visible rather than smoothed over.  Sealing is downward-closed under
garbling, while signed progress is not (Chapter 9), so the Blackwell order is a good regulator for
the protected coordinate and a bad one for the report.  And sealing is an exact row equality: every
characterization below is destroyed by an arbitrarily small perturbation, and no approximate
version of any of them exists in this closure.

The comparison below is constructed directly with Mathlib's `PMF.bind`, `PMF.map`, and `PMF.pure`
(`Mathlib/Probability/ProbabilityMassFunction/Monad.lean` and `Constructions.lean`), which is what
makes B5 a base type rather than a refinement of B2: `PMF X` is a map into `ℝ≥0∞` with a
summability field, and no declaration in the closure carries it to or from a real reading.  No
converse form of the Blackwell--Sherman--Stein theorem is invoked.  The conceptual source is Blackwell,
"Equivalent Comparisons of Experiments", *Annals of Mathematical Statistics* 24(2), 1953,
265--272, DOI 10.1214/aoms/1177729032.

The final sections keep two further boundaries explicit:

* a terminal experiment for one policy is weaker than policy-uniform interactive sealing; and
* sealing factors the candidate/audit law but does not prove the uniform-deviation event required
  by the existing conditional `2 * Δ` AuditCP theorem.

-/

open MeasureTheory ProbabilityTheory

namespace AuditCP

universe uΘ uX₀ uX₁ uX₂ uS uA uY uZ uH uU uO uG

/-! ## Experiment comparison -/

/-- `E₀` is Blackwell-below `E₁` when some garbling `G` of `E₁`'s output reproduces `E₀`:
`∃ G, ∀ θ, E₀ θ = (E₁ θ).bind G` (blackwell1953). -/
def BlackwellBelow {Θ : Type uΘ} {X₀ : Type uX₀} {X₁ : Type uX₁}
    (E₀ : AuditExperiment Θ X₀) (E₁ : AuditExperiment Θ X₁) : Prop :=
  ∃ G : AuditExperiment X₁ X₀, ∀ θ, E₀ θ = (E₁ θ).bind G

/-- `E₀` and `E₁` are Blackwell-equivalent when each is Blackwell-below the other (blackwell1953). -/
def BlackwellEquivalent {Θ : Type uΘ} {X₀ : Type uX₀} {X₁ : Type uX₁}
    (E₀ : AuditExperiment Θ X₀) (E₁ : AuditExperiment Θ X₁) : Prop :=
  BlackwellBelow E₀ E₁ ∧ BlackwellBelow E₁ E₀

/-- `BlackwellBelow E E` holds via the Dirac identity garbling `PMF.pure`. -/
theorem blackwellBelow_refl {Θ : Type uΘ} {X : Type uX₀} (E : AuditExperiment Θ X) :
    BlackwellBelow E E := by
  refine ⟨PMF.pure, ?_⟩
  intro θ
  exact (PMF.bind_pure (E θ)).symm

/-- If `BlackwellBelow E₀ E₁` and `BlackwellBelow E₁ E₂`, then `BlackwellBelow E₀ E₂`. -/
theorem blackwellBelow_trans
    {Θ : Type uΘ} {X₀ : Type uX₀} {X₁ : Type uX₁} {X₂ : Type uX₂}
    {E₀ : AuditExperiment Θ X₀} {E₁ : AuditExperiment Θ X₁} {E₂ : AuditExperiment Θ X₂}
    (h₀₁ : BlackwellBelow E₀ E₁) (h₁₂ : BlackwellBelow E₁ E₂) :
    BlackwellBelow E₀ E₂ := by
  obtain ⟨G₀₁, hG₀₁⟩ := h₀₁
  obtain ⟨G₁₂, hG₁₂⟩ := h₁₂
  refine ⟨fun x₂ => (G₁₂ x₂).bind G₀₁, ?_⟩
  intro θ
  rw [hG₀₁ θ, hG₁₂ θ, PMF.bind_bind]

/-- If `BlackwellBelow E₀ E₁`, then every decision rule `rule₀` on `E₀` is matched by a rule
`rule₁` on `E₁` inducing the same action law at every parameter:
`∃ rule₁, ∀ θ, (E₁ θ).bind rule₁ = (E₀ θ).bind rule₀`. -/
theorem BlackwellBelow.simulate_decision
    {Θ : Type uΘ} {X₀ : Type uX₀} {X₁ : Type uX₁} {Decision : Type uX₂}
    {E₀ : AuditExperiment Θ X₀} {E₁ : AuditExperiment Θ X₁}
    (h : BlackwellBelow E₀ E₁) (rule₀ : AuditExperiment X₀ Decision) :
    ∃ rule₁ : AuditExperiment X₁ Decision,
      ∀ θ, (E₁ θ).bind rule₁ = (E₀ θ).bind rule₀ := by
  obtain ⟨G, hG⟩ := h
  refine ⟨fun x₁ => (G x₁).bind rule₀, ?_⟩
  intro θ
  rw [← PMF.bind_bind, ← hG θ]

/-! ## Audit sealing and the public-only experiment -/

/-- The channel `K` is audit-sealed: its output law at fixed public state `s` does not depend on
the audit state `a`. -/
def AuditSealed {S : Type uS} {A : Type uA} {Y : Type uY}
    (K : AuditChannel S A Y) : Prop :=
  ∀ s a a', K (s, a) = K (s, a')

/-- The channel `K` factors through the public coordinate: `∃ H, ∀ s a, K (s, a) = H s`. -/
def FactorsThroughPublic {S : Type uS} {A : Type uA} {Y : Type uY}
    (K : AuditChannel S A Y) : Prop :=
  ∃ H : AuditExperiment S Y, ∀ s a, K (s, a) = H s

/-- F1 — given `A` nonempty, `AuditSealed K ↔ FactorsThroughPublic K`. -/
theorem auditSealed_iff_factorsThroughPublic
    {S : Type uS} {A : Type uA} {Y : Type uY} [Nonempty A]
    (K : AuditChannel S A Y) :
    AuditSealed K ↔ FactorsThroughPublic K := by
  constructor
  · intro hsealed
    let a₀ : A := Classical.choice inferInstance
    refine ⟨fun s => K (s, a₀), ?_⟩
    intro s a
    exact hsealed s a a₀
  · rintro ⟨H, hH⟩ s a a'
    exact (hH s a).trans (hH s a').symm

/-- The channel revealing exactly the public state `s` and nothing else,
`fun (s, a) => PMF.pure s`. -/
noncomputable def publicOnlyExperiment {S : Type uS} {A : Type uA} :
    AuditChannel S A S :=
  fun sa => PMF.pure sa.1

/-- The channel revealing the public state together with `K`'s output,
`fun sa => (K sa).map (fun y => (sa.1, y))`. -/
noncomputable def learnerExperiment
    {S : Type uS} {A : Type uA} {Y : Type uY}
    (K : AuditChannel S A Y) : AuditChannel S A (S × Y) :=
  fun sa => (K sa).map fun y => (sa.1, y)

/-- Pushing a PMF on `Y` through the tag `y ↦ (s, y)` is injective. -/
theorem pmf_map_publicTag_injective {S : Type uS} {Y : Type uY} (s : S) :
    Function.Injective (fun p : PMF Y => p.map fun y => (s, y)) := by
  intro p q hpq
  calc
    p = (p.map fun y => (s, y)).map Prod.snd := by
      rw [PMF.map_comp]
      change p = p.map (fun y : Y => y)
      rw [show (fun y : Y => y) = id from funext fun _ => rfl, PMF.map_id]
    _ = (q.map fun y => (s, y)).map Prod.snd :=
      congrArg (fun r : PMF (S × Y) => r.map Prod.snd) hpq
    _ = q := by
      rw [PMF.map_comp]
      change q.map (fun y : Y => y) = q
      rw [show (fun y : Y => y) = id from funext fun _ => rfl, PMF.map_id]

/-- F2a — public information is Blackwell-below the complete learner view:
`BlackwellBelow publicOnlyExperiment (learnerExperiment K)`. -/
theorem publicOnly_blackwellBelow_learner
    {S : Type uS} {A : Type uA} {Y : Type uY}
    (K : AuditChannel S A Y) :
    BlackwellBelow (publicOnlyExperiment (S := S) (A := A)) (learnerExperiment K) := by
  refine ⟨fun sy => PMF.pure sy.1, ?_⟩
  rintro ⟨s, a⟩
  simp [publicOnlyExperiment, learnerExperiment, PMF.map, Function.comp_def]

/-- F2b — given `A` nonempty,
`BlackwellBelow (learnerExperiment K) publicOnlyExperiment ↔ AuditSealed K` (blackwell1953). -/
theorem learner_blackwellBelow_publicOnly_iff_auditSealed
    {S : Type uS} {A : Type uA} {Y : Type uY} [Nonempty A]
    (K : AuditChannel S A Y) :
    BlackwellBelow (learnerExperiment K) (publicOnlyExperiment (S := S) (A := A)) ↔
      AuditSealed K := by
  constructor
  · rintro ⟨G, hG⟩ s a a'
    apply pmf_map_publicTag_injective s
    change learnerExperiment K (s, a) = learnerExperiment K (s, a')
    calc
      learnerExperiment K (s, a) =
          (publicOnlyExperiment (S := S) (A := A) (s, a)).bind G := hG (s, a)
      _ = G s := by simp [publicOnlyExperiment]
      _ = (publicOnlyExperiment (S := S) (A := A) (s, a')).bind G := by
        simp [publicOnlyExperiment]
      _ = learnerExperiment K (s, a') := (hG (s, a')).symm
  · intro hsealed
    obtain ⟨H, hH⟩ := (auditSealed_iff_factorsThroughPublic K).1 hsealed
    refine ⟨fun s => (H s).map fun y => (s, y), ?_⟩
    rintro ⟨s, a⟩
    simp [learnerExperiment, publicOnlyExperiment, hH]

/-- F2 — given `A` nonempty,
`BlackwellEquivalent (learnerExperiment K) publicOnlyExperiment ↔ AuditSealed K` (blackwell1953). -/
theorem blackwellEquivalent_publicOnly_iff_auditSealed
    {S : Type uS} {A : Type uA} {Y : Type uY} [Nonempty A]
    (K : AuditChannel S A Y) :
    BlackwellEquivalent (learnerExperiment K)
        (publicOnlyExperiment (S := S) (A := A)) ↔ AuditSealed K := by
  constructor
  · exact fun h => (learner_blackwellBelow_publicOnly_iff_auditSealed K).1 h.1
  · intro hsealed
    exact ⟨(learner_blackwellBelow_publicOnly_iff_auditSealed K).2 hsealed,
      publicOnly_blackwellBelow_learner K⟩

/-! ## Deterministic and downstream consequences -/

/-- The channel obtained by postprocessing `K`'s output with the audit-blind kernel `R`,
`fun sa => (K sa).bind (R sa.1)`. -/
noncomputable def auditBlindPostprocess
    {S : Type uS} {A : Type uA} {Y : Type uY} {Z : Type uZ}
    (K : AuditChannel S A Y) (R : S → AuditExperiment Y Z) : AuditChannel S A Z :=
  fun sa => (K sa).bind (R sa.1)

/-- F9 — if `K` is audit-sealed, then `auditBlindPostprocess K R` is audit-sealed for every
audit-blind postprocessing `R`. -/
theorem AuditSealed.postprocess
    {S : Type uS} {A : Type uA} {Y : Type uY} {Z : Type uZ}
    {K : AuditChannel S A Y} (hK : AuditSealed K) (R : S → AuditExperiment Y Z) :
    AuditSealed (auditBlindPostprocess K R) := by
  intro s a a'
  simp only [auditBlindPostprocess]
  rw [hK s a a']

/-- `PMF.pure` is injective on `Y`. -/
theorem pmf_pure_injective {Y : Type uY} : Function.Injective (@PMF.pure Y) := by
  intro y y' h
  by_contra hne
  have hmass := congrArg (fun p : PMF Y => p y) h
  rw [PMF.pure_apply_self, PMF.pure_apply_of_ne _ _ hne] at hmass
  exact one_ne_zero hmass

/-- The deterministic channel represented as a Dirac law at `f`, `fun sa => PMF.pure (f sa)`. -/
noncomputable def deterministicAuditChannel
    {S : Type uS} {A : Type uA} {Y : Type uY}
    (f : S × A → Y) : AuditChannel S A Y :=
  fun sa => PMF.pure (f sa)

/-- F5 — `AuditSealed (deterministicAuditChannel f) ↔ ∀ s a a', f (s, a) = f (s, a')`. -/
theorem deterministicAuditChannel_sealed_iff
    {S : Type uS} {A : Type uA} {Y : Type uY} (f : S × A → Y) :
    AuditSealed (deterministicAuditChannel f) ↔
      ∀ s a a', f (s, a) = f (s, a') := by
  constructor
  · intro h s a a'
    exact pmf_pure_injective (h s a a')
  · intro h s a a'
    exact congrArg PMF.pure (h s a a')

/-- `AuditSealedUntil D T ↔ ∀ n ≤ T, AuditSealed (deterministicAuditChannel (D.transcript n))`. -/
theorem auditSealedUntil_iff_stagewise_dirac_sealed
    {Ωtrain : Type uS} {Ωaudit : Type uA} {Transcript : Type uY}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit] [MeasurableSpace Transcript]
    (D : FilteredDisclosure (Ωtrain × Ωaudit) Transcript) (T : ℕ) :
    AuditSealedUntil D T ↔
      ∀ n ≤ T, AuditSealed (deterministicAuditChannel (D.transcript n)) := by
  constructor
  · intro hsealed n hn
    exact (deterministicAuditChannel_sealed_iff (D.transcript n)).2
      (hsealed n hn)
  · intro hsealed n hn
    exact (deterministicAuditChannel_sealed_iff (D.transcript n)).1
      (hsealed n hn)

/-- If `K` is audit-sealed, then its second-coordinate projection `fun sa => (K sa).map Prod.snd`
is audit-sealed. -/
theorem AuditSealed.snd_projection
    {S : Type uS} {A : Type uA} {Y : Type uY} {Z : Type uZ}
    {K : AuditChannel S A (Y × Z)} (hK : AuditSealed K) :
    AuditSealed (fun sa => (K sa).map Prod.snd) := by
  intro s a a'
  change (K (s, a)).map Prod.snd = (K (s, a')).map Prod.snd
  rw [hK s a a']

/-- If the second-coordinate projection of `K` is not audit-sealed, then `K` is not audit-sealed. -/
theorem combined_not_sealed_of_snd_not_sealed
    {S : Type uS} {A : Type uA} {Y : Type uY} {Z : Type uZ}
    {K : AuditChannel S A (Y × Z)}
    (hZ : ¬ AuditSealed (fun sa => (K sa).map Prod.snd)) :
    ¬ AuditSealed K := by
  exact fun hK => hZ hK.snd_projection

/-! ## Complete-transcript obstruction -/

/-- The uniform (fair) distribution on `Bool`. -/
noncomputable def fairBool : PMF Bool :=
  PMF.uniformOfFintype Bool

/-- Every outcome of `fairBool` has mass `1/2`. -/
theorem fairBool_apply (b : Bool) : fairBool b = 1 / 2 := by
  rw [fairBool, PMF.uniformOfFintype_apply]
  norm_num

/-- The channel releasing a fair bit `u` together with `u xor a` for audit state `a`,
`fun sa => fairBool.map (fun u => (u, u xor sa.2))`. -/
noncomputable def xorTranscriptChannel : AuditChannel Unit Bool (Bool × Bool) :=
  fun sa => fairBool.map fun u => (u, Bool.xor u sa.2)

/-- The decoder recovering the audit bit from a parity pair, `fun (y₁, y₂) => y₁ xor y₂`. -/
def xorTranscriptDecoder (y : Bool × Bool) : Bool :=
  Bool.xor y.1 y.2

/-- Decoding `xorTranscriptChannel`'s output recovers the audit bit exactly:
`(xorTranscriptChannel ((), a)).map xorTranscriptDecoder = PMF.pure a`. -/
theorem xorTranscript_decodes_audit (a : Bool) :
    (xorTranscriptChannel ((), a)).map xorTranscriptDecoder = PMF.pure a := by
  rw [xorTranscriptChannel, PMF.map_comp]
  have hfun :
      xorTranscriptDecoder ∘ (fun u => (u, Bool.xor u a)) = Function.const Bool a := by
    funext u
    cases u <;> cases a <;> rfl
  rw [hfun, PMF.map_const]

/-- F6a — both marginals of `xorTranscriptChannel`, `fun sa => (xorTranscriptChannel sa).map
Prod.fst` and `Prod.snd`, are audit-sealed. -/
theorem xorTranscript_marginals_sealed :
    AuditSealed (fun sa => (xorTranscriptChannel sa).map Prod.fst) ∧
      AuditSealed (fun sa => (xorTranscriptChannel sa).map Prod.snd) := by
  constructor
  · intro s a a'
    cases s
    simp only [xorTranscriptChannel, PMF.map_comp]
    have hfun :
        Prod.fst ∘ (fun u => (u, Bool.xor u a)) = (id : Bool → Bool) := by
      funext u
      rfl
    have hfun' :
        Prod.fst ∘ (fun u => (u, Bool.xor u a')) = (id : Bool → Bool) := by
      funext u
      rfl
    rw [hfun, hfun', PMF.map_id]
  · intro s a a'
    cases s
    simp only [xorTranscriptChannel, PMF.map_comp]
    apply PMF.ext
    intro b
    cases a <;> cases a' <;> cases b <;>
      simp [Function.comp_def, PMF.map_apply, fairBool_apply]

/-- F6b — `xorTranscriptChannel` is not audit-sealed. -/
theorem xorTranscript_not_sealed : ¬ AuditSealed xorTranscriptChannel := by
  intro hsealed
  have hrows := hsealed () false true
  have hdecoded := congrArg (fun p : PMF (Bool × Bool) => p.map xorTranscriptDecoder) hrows
  rw [xorTranscript_decodes_audit false, xorTranscript_decodes_audit true] at hdecoded
  exact Bool.false_ne_true (pmf_pure_injective hdecoded)

/-! ## Policy-uniform interactive sealing -/

/-- One controlled interaction step: draw an action `u` from `policy` at the public state and
history, draw a response `o` from `response`, and record `update h u o`. -/
noncomputable def controlledInteractionStep
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    (policy : S → H → PMF U)
    (response : S × A → H → U → PMF O)
    (update : H → U → O → H) : S × A → H → PMF H :=
  fun sa h => (policy sa.1 h).bind fun u =>
    (response sa h u).map fun o => update h u o

/-- The response kernel `response` is locally audit-sealed: its output at fixed public state,
history, and action does not depend on the audit state. -/
def LocallyAuditSealedResponse
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    (response : S × A → H → U → PMF O) : Prop :=
  ∀ s a a' h u, response (s, a) h u = response (s, a') h u

/-- If `response` is locally audit-sealed, then `controlledInteractionStep policy response update`
at fixed public state and history does not depend on the audit state. -/
theorem controlledInteractionStep_eq_of_localSeal
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    (policy : S → H → PMF U)
    (response : S × A → H → U → PMF O)
    (update : H → U → O → H)
    (hresponse : LocallyAuditSealedResponse response)
    (s : S) (a a' : A) (h : H) :
    controlledInteractionStep policy response update (s, a) h =
      controlledInteractionStep policy response update (s, a') h := by
  simp only [controlledInteractionStep]
  apply congrArg (PMF.bind (policy s h))
  funext u
  rw [hresponse s a a' h u]

/-- The `n`-round history law obtained by iterating `step` from `initial`, by recursion on `n`. -/
noncomputable def iterateInteraction
    {S : Type uS} {A : Type uA} {H : Type uH}
    (initial : AuditExperiment S H) (step : S × A → H → PMF H) :
    ℕ → AuditChannel S A H
  | 0, sa => initial sa.1
  | n + 1, sa => (iterateInteraction initial step n sa).bind (step sa)

/-- If `step` is audit-independent at every history, then `iterateInteraction initial step n` is
audit-sealed at every round `n`. -/
theorem iterateInteraction_sealed
    {S : Type uS} {A : Type uA} {H : Type uH}
    (initial : AuditExperiment S H) (step : S × A → H → PMF H)
    (hstep : ∀ s a a' h, step (s, a) h = step (s, a') h) (n : ℕ) :
    AuditSealed (iterateInteraction initial step n) := by
  induction n with
  | zero =>
      intro s a a'
      rfl
  | succ n ih =>
      intro s a a'
      simp only [iterateInteraction]
      rw [ih s a a']
      apply congrArg (PMF.bind (iterateInteraction initial step n (s, a')))
      funext h
      exact hstep s a a' h

/-- F8 — if `response` is locally audit-sealed, then the `n`-round interaction history law
`iterateInteraction initial (controlledInteractionStep policy response update) n` is audit-sealed
for every audit-blind `policy`. -/
theorem policyUniform_interactive_sealing
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    (initial : AuditExperiment S H)
    (policy : S → H → PMF U)
    (response : S × A → H → U → PMF O)
    (update : H → U → O → H)
    (hresponse : LocallyAuditSealedResponse response) (n : ℕ) :
    AuditSealed
      (iterateInteraction initial (controlledInteractionStep policy response update) n) := by
  apply iterateInteraction_sealed
  intro s a a' h
  exact controlledInteractionStep_eq_of_localSeal policy response update hresponse s a a' h

/-- The channel exposing `response`'s output with public state, history, and action folded into
one public coordinate, `fun ((s, h), u), a => response (s, a) h u`. -/
def testedResponseChannel
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    (response : S × A → H → U → PMF O) : AuditChannel ((S × H) × U) A O :=
  fun p => response (p.1.1.1, p.2) p.1.1.2 p.1.2

/-- `LocallyAuditSealedResponse response ↔ AuditSealed (testedResponseChannel response)`. -/
theorem locallyAuditSealedResponse_iff_testedChannel_sealed
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    (response : S × A → H → U → PMF O) :
    LocallyAuditSealedResponse response ↔ AuditSealed (testedResponseChannel response) := by
  constructor
  · intro hresponse shU a a'
    exact hresponse shU.1.1 a a' shU.1.2 shU.2
  · intro hsealed s a a' h u
    exact hsealed ((s, h), u) a a'

/-- F8 converse — given `A` nonempty, `BlackwellEquivalent (learnerExperiment
(testedResponseChannel response)) publicOnlyExperiment ↔ LocallyAuditSealedResponse response`. -/
theorem blackwellEquivalent_testedResponse_iff_localSeal
    {S : Type uS} {A : Type uA} {H : Type uH} {U : Type uU} {O : Type uO}
    [Nonempty A] (response : S × A → H → U → PMF O) :
    BlackwellEquivalent (learnerExperiment (testedResponseChannel response))
        (publicOnlyExperiment (S := (S × H) × U) (A := A)) ↔
      LocallyAuditSealedResponse response := by
  rw [blackwellEquivalent_publicOnly_iff_auditSealed]
  exact (locallyAuditSealedResponse_iff_testedChannel_sealed response).symm

/-! ## Candidate-channel absorption -/

/-- The joint law sampling public state, then audit state from `κ`, then candidate from `C`:
`μ.bind (fun s => (κ s).bind (fun a => (C (s, a)).bind (fun g => PMF.pure ((s, g), a))))`. -/
noncomputable def auditThenCandidateLaw
    {S : Type uS} {A : Type uA} {G : Type uG}
    (μ : PMF S) (κ : AuditExperiment S A) (C : AuditChannel S A G) : PMF ((S × G) × A) :=
  μ.bind fun s => (κ s).bind fun a => (C (s, a)).bind fun g => PMF.pure ((s, g), a)

/-- The joint law sampling public state, then candidate from `H`, then audit state from `κ`:
`μ.bind (fun s => (H s).bind (fun g => (κ s).bind (fun a => PMF.pure ((s, g), a))))`. -/
noncomputable def candidateThenAuditLaw
    {S : Type uS} {A : Type uA} {G : Type uG}
    (μ : PMF S) (κ : AuditExperiment S A) (H : AuditExperiment S G) : PMF ((S × G) × A) :=
  μ.bind fun s => (H s).bind fun g => (κ s).bind fun a => PMF.pure ((s, g), a)

/-- F10 — if `C` is audit-sealed, then `C` factors through some `H : AuditExperiment S G` with
`∀ s a, C (s, a) = H s`, and `auditThenCandidateLaw μ κ C = candidateThenAuditLaw μ κ H`. -/
theorem sealedCandidateChannel_absorption
    {S : Type uS} {A : Type uA} {G : Type uG} [Nonempty A]
    (μ : PMF S) (κ : AuditExperiment S A) (C : AuditChannel S A G)
    (hC : AuditSealed C) :
    ∃ H : AuditExperiment S G,
      (∀ s a, C (s, a) = H s) ∧
        auditThenCandidateLaw μ κ C = candidateThenAuditLaw μ κ H := by
  obtain ⟨H, hH⟩ := (auditSealed_iff_factorsThroughPublic C).1 hC
  refine ⟨H, hH, ?_⟩
  simp only [auditThenCandidateLaw, candidateThenAuditLaw]
  apply congrArg (PMF.bind μ)
  funext s
  simp_rw [hH]
  exact PMF.bind_comm (κ s) (H s) (fun a g => PMF.pure ((s, g), a))

/-! ## Endpoint-only specialization -/

/-- The trajectory taking value `endpoints.1` at stage `0` and `endpoints.2` at every later
stage. -/
def endpointPairPath {Candidate : Type*} (endpoints : Candidate × Candidate) :
    AuditTrajectory Candidate
  | 0 => endpoints.1
  | _ + 1 => endpoints.2

/-- `cumCP E (endpointPairPath endpoints) 1 = E endpoints.1 - E endpoints.2`. -/
theorem cumCP_endpointPairPath {Candidate : Type*} (E : AuditPotential Candidate)
    (endpoints : Candidate × Candidate) :
    cumCP E (endpointPairPath endpoints) 1 = E endpoints.1 - E endpoints.2 := by
  rw [cumCP_telescope]
  rfl

/-- F14 — if the endpoint-pair channel `C` is audit-sealed, then it factors through some `H` with
`auditThenCandidateLaw μ κ C = candidateThenAuditLaw μ κ H`, and every endpoint pair satisfies
`cumCP E (endpointPairPath endpoints) 1 = E endpoints.1 - E endpoints.2`. -/
theorem sealedEndpointPair_absorption
    {S : Type uS} {A : Type uA} {Candidate : Type uG} [Nonempty A]
    (μ : PMF S) (κ : AuditExperiment S A) (C : AuditChannel S A (Candidate × Candidate))
    (hC : AuditSealed C) (E : AuditPotential Candidate) :
    ∃ H : AuditExperiment S (Candidate × Candidate),
      (∀ s a, C (s, a) = H s) ∧
      auditThenCandidateLaw μ κ C = candidateThenAuditLaw μ κ H ∧
      ∀ endpoints, cumCP E (endpointPairPath endpoints) 1 =
        E endpoints.1 - E endpoints.2 := by
  obtain ⟨H, hH, hlaw⟩ := sealedCandidateChannel_absorption μ κ C hC
  exact ⟨H, hH, hlaw, cumCP_endpointPairPath E⟩

/-- F14 conditional-kernel endpoint specialization — if both reported endpoints lie in `F t` at
every training state, the uniform-deviation failure event is measurable, and its kernel fiber has
probability at most `δ` for `μtrain`-almost every training state, then the signed endpoint report
exceeds its population value by more than `2Δ` with probability at most `δ` under
`μtrain.compProd κ`. -/
theorem kernel_endpointPair_goodhart
    {Ωtrain Ωaudit Candidate : Type*}
    [MeasurableSpace Ωtrain] [MeasurableSpace Ωaudit]
    (μtrain : AuditSampleLaw Ωtrain) [IsProbabilityMeasure μtrain]
    (κ : Kernel Ωtrain Ωaudit) [IsMarkovKernel κ]
    (F : Ωtrain → AuditEnvelope Candidate) (endpoints : Ωtrain → Candidate × Candidate)
    (Ehat : Ωtrain → Ωaudit → AuditPotential Candidate) (E : Ωtrain → AuditPotential Candidate)
    (Δ : ℝ) (δ : ENNReal)
    (hendpoints : ∀ t, (endpoints t).1 ∈ F t ∧ (endpoints t).2 ∈ F t)
    (hBad : MeasurableSet
      {p : Ωtrain × Ωaudit | ¬ UniformDev (F p.1) (Ehat p.1 p.2) (E p.1) Δ})
    (hfiber : ∀ᵐ t ∂μtrain,
      κ t {a | ¬ UniformDev (F t) (Ehat t a) (E t) Δ} ≤ δ) :
    (μtrain.compProd κ)
      {p : Ωtrain × Ωaudit |
        Ehat p.1 p.2 (endpoints p.1).1 - Ehat p.1 p.2 (endpoints p.1).2 >
          E p.1 (endpoints p.1).1 - E p.1 (endpoints p.1).2 + 2 * Δ} ≤ δ := by
  have hadm : ∀ t, Admissible (endpointPairPath (endpoints t)) (F t) := by
    intro t n
    cases n with
    | zero => exact (hendpoints t).1
    | succ n => exact (hendpoints t).2
  have h := kernel_randomTrajectory_goodhart μtrain κ F
    (fun t => endpointPairPath (endpoints t)) Ehat E Δ δ hadm hBad hfiber 1
  simpa only [cumCP_endpointPairPath] using h

end AuditCP
