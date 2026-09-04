import AuditCP.Base

/-!
# Chapter 1 — the audited objects

Every declaration here is a refinement of a base type of `AuditCP.Base`; none of them redefines
one (schmidhuber1991; schmidhuber2010).  The concrete audit loss (`auditCE`) refines B2 `AuditPotential`; the signed ledger `cumCP`
reads a B2 potential along a B3 `AuditTrajectory`; the two hypotheses of the whole argument
(`UniformDev`, `Admissible`) are predicates on a B4 `AuditEnvelope`.

The audit potential is kept abstract.  `cumCP`, `UniformDev` and `Admissible` mention no loss, no
label, no probability and no cardinality: they are stated at B1/B2/B3/B4 and nothing else, which is
why the same statements carry the finite-sample, conditional, adaptive and interface chapters
without restatement.
-/

namespace AuditCP

/-- A predictor mapping each input `X` to a predictive finite probability mass function over
labels `Y`. -/
abbrev Predictor (X Y : Type*) [Fintype Y] := X → FinitePMF Y

/-- The `ε`-floored cross-entropy audit loss of the predictive pmf `p` at label `y`,
`-log (max ε (p.prob y))` (dawid1984prequential). -/
noncomputable def auditCE {Y : Type*} [Fintype Y] (ε : ℝ) (p : FinitePMF Y) (y : Y) : ℝ :=
  -Real.log (max ε (p.prob y))

/-- Every point probability of a finite probability mass function is at most `1`. -/
theorem finitePMF_prob_le_one {Y : Type*} [Fintype Y] (p : FinitePMF Y) (y : Y) :
    p.prob y ≤ 1 := by
  classical
  calc
    p.prob y ≤ ∑ z : Y, p.prob z :=
      Finset.single_le_sum (fun z _ => p.prob_nonneg z) (Finset.mem_univ y)
    _ = 1 := p.prob_sum_one

/-- For `0 < ε ≤ 1`, the audit loss `auditCE ε p y` lies in the interval `[0, -log ε]`. -/
theorem auditCE_mem_Icc {Y : Type*} [Fintype Y] (ε : ℝ) (p : FinitePMF Y) (y : Y)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    auditCE ε p y ∈ Set.Icc 0 (-Real.log ε) := by
  have hp1 : p.prob y ≤ 1 := finitePMF_prob_le_one p y
  have hmax0 : 0 ≤ max ε (p.prob y) := le_trans hε0.le (le_max_left _ _)
  have hmax1 : max ε (p.prob y) ≤ 1 := max_le hε1 hp1
  have hlog_nonpos : Real.log (max ε (p.prob y)) ≤ 0 := Real.log_nonpos hmax0 hmax1
  have hmax_pos : 0 < max ε (p.prob y) := lt_of_lt_of_le hε0 (le_max_left _ _)
  have hlog_mono : Real.log ε ≤ Real.log (max ε (p.prob y)) :=
    Real.strictMonoOn_log.monotoneOn hε0 hmax_pos (le_max_left _ _)
  simp only [auditCE, Set.mem_Icc]
  constructor <;> linarith

/-- Cumulative signed compression progress of a potential `E` read along a trajectory `g` over
`T` stages, ∑_{t < T} (E(g t) − E(g(t+1))) (schmidhuber1991; schmidhuber2010). -/
noncomputable def cumCP {ι : Type*} (E : AuditPotential ι) (g : AuditTrajectory ι) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (E (g t) - E (g (t + 1)))

/-- The potentials `Ehat` and `E` agree to within `Δ` at every point of the envelope `F`. -/
def UniformDev {ι : Type*} (F : AuditEnvelope ι) (Ehat E : AuditPotential ι) (Δ : ℝ) : Prop :=
  ∀ θ ∈ F, |Ehat θ - E θ| ≤ Δ

/-- Every stage of the trajectory `g` lies in the envelope `F`. -/
def Admissible {ι : Type*} (g : AuditTrajectory ι) (F : AuditEnvelope ι) : Prop :=
  ∀ t, g t ∈ F

end AuditCP
