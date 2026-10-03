import AuditCP.Base
import AuditCP.Basic
import AuditCP.Telescope
import AuditCP.CyberneticCocycle
import AuditCP.FiniteAudit
import AuditCP.FiniteExperts
import AuditCP.StructuralAudit
import AuditCP.ConditionalAudit
import AuditCP.FilteredAudit
import AuditCP.FiniteBlackwell
import AuditCP.FiniteBlackwellDecision
import AuditCP.LawBridge
import AuditCP.FiniteBlackwellBrier
import AuditCP.EntropyFloor
import AuditCP.PaperMetrology
import AuditCPRL.L0
import AuditCPRL.Shaping
import AuditCPRL.Convergence
import AuditCPRL.ReachableEnvelope
import AuditCPRL.BellmanLadder
import AuditCPRL.ReusedPanel
import AuditCPRL.SelfModification
import AuditCPRL.Concealment
import AuditCPRL.Occupancy
import AuditCPRL.IntrinsicBudget
import AuditCPRL.Disclosure
import AuditCPRL.VersionedTarget
import AuditCPRL.Milestone

/-!
# Audit-CP — the thesis

This root is the thesis, in order.  The import list above is the argument.  Chapters 0 to 12 form
one chain in which each module imports its predecessor (chapter 2½ branches from chapter 2), and
chapters 13 to 25 import the chapters they use together with `RLTheory`.

## The claim

A signed audit ledger is a conservative field, and that is enough to price it.  Because cumulative
compression progress is an exact difference of a potential rather than a rectified sum, a closed
trajectory nets exactly zero at every horizon, the audited quantity reads exactly two stages
however long the run, and a single uniform-deviation event over a predeclared class controls every
horizon with no union bound over time.  What the audit then costs is the log-cardinality of that
predeclared class and nothing else — not the horizon, not the number of reuses, not the adaptivity
of the selection, and no parameter count.  What the audit cannot do is survive a change of the
interface it reads through: sealing is an exact property of a channel, coarse-graining that
contracts every individual divergence can still reverse the sign of their difference, and the
population potential itself moves when the presentation moves.

Compression and non-compression together are the thesis.

## The base

`AuditCP.Base` declares the seven types the whole argument is built from and proves nothing.
Four are independent, distinguished by their value carrier: B1 `AuditIndex` (a bare sort),
B2 `AuditPotential` (`ℝ`), B5 `AuditExperiment` (Mathlib `PMF`), B7 `AuditSampleLaw` (Mathlib
`Measure`).  Three are refinements consumed by more than one chapter: B3 `AuditTrajectory`,
B4 `AuditEnvelope`, B6 `AuditChannel`.  No module redefines any of them, and every declaration in
the closure is a refinement of one.

## The chapters

| chapter | module | what it adds |
| --- | --- | --- |
| 0 | `Vendored.FinitePMF`, `Base` | the base types; nothing is proved |
| 1 | `Basic` | the audited objects: the ledger, the deviation ball, admissibility |
| 2 | `Telescope` | the ledger is exact; a closed path nets zero |
| 2½ | `CyberneticCocycle` | an independently given change law composes exactly iff it is a potential difference; clipping breaks closed-loop cancellation |
| 3 | `FiniteAudit` | the slack: `2Δ`, uniformly in the horizon and the policy |
| 4 | `FiniteExperts` | the slack gets a number, and B7 enters |
| 5 | `StructuralAudit` | the envelope may be random and the audit may not see it |
| 6 | `ConditionalAudit` | the audit law may depend on the world, arbitrarily |
| 7 | `FilteredAudit` | the learner adapts, the interface discloses, and the bits are priced |
| 8 | `FiniteBlackwell` | sealing is a property of the interface; B5 and B6 enter |
| 9 | `FiniteBlackwellDecision` | what sealing means to a decision maker, and where the order fails |
| 9½ | `LawBridge` | one law carrier: `FinitePMF` and `PMF` are images of each other; total variation and pushforward commute with the bridge |
| 10 | `FiniteBlackwellBrier` | one full-support prior recovers row equality |
| 11 | `EntropyFloor` | what the ledger cannot buy: the world's own entropy |
| 12 | `PaperMetrology` | reading the instrument |

## The crossovers
Chapters 13 to 25 are the argument carried into reinforcement learning.  They import `RLTheory`,
a published library that was not written for this work and is used unchanged, on one side, and the
chapters above on the other; that is what makes each of them a claim about RL rather than a
relabeling.  Every theorem was built to the bone — no unused binder, every cited declaration in the
statement or proof.
| chapter | module | what it adds |
| --- | --- | --- |
| 13 | `AuditCPRL.L0` | the Goodhart gap is exactly the centered endpoint increment |
| 14 | `AuditCPRL.Shaping` | potential-based shaping with an estimated potential: error `2Δ`, horizon-free |
| 15 | `AuditCPRL.Convergence` | a convergent stochastic-approximation run exhausts its ledger |
| 16 | `AuditCPRL.ReachableEnvelope` | the admissible class is the learner's reachable envelope; the missing uniform envelope named |
| 17 | `AuditCPRL.BellmanLadder` | a predeclared Q-function ladder on one panel: horizon-free finite-sample bound |
| 18 | `AuditCPRL.ReusedPanel` | policy improvement on a reused panel pays the class term once; one panel, every horizon |
| 19 | `AuditCPRL.SelfModification` | a learner closing its own dynamics on the audit is charged the pre-committed envelope only |
| 20 | `AuditCPRL.Concealment` | per-step marginal tests cannot establish concealment in a POMDP |
| 21 | `AuditCPRL.Occupancy` | state aggregation is a garbling and can reverse signed occupancy progress |
| 22 | `AuditCPRL.IntrinsicBudget` | an audited intrinsic reward is kernel-budgeted and cannot farm noise |
| 23 | `AuditCPRL.Disclosure` | disclosure and sample size exchange on the audit channel |
| 24 | `AuditCPRL.VersionedTarget` | pricing a bridge state across a target version |
| 25 | `AuditCPRL.Milestone` | the number of demonstrable milestones a world can pay for |
## Scope

Because chapters 13 to 25 import `RLTheory`, this root does not build as a standalone Mathlib-only
package; that is by design.  The vocabulary is deliberate
throughout: the audit yields a *slack* and a *lower bound on improvement*, never a certificate.
-/
