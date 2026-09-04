import AuditCP.Paper

/-!
# AuditCP — current-paper root

This root deliberately exposes only the finite sealed-audit development used by the current
Audit-CP paper.  The random-set, cybernetic-quotient, amalgamation, and model-theoretic
rederivation has the separate root `AuditCPNext`.

Dependency direction is one way: `AuditCPNext` may import this root; this root must never import
`AuditCP.Next` or any of its modules.
-/
