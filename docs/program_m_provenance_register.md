# Program M — Provenance register

This ledger prevents an output structure from being hidden in its assumptions.
One row is required for every Program M reconstruction claim.

| ID | Output | Primitive branch | Axioms used | Status | Necessity | Uniqueness | Countermodel | Janus-specific input | Evidence |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `MF-TOP-001` | Alexandrov upper-set topology | `MF-A0` | selected label; reflexive-transitive closure; upper-set convention | proved | conditional | not claimed | required | none | T |
| `MF-TOP-002` | homeomorphism under foundational relabelling | `MF-A0` | foundational isomorphism; same construction convention | proved | necessary under inputs | up to supplied isomorphism | required | none | T |
| `MF-NOGO-001` | topology does not recover all relations | `MF-A0` | two Bool systems; upper-set reconstruction | proved | impossible in general | n/a | empty-edge/self-loop witness | none | T |
| `MF-NOGO-002` | topology construction is not automatically unique | `MF-A0` | directed Bool system; upper/lower conventions | proved | impossible without convention | refuted | upper/lower witness | none | T |

Allowed values for `Necessity` are `necessary`, `conditional`, `possible`,
`impossible` and `unknown`. A row cannot be promoted beyond `O` without a
linked Lean theorem, executable audit, explicit interface or no-go witness.
