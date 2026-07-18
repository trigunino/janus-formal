# Program M — Plain-language guide

## The question

Program M asks whether familiar physical structures can be obtained from
weaker mathematics instead of being assumed at the start.

It does **not** begin by assuming a universe, four dimensions, a metric, two
sectors or a Janus throat. Its first pilot contains only objects and labelled
relations between them.

## The first construction

For one selected relation, MF-TOP-001 defines reachability:

```text
A reaches A
A -> B and B -> C imply A reaches C
```

Reachability is a preorder. Mathlib's upper-set construction then gives a
topology: a mathematical notion of open regions and neighbourhoods.

```text
objects and a selected relation
  -> reflexive-transitive reachability
  -> preorder
  -> Alexandrov upper-set topology
```

This construction is invariant under renaming the objects. It therefore uses
the relational pattern, not the chosen names.

## What has actually been proved

- **MF-TOP-001 (T):** every selected binary relation supports this explicit
  Alexandrov-topology construction.
- **MF-TOP-002 (T):** isomorphic relational systems produce homeomorphic
  reconstructed spaces.
- **MF-NOGO-001 (T):** different primitive relations can lose their difference
  during reconstruction and produce the same topology.
- **MF-NOGO-002 (T):** the same relation can produce different standard
  topologies when the upper/lower convention changes.

These are mathematical results, not evidence that physical spacetime is an
Alexandrov space.

## Why the negative results matter

MF-TOP-001 proves existence, not unique emergence. The no-go results show that
the topology neither remembers all primitive information nor follows uniquely
without a declared orientation convention. Any future claim of emergence must
therefore list its extra assumptions.

## Vocabulary

| Term | Meaning here |
| --- | --- |
| primitive object | an element with no assumed spatial or physical meaning |
| relation | a declared link between two primitive objects |
| reachability | zero or more consecutive relation steps |
| preorder | a reflexive and transitive relation |
| topology | a collection of subsets called open sets |
| Alexandrov topology | a topology also closed under arbitrary intersections |
| isomorphism | a reversible relabelling preserving all primitive relations |
| homeomorphism | a reversible map preserving the reconstructed topology |
| no-go | a proof that a stronger conclusion does not follow from current data |

## Current boundary

Nothing yet derives dimension, continuity, a metric, causal cones, fields,
bimetry, PT symmetry or a throat. The next decision is whether additional
axioms can select a topology without hiding spatial information in them.

## Where to verify details

- axioms and anti-smuggling rules:
  `formal/axioms/program_m_foundations.md`;
- Lean proofs:
  `JanusFormal/Foundations/ProgramMTop001.lean` and
  `JanusFormal/Foundations/ProgramMTopNoGo.lean`;
- claim-by-claim provenance:
  `docs/program_m_provenance_register.md`.

