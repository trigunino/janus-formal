# MF-ENUM-001 — Finite relational census

## Purpose

This executable audit explores all directed binary relations on one to four
objects without imposing symmetry. Relations differing only by a permutation
of object names are counted once.

## Conventions

- directed edges and self-loops are allowed;
- equivalence is simultaneous relabelling of rows and columns;
- reachability is reflexive-transitive closure;
- strongly connected components are mutual-reachability classes;
- upper and lower open sets are computed separately.

No graph is interpreted as spacetime or causality.

## Exhaustive results

| Objects | Labelled relations | Classes up to renaming | Reachability classes | Orientation-independent classes |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 2 | 1 | 2 |
| 2 | 16 | 10 | 3 | 6 |
| 3 | 512 | 104 | 9 | 40 |
| 4 | 65,536 | 3,044 | 33 | 1,248 |

`Orientation-independent classes` counts primitive relation classes whose
generated upper and lower topologies agree. Self-loop choices can distinguish
primitive classes while disappearing under reflexive closure, so this column
must not be compared directly with the number of reachability classes.

## Main conclusion

The map from primitive relations to reachability is highly many-to-one. At four
objects, 3,044 relational classes collapse to 33 reachability classes. A
topology reconstructed only from reachability cannot recover most primitive
edge information.

This is an executable finite result, not a theorem about arbitrary cardinality
or a physical selection principle.

## Reproduction

```text
python scripts/enumerate_program_m_relations.py --max-objects 4
```

Machine-readable output is stored in
`outputs/program_m/mf_enum_001.json`. Tests verify the known class counts,
canonical-label invariance, a three-cycle SCC, the audited size bound, and the
positive/negative Minkowski 1+1 order witnesses described in
[`program_m_minkowski_two_order_audit.md`](program_m_minkowski_two_order_audit.md).
The same output records the deterministic scaling comparison described in
[`program_m_minkowski_two_scaling_audit.md`](program_m_minkowski_two_scaling_audit.md).
