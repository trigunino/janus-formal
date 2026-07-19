# MF-COMP-001 — Controlled compression audit

## Question

How much of the lossless decorated skeleton can be removed before distinct
primitive relations become indistinguishable?

The audit compares four invariant summaries on all four-object relation
classes:

| Retained data | Distinct signatures | Relation classes involved in collisions |
| --- | ---: | ---: |
| bare ordered skeleton | 24 | 3,044 |
| skeleton and fiber sizes | 33 | 3,044 |
| plus bridge existence | 51 | 3,044 |
| plus internal and bridge edge counts | 990 | 2,284 |
| complete primitive relation | 3,044 | 0 |

All signatures are canonicalized under relabelling of skeleton components.

## Explicit count-level collision

Masks `23` and `54` are non-isomorphic four-object relations. They have the
same ordered skeleton, fiber sizes, internal edge counts and bridge counts, but
the placement of a self-loop inside a two-object component differs. Counts do
not record which internal object carries the loop.

## Conclusion

Component sizes and edge counts are not sufficient for lossless
reconstruction. Endpoint incidence inside and between fibers contains genuine
invariant information.

This is directly relevant to future throat searches: bottlenecks and privileged
interfaces depend on *which* internal objects carry bridge edges, not only on
how many bridges exist.

MF-COMP-001 therefore rejects count-only decoration as the foundational state.
The full incidence relation remains authoritative. Compressed summaries may be
used only for search indexes or after proving that a target observable factors
through them.

The exact factorization obligation is formalized in
[`program_m_observable_factorization.md`](program_m_observable_factorization.md).

## Evidence boundary

The result is exhaustive for one to four objects and executable (`X`). It is
not a general Lean theorem for arbitrary finite or infinite systems.
