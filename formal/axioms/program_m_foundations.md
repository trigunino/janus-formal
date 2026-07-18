# Program M — Foundational relational pilot

## Status

This file fixes the first **pilot language**, not the ontology of the physical
Universe. Competing foundational languages remain admissible.

## Primitive signature

`MF-A0` supplies only:

- a type `Obj` of primitive objects;
- a type `Rel` of primitive relation labels;
- a truth-valued incidence predicate `holds : Rel -> Obj -> Obj -> Prop`;
- relabellings of objects and relations that preserve `holds`.

No finiteness, topology, order, metric, dimension, differentiability,
probability, causal direction, field, sector exchange, PT symmetry, action or
gorge is included in `MF-A0`.

The use of binary relations is a pilot restriction. Higher-arity, enriched,
categorical, algebraic and spectral primitives must be recorded as distinct
branches rather than encoded silently.

## Equivalence

Two `MF-A0` systems are equivalent only when bijections of `Obj` and `Rel`
preserve and reflect `holds`. Weaker observational equivalences belong to later
stages and must not be confused with foundational isomorphism.

## Reconstruction ladder

Each arrow is an open theorem or construction:

```text
MF-A0 relational system
  -> MF-R1 derived reachability or neighbourhood
  -> MF-R2 candidate topology
  -> MF-R3 candidate dimension/continuum structure
  -> MF-R4 candidate metric or causal structure
  -> MF-R5 fields, symmetries and sectors
  -> MF-R6 geometry candidate
  -> Program P adapter
```

No later structure may be used to define an earlier arrow unless the result is
explicitly labelled circular or conditional.

## Anti-smuggling tests

Every reconstruction claim must provide:

1. the exact axioms used;
2. invariance under `MF-A0` equivalence;
3. a proof that the output is well-defined;
4. a uniqueness statement or explicit multiplicity;
5. a countermodel showing which dropped hypothesis breaks the conclusion;
6. a classification as necessary, conditional, possible or impossible;
7. a check that Janus-specific structure was not encoded in definitions.

In particular, a two-colouring is not evidence for two physical sectors, a
cycle is not a throat, an involution is not PT, and graph distance is not a
physical metric without additional reconstruction theorems.

## First theorem targets

- `MF-TOP-001` (**T**): every selected binary relation yields an Alexandrov
  upper-set topology after the explicitly declared reflexive-transitive
  closure;
- `MF-TOP-002` (**T**): foundational isomorphisms induce homeomorphisms of the
  reconstructed spaces;
- `MF-NOGO-001` (**T**): non-isomorphic empty-edge and self-loop systems on
  two objects produce the same reconstructed topology;
- `MF-NOGO-002` (**T**): one directed two-object system has distinct upper-set
  and lower-set Alexandrov topologies;
- `MF-ENUM-001`: enumerate finite systems only after quotienting relabellings.

The two positive results compile in
`JanusFormal.Foundations.ProgramMTop001`. They reuse Mathlib's
`Relation.ReflTransGen`, `Topology.upperSet` and `AlexandrovDiscrete`; these
library primitives were audited before adding project definitions. The finite
no-go witnesses compile in `JanusFormal.Foundations.ProgramMTopNoGo`.
Uniqueness remains refuted at this level; finite enumeration remains **O**.
