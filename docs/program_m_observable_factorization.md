# MF-OBS-000 — When a compression is safe

## Rule

A compressed description is safe for a chosen observable exactly when the
observable gives the same value to every pair of primitive states that the
compression identifies.

```text
same compressed state
  -> same observable value
```

If this condition holds, the observable can be defined directly on compressed
states. If one collision has different observable values, such a downstream
definition is impossible.

## Proved results

- compression safety is exactly Mathlib's `Function.FactorsThrough` condition;
- for nonempty output types, safety is equivalent to the existence of a
  downstream observable on compressed states;
- one explicit collision with different values proves a no-go;
- an observable factors through the bare causal skeleton exactly when it is
  constant inside every mutual-reachability component;
- every observable factors through the lossless fiber decomposition.

## Consequence for Program M

There is no universally safe lossy compression. Safety is relative to a named
observable. Topology, skeleton, component sizes or edge counts may be used only
after proving the corresponding factorization theorem.

In particular, a proposed throat indicator depending on internal incidence
cannot be computed from the bare skeleton unless a separate theorem proves
that it is constant across all primitive systems with that skeleton.

This result is mathematical. It does not define a throat observable or assert
that any present relational invariant is physical.

