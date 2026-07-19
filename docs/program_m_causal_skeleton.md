# MF-CAUS-000 — Oriented reachability skeleton

## Construction

Objects that can reach each other in both directions are grouped into one
class. The classes retain the one-way reachability relation between them.

```text
primitive directed relation
  -> reachability preorder
  -> mutual-reachability classes
  -> partially ordered skeleton
```

For example, if `A`, `B` and `C` form a directed cycle while that cycle reaches
`D` but `D` cannot return, the skeleton is:

```text
{A,B,C}  ->  {D}
```

## Proved properties

- two objects have the same class exactly when they are mutually reachable;
- one class is below another exactly when its representatives are reachable;
- strict order between classes is exactly one-way, irreversible reachability;
- the class space is a partial order by Mathlib's antisymmetrization theorem.

## Interpretation boundary

This is called a *causal skeleton* only as a research label. It is not yet a
physical causal order. No clocks, signals, light cones, metric or Lorentzian
geometry have been constructed.

## Information retained and lost

The skeleton retains irreversible ordering between components. It deliberately
forgets the internal edge pattern, path multiplicity and cycle structure inside
each component.

Program M must therefore keep a decorated two-level object:

```text
ordered skeleton
+ internal relational data attached to every class
```

This matters for a possible throat: a throat-like structure might depend on
internal cycles or bottlenecks that vanish in the bare quotient. No throat claim
may be made from the skeleton alone.

## Next target

`MF-DEC-001` now supplies a lossless fiber decoration without introducing a
metric or geometry. Minimality is not claimed; controlled compression remains
open.
