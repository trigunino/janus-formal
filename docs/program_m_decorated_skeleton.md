# MF-DEC-001 — Lossless decorated skeleton

## Why this layer exists

The bare oriented skeleton retains irreversible ordering but erases the inside
of every mutual-reachability class. MF-DEC-001 attaches that information back
without adding distance, coordinates or geometry.

## Structure

```text
partially ordered skeleton
+ fiber of primitive objects over each class
+ original directed relation between fiber elements
```

Every primitive object belongs to exactly one fiber. Every primitive edge is
then classified uniquely as:

- **internal**: both endpoints lie in the same fiber;
- **bridge**: the endpoints lie in different fibers.

Every bridge is proved to point strictly forward in the skeleton order.

## What is proved

- the primitive object type is equivalent to the disjoint union of all fibers;
- the selected primitive relation is preserved exactly under that equivalence;
- internal and bridge edges form a disjoint exhaustive split;
- bridge edges respect strict irreversible reachability.

Consequently, this representation is lossless.

## What is not proved

This is a baseline, not yet a *minimal* decoration. Keeping the full relation
guarantees that no potential throat signal is destroyed, but it performs no
compression. No internal cycle, bottleneck or bridge has yet been identified
with a physical throat.

The next research problem is controlled compression: remove one kind of
decoration at a time and prove which invariant or reconstruction ability is
lost.

