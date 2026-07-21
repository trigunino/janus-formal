# MF-DIM-000 — Exact order invariants before dimension

## Literature boundary

The Myrheim–Meyer estimator uses the ordering fraction

```text
r = 2 R / (n (n - 1))
```

where `R` is the number of strict comparable pairs. Its interpretation as a
dimension estimator assumes a causal set faithfully approximating a suitable
Minkowski interval and is statistical/asymptotic, not a theorem for every
finite partial order. See the dimension-estimator discussion in
[Surya's causal-set review](https://link.springer.com/article/10.1007/s41114-019-0023-1).

Program M therefore computes the underlying exact order invariants before
attaching a dimension interpretation.

## Computed invariants

For each finite skeleton order, the audit computes:

- number of elements;
- number and fraction of strict comparable pairs;
- maximum chain size (height);
- maximum antichain size (width);
- multiset of closed interval sizes.

These depend only on the quotient order and contain no metric input.

## Exhaustive result through four primitive objects

At most four primitive objects produce 24 bare skeleton orders. They collapse
to only 14 signatures when classified by size and ordering fraction. Even the
combined size, fraction, height, width and interval-size profile gives only 19
signatures.

The first collision already occurs on three skeleton elements:

```text
V order:       0 < 1 and 0 < 2
Lambda order:  0 < 2 and 1 < 2
```

The orders are orientation reversals and are not isomorphic as directed
orders, but all audited invariants agree:

```text
strict relations = 2
height = 2
width = 2
closed interval sizes = [1,1,1,2,2]
```

## Conclusion

These invariants do not select an orientation and do not uniquely identify a
finite order. An inferred Myrheim–Meyer dimension is conditional on an
independently justified manifold-like statistical regime.

This is not a criticism of the estimator inside its intended domain. It is a
no-go against using a small-order value alone to claim that dimension or time
orientation has emerged in Program M.

The next stage must separate:

1. exact order invariants;
2. statistical manifold-likeness tests;
3. conditional dimension estimators;
4. independent orientation-sensitive observables.

