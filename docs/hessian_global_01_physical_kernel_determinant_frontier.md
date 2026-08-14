# HESSIAN-GLOBAL-01 — physical kernel and determinant frontier

## Purpose

The preferred Candidate-A determinant line is already built from the true
Fredholm data of the actual Hessian.  The remaining zero-mode issue is not the
existence of a kernel basis — one named basis already exists — but whether the
chosen family basis remains physically resolved into the five H12/H14 sectors.

The new route separates that finite-dimensional question from the determinant
line itself.

## 1. Existing named basis versus physical sectors

The original family stores

```text
e_i(a) : basis of ker H_a
```

with a fixed sector label `s(i)` inherited from the H12 action generators.
A fixed label is not enough to imply

```text
e_i(a) ∈ E_{s(i)}.
```

At `a = 0`, however, H12 already proves the stronger statement: the action
generator is fixed by its physical projector, and the family basis agrees with
that generator basis.

## 2. All-parameter projector commutation

Once the exact D11 realization is componentwise in the five physical sectors,
the full Candidate-A family satisfies

```text
H_a P_s = P_s H_a
```

for every parameter.  Thus each `P_s` preserves the true kernel.

## 3. Canonical projected physical zero modes

Define

```text
e~_i(a) := P_{s(i)} e_i(a).
```

These vectors are constructed without an additional transport hypothesis.  They
are proved to be:

```text
H_a e~_i(a) = 0
e~_i(a) ∈ E_{s(i)}
P_t e~_i(a) = 0   for t ≠ s(i)
e~_i(0) = e_i(0)
```

and, whenever the original named family is C1,

```text
a ↦ e~_i(a)
```

is C1 in the common ambient Hilbert space.

## 4. Exact finite-dimensional remaining condition

The remaining physical-kernel theorem is now just:

```text
for every a, { e~_i(a) }_i is a basis of ker H_a.
```

Once that is proved, one obtains a preferred physical
`FiniteKernelBasisFamilyData` and a canonical coordinate transport sending

```text
e~_i(a) ↦ e~_i(b).
```

This route can replace the older arbitrary named-basis transport; one no longer
needs to prove that the old transport happened to preserve sectors.

## 5. The determinant line does not depend on this basis replacement

For a self-adjoint index-zero Fredholm operator,

```text
Det_Fred(H_a) = Hom(det coker H_a, det ker H_a).
```

The canonical Fredholm frame is the top-exterior self-adjoint equivalence

```text
det coker H_a ≃ det ker H_a
```

itself.  For any top kernel vector `v`, if the matching cokernel vector is the
inverse image of `v` through this equivalence, the determinant frame sends it
exactly back to `v`.

Therefore simultaneous kernel/cokernel basis changes cancel in the `Hom`
factor.  Named volumes are useful witnesses and transport coordinates, but do
not define a different Fredholm frame.

The full tensor section remains

```text
D_zeta(a) • complexifiedFredholmFrame(a)
```

after the physical kernel basis is selected.  There is no extra finite-sector
connection coefficient to add to the already constructed zeta/Bismut--Freed
connection.

## 6. Remaining proof target

The preferred finite-dimensional target can now be attacked either by:

1. proving linear independence/completeness of the projected vectors directly;
2. proving a nonvanishing Gram determinant for the projected family;
3. constructing a sector-covariant kernel transport, which then propagates the
   H12 basepoint basis sector-by-sector.

The determinant tensor product, determinant frame and zeta coordinate do not
need to be rebuilt whichever route is chosen.
