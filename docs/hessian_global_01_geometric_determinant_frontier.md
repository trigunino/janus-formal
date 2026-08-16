# HESSIAN-GLOBAL-01 — geometric determinant frontier after PR #60

## Status

This note supersedes the old statement that the finite-kernel Fredholm factor
and the reduced zeta determinant are only a split cartesian packet.

The implementation now contains an actual tensor-product determinant layer.
It does **not** claim that the remaining geometric families-index theorems or
Lean elaboration cleanup are complete.

## 1. Full Fredholm--zeta determinant fibre

For the genuine self-adjoint Candidate-A Hessian family `H_a`, the finite
Fredholm factor is

```text
Det_Fred(H_a) = Hom(det coker H_a, det ker H_a).
```

It is first complexified,

```text
Complex ⊗[Real] Det_Fred(H_a),
```

and then tensored with the determinant line of the invertible reduced family.
For the reduced invertible factor the determinant line is canonically the
complex scalar line, so the implemented full fibre is

```text
FullDet(H_a)
  = (Complex ⊗[Real] Det_Fred(H_a))
      ⊗[Complex] Det_red(H_a).
```

The zeta determinant occupies the reduced factor; it is no longer stored as an
unrelated component of a pair.

The canonical right-unit tensor equivalence

```text
FullDet(H_a) ≃ₗ[Complex] Complex ⊗[Real] Det_Fred(H_a)
```

sends the full zeta section exactly to

```text
D_zeta(a) • complexifiedFredholmFrame(a).
```

Therefore the previous item 18, understood as the algebraic tensor-product
identification, is architecturally closed.

## 2. Canonical transport and fixed-fibre atlas

The named kernel coordinates generate kernel and cokernel transports.  Their
top exterior powers generate the actual Fredholm-line transport, which
preserves the canonical Fredholm frame exactly.

Scalar extension gives a genuine complex-linear transport of the complexified
Fredholm lines.  Conjugating it by the full-tensor collapse produces

```text
FullDet(H_a) ≃ₗ[Complex] FullDet(H_b).
```

The basepoint transport trivializes every full determinant fibre against
`FullDet(H_0)`.  In that fixed fibre every spectral-cut chart is literally

```text
D_i(a) • one fixed Fredholm frame.
```

The existing zeta transitions therefore become genuine full-line gluing laws,

```text
g_ij(a) • s_i(a) = s_j(a),
```

and the local connection obeys the same exact gauge law in the full tensor
line.

The finite Fredholm factor is flat in this canonical coordinate transport; all
nontrivial connection coefficient is carried by the reduced zeta factor.

## 3. C1 Fredholm splitting frontier

The original named-kernel family only fixed a basis of every `ker H_a`; it did
not assert regularity in `a`.

The preferred route now records regularity in the common ambient Hilbert space,
not in a parameter-dependent subtype.

Two C1 packets are isolated:

```text
mode ↦ (a ↦ namedKernelVector_a(mode))
```

and, for every fixed vector of `(ker H_0)ᗮ`,

```text
a ↦ T_a(v) : ambient Candidate-A Hilbert space.
```

Together they form a C1 orthogonal Fredholm splitting packet for

```text
E = ker H_a ⊕ (ker H_a)ᗮ.
```

The exact kernel equation, complement membership, unitarity, fixed kernel rank
and basepoint agreement with the action-generated zero modes are retained.

What remains for item 16 is no longer construction of an abstract basis family.
It is the genuine proof that the already selected Candidate-A named basis and
complement trivialization satisfy these C1 packets.

## 4. Geometric Bismut--Freed comparison beyond the circle

The one-dimensional circle model proves connection/holonomy statements along a
single path, but it cannot by itself prove the curvature of a connection on a
higher-dimensional parameter space.

The preferred geometric interface now separates these statements.

For a geometric parameter base `B`, tangent type `TB`, a geometric
Bismut--Freed one-form `A_geom`, and a Candidate-A family path `gamma`, the
pathwise comparison theorem required is

```text
gamma^* A_geom(a)
  = -Tr(G_a H'_a - G_ref,a H'_ref,a).
```

Once this identity is supplied, the geometric pullback connection equals the
existing intrinsic operator-trace/zeta connection, including on the full
Fredholm--zeta tensor line, and the full zeta section is parallel for that
geometric connection.

Independently, the multidimensional families-index theorem required is

```text
F_BF = F_local-families-index.
```

This curvature identity is kept separate from circle holonomy.

## 5. Program-P-derived Quillen status

The D10/D11 `QuillenBismutFreedStatus` is no longer accepted as a free package
in the preferred Candidate-A interface.

Program P now instantiates its fields with existing concrete results:

```text
determinant line constructed
zeta / finite-part metric relation
full-tensor Bismut--Freed parallelism
operator-generated spectral-cut descent
circle holonomy formula
```

and consumes the geometric families-index curvature equality for the remaining
curvature field.

Thus the essential external geometric data have been reduced to:

1. the closed D11 natural analytic family input;
2. the geometric Bismut--Freed one-form and Candidate-A path;
3. the one-form/operator-trace comparison;
4. the local families-index curvature comparison.

No independent Quillen determinant family is supplied.

## 6. Current preferred terminal interface

The new terminal family gate combines exactly:

```text
C1 actual Fredholm splitting
+
closed D11 natural analytic family
+
geometric BF one-form = intrinsic operator trace along the family
+
geometric BF curvature = local families-index curvature
```

and exports:

```text
regular named zero modes
Program-P-derived Quillen/Bismut--Freed status
parallel full Fredholm--zeta determinant section
multidimensional families-index curvature equality.
```

## 7. Genuine remaining mathematical proofs

The new determinant architecture does not discharge the earlier physical and
analytic premises.  In particular the genuine proofs still include the
Candidate-A five-sector completion/core agreement, exact action-symmetry
invariance and kernel identification, projected Hessian commutation, sector
Garding estimates and off-diagonal margin, H11 smallness, intrinsic relative
nuclear expansions, uniform heat/Mellin continuation, and construction and
regularity of the actual operator/reference families.

At the final family-geometric layer the remaining irreducible work is now
sharply isolated:

```text
prove C1 regularity of the selected named kernel basis;
prove C1 regularity of the selected complement trivialization;
construct/identify the D11 natural Candidate-A family geometry;
prove gamma^* A_BF = -Tr(GH' - G_ref H'_ref);
prove F_BF = F_local-families-index.
```

The algebraic full determinant tensor product, its spectral-cut atlas, its
canonical finite-factor transport and its full-line zeta connection are no
longer entries on this remaining list.
