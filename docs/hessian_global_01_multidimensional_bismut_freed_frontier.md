# HESSIAN-GLOBAL-01 — genuine multidimensional Bismut–Freed frontier

## Why this frontier exists

The preferred Candidate-A route already has a genuine one-parameter family

```text
a ↦ H_a
```

with true kernel complements, a transported reduced family, Green operators,
intrinsic nuclear logarithmic traces, Mellin/zeta determinants and the
operator-trace Bismut–Freed coefficient.

A one-dimensional path can determine parallel transport and holonomy, but it
cannot by itself prove a higher-dimensional families-index curvature formula.
The old interface therefore left two objects too abstract:

```text
A_BF : Base → Tangent → ℂ
F_BF : Base → Tangent → Tangent → ℂ
```

where neither linearity of `A_BF` nor derivation of `F_BF = d A_BF` was encoded.

The new route removes that freedom.

## 1. One actual ambient family on a normed base

The higher-dimensional input is now a real normed parameter space `Base` and
one literal ambient family

```text
H : Base → CandidateAHilbert →L[ℝ] CandidateAHilbert.
```

The same `H` is required to be represented by a D11 natural elliptic family in
the exact H12/H14 five-sector coordinates.

The D11 representation is no longer specialized to `ℝ`.  It has an arbitrary
parameter base, sectorwise source/target coordinates, componentwise natural
operator factorization and sector-preserving represented pullbacks.

Consequently every `H_b` is exactly five-block and satisfies

```text
H_b P_s = P_s H_b
```

for the same completion-derived projectors used by H12.

## 2. Genuine varying kernel complements

No reduced multidimensional actual operator is supplied independently.

For every `b`, the zero-mode-free space is the true

```text
(ker H_b)ᗮ.
```

One anchor `b₀` and certified unitary transports

```text
T_b : (ker H_b₀)ᗮ ≃L[ℝ] (ker H_b)ᗮ
```

conjugate the genuine restricted Hessians to one fixed anchor Hilbert space.
A uniform positive gap on the actual current fibers then constructs the fixed
Green family canonically.

## 3. Frechet derivative and intrinsic trace one-form

On a normed `Base`, the reduced fixed family carries a genuine Frechet
derivative

```text
DH_b : Base →L[ℝ] End(E_red).
```

The inverse derivative is required directionwise to be

```text
DG_b[v] = - G_b (DH_b[v]) G_b.
```

For every direction, `G_b DH_b[v]` carries an intrinsic nuclear trace.  The
trace is not merely a function of `v`: the implementation requires an actual
continuous-linear covector

```text
θ_b : Base →L[ℝ] ℝ
θ_b(v) = Tr(G_b DH_b[v]).
```

For an actual/reference pair the real trace part of the BF one-form is

```text
A_trace,b = -(θ_actual,b - θ_reference,b).
```

## 4. Genuine geometric one-form

The geometric BF connection is now an actual complex covector

```text
A_BF,b : Base →L[ℝ] ℂ.
```

A path `γ : ℝ → Base` stores a velocity only together with the proof

```text
γ'(a) = velocity(a).
```

The geometric/operator comparison is pointwise equality of genuine one-forms,
not equality of two arbitrary scalar functions.

## 5. Curvature is derived, not supplied

The BF one-form is Frechet differentiable as a map

```text
Base → (Base →L[ℝ] ℂ).
```

Its curvature is definitionally

```text
F_BF,b(u,v)
  = D A_BF,b[u](v) - D A_BF,b[v](u).
```

Antisymmetry and tangent bilinearity are downstream theorems.

The operator trace one-form is differentiated similarly, producing a derived
trace curvature.  Equality of one-forms and their derivatives gives

```text
F_BF = complexification(F_trace).
```

The families-index theorem then has exactly one remaining curvature input: a
genuine continuous bilinear local index two-form

```text
ω_index,b : Base →L[ℝ] (Base →L[ℝ] ℂ)
```

and the theorem

```text
F_BF = ω_index.
```

There is no independent supplied BF curvature function anymore.

## 6. Restriction to the already constructed Candidate-A path

The multidimensional family must extend the existing one-dimensional result,
not replace it.  A differentiable path through `Base` is therefore required to
satisfy

```text
H_{γ(a)} = actualOperator(a).
```

The geometric BF one-form on that path must recover the already established
operator-trace coefficient

```text
A_BF,γ(a)(γ'(a))
  = -Tr(G_a H'_a - G_ref,a H'_ref,a).
```

Thus the existing zeta connection and circle holonomy remain the pathwise
restriction of the higher-dimensional geometry.

## 7. Physical zero modes

The old kernel-family sector structure only kept fixed labels.  That was not
enough to prove that a named basis vector stayed in the corresponding physical
subspace.

The preferred route now has two stronger constructions.

First, if the canonical kernel transport commutes with the five projectors, the
H12 basepoint sector theorem propagates to every parameter.

Second, independently of that transport covariance, the canonical projected
vectors

```text
e~_i(a) = P_{s(i)} e_i(a)
```

are already proved to be C1, genuine zero modes, physically sector-pure and
equal to the original action-generated modes at `a = 0`.

The remaining finite-dimensional problem can therefore be stated sharply:
prove that these projected vectors remain a basis of the full actual kernel.

## 8. Actual remaining higher-dimensional work

After the structures in this frontier, the genuinely new geometric proofs are:

1. construct the concrete multidimensional Candidate-A parameter space `Base`;
2. construct the ambient natural elliptic D11 family `H_b` on that base;
3. prove its restriction to the existing path is exactly `actualOperator(a)`;
4. construct the unitary trivialization of the true `(ker H_b)ᗮ` family and a
   uniform reduced gap;
5. prove Frechet differentiability of the transported reduced family and the
   inverse formula in all tangent directions;
6. construct the intrinsic nuclear trace covector and prove its continuity and
   linearity in tangent directions;
7. construct the geometric BF one-form and prove its value/derivative agreement
   with the intrinsic trace one-form;
8. construct the local families-index two-form and prove
   `F_BF = ω_index`;
9. prove completeness of the projected physical named kernel family (or,
   equivalently, provide a sector-covariant physical kernel transport).

The full determinant tensor product, its complex vector-bundle structure, the
zeta section, spectral-cut gluing, pathwise BF trace connection and circle
holonomy are not on this remaining list.
