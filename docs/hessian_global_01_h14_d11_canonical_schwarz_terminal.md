# HESSIAN-GLOBAL-01 — canonical Schwarz terminal frontier

## Current strongest facade

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CanonicalSchwarzNuclearDuhamelZetaTerminal4D
```

This facade collects the preferred Candidate-A route from the concrete H14
reduced Green operator to the D11-transported physical five-sector determinant
atlas.

The implementation is architectural and has not yet received a complete Lean
build pass.

## 1. Actual family

The operator-norm differentiable represented D11 frame `F_a` transports

```text
H_red,0,
G_0,
ker H_0,
(ker H_0)ᗮ,
the five physical projectors.
```

In fixed coordinates the reduced operator and Green family are constant.  In
moving coordinates their derivatives are commutators with `F'_a F_a⁻¹`, and

```text
G'_a = -G_a H'_a G_a.
```

The actual nuclear heat family is unitarily conjugated to its H12 value, so its
intrinsic heat trace, finite part, regularized zeta derivative and determinant
coordinate are constant in the family parameter.

## 2. Reference Duhamel family

For each reference, the Duhamel simplex slices have common rank-one spectra

```text
D_a(t,s)
  = sum_i c(a,t,s,i) rankOne(x(a,t,i),y(a,t,i)).
```

Integrating the coefficients in `s` constructs the genuine averaged Duhamel
operator.  A certified sum/integral exchange proves

```text
Tr(D_a(t)) = integral_s Tr(D_a(t,s)) dμ(s).
```

Each slice is identified with

```text
K_left(a,t,s) (H'_a K_right(a,t,s)).
```

Automatic nuclear cyclicity and

```text
K_right(a,t,s) K_left(a,t,s) = K_full(a,t)
```

give

```text
Tr(D_a(t,s)) = Tr(H'_a K_full(a,t)).
```

Probability normalization removes the simplex integral.

## 3. Short and long time

The collapsed insertion/full-heat operator has a common rank-one expansion on
each time region.  Integrating the coefficients constructs nuclear regional
operators and proves

```text
integral_region Tr(D_a(t)) dt = Tr(D_region,a).
```

At short time, cutoff counterterms and cutoff spectral integrals converge, and
their renormalized remainder tends to `G_a H'_a`.  Uniqueness of limits gives

```text
C'_a - D_short,a = G_a H'_a + B_a.
```

At long time, a finite-cutoff primitive identity and decay of the terminal
primitive give

```text
D_long,a = B_a.
```

The matching term cancels and intrinsic trace subtraction yields

```text
countertermDerivative(a)
  - integral_short Tr(D_a(t)) dt
  - integral_long Tr(D_a(t)) dt
    = Tr(G_a H'_a).
```

## 4. Counterterm

The scalar counterterm contribution is itself a differentiable rank-one trace
series.  Uniform summable control of its coefficient derivatives allows
termwise differentiation.  The resulting derivative series is simultaneously
an intrinsic nuclear expansion of the counterterm variation operator.
Therefore

```text
countertermDerivative(a) = Tr(C'_a)
```

is a theorem rather than a comparison field.

## 5. Canonical Mellin Schwarz symmetry

For a real heat trace,

```text
kernel(s,t) = conj (kernel(conj s,t))
```

pointwise.  In the convergence half-plane the continuation packet already
provides integrability.  Complex conjugation is bundled as a real continuous
linear map, so it commutes with the Bochner integral:

```text
I(s) = conj (I(conj s)).
```

Mathlib's Gamma conjugation then gives

```text
M(s) = conj (M(conj s)).
```

for the normalized Mellin candidate.  No Mellin symmetry is supplied per
reference.

## 6. Analytic reflection and zeta reality

For each parameter, one common open preconnected domain contains zero and a
Mellin seed.  The zeta continuation and

```text
s ↦ conj (zeta (conj s))
```

are analytic there.  They agree near the seed by the canonical Mellin formula;
the analytic identity principle makes them equal on the whole domain.

On the real axis near zero,

```text
zeta(x) = conj (zeta(x)).
```

Restricting the complex derivative to the real axis and composing with the
imaginary-part continuous linear map gives

```text
Im (zeta'(0)) = 0.
```

Thus reference coefficient reality is derived, not stored.

## 7. Reference and relative coefficients

The finite-part variation and zeta reality imply

```text
T_reference(a) = -Tr(G_a H'_a).
```

The actual coefficient is zero in the D11 unitary frame.  Analytic subtraction
of actual and reference Mellin continuations therefore gives

```text
T_relative(a) = Tr(G_ref,a H'_ref,a).
```

The base and every local spectral-cut coefficient are generated from these
identities.  The existing reference operators, zeta charts, determinant
cocycle, Quillen metric, circle clutching and physical kernel data are retained.

## 8. Removed independent inputs

The strongest facade no longer accepts any of the following as independent
facts:

```text
trace cyclicity,
trace of the Duhamel average,
probability collapse,
integral Tr = Tr integral,
counterterm derivative = operator trace,
short-time boundary identity,
long-time boundary identity,
global Duhamel-Green scalar identity,
Mellin integral conjugation,
normalized Mellin conjugation,
reality of zeta'(0),
reference coefficient equality,
relative coefficient equality.
```

## 9. Remaining irreducible proofs

For the base reference and each local reference:

1. construct the genuine heat and Duhamel operators on the fixed reduced
   Hilbert space;
2. prove intrinsic nuclearity and parameter differentiability;
3. construct the simplex, collapsed-time and counterterm rank-one systems;
4. prove nuclear-norm and trace summability;
5. prove the simplex, short-time and long-time sum/integral exchanges;
6. prove the heat semigroup law and slice operator identifications;
7. prove short-time renormalized convergence;
8. prove the finite long-time primitive identity and terminal decay;
9. prove analytic regularity of the reflected continuation on the selected
   common domain.

The final complex reflection statement is now a regularity theorem, not a
scalar determinant comparison.

## 10. Expected elaboration-sensitive points

A future Lean pass should focus first on:

* the exact `ContinuousLinearMap.integral_comp_comm` spelling;
* `Complex.Gamma_conj` orientation;
* simplification of conjugated complex powers in the Mellin kernel;
* termwise derivative arguments using `hasDerivAt_tsum`;
* dependent transport of intrinsic nuclear trace certificates;
* sum/integral interchanges and set-integral measures;
* uniqueness of operator-valued limits;
* deep Candidate-A instance synthesis and reducible types.

No `sorry`, `admit`, replacement Green operator or second Hilbert completion is
intended by the architecture.
