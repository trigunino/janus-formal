# HESSIAN-GLOBAL-01 — selected-trace invariant-domain terminal

## Strongest current facade

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzNuclearDuhamelZetaTerminal4D
```

This facade imports the preferred Candidate-A route from the concrete H14
reduced Green operator to the physical D11 five-sector spectral-cut atlas.

## What changed at this frontier

Earlier frontends constructed a logarithmic derivative operator from the
Duhamel limits and then required either

```text
generatedTrace = selectedReferenceTrace
```

or

```text
generatedLogarithmicOperator = selectedLogarithmicOperator.
```

The selected-trace frontend removes both comparisons.  Each short-time boundary
packet is parameterized directly by the `IntrinsicLogarithmicDerivativeTraceData`
already selected by its reference chart.  Its limit target is definitionally

```text
reference.family.logarithmicDerivativeOperator a
  = G_ref,a H'_ref,a,
```

and its nuclear certificate is definitionally `reference.traceClass a`.
Therefore the scalar produced by the endpoint construction is the selected
reference trace without transport or uniqueness being needed at the atlas
boundary.

## Complete generated chain

The terminal facade now derives:

```text
H_a F_a = F_a H_0,
F_a P_s = P_s F_a,
G'_a = -G_a H'_a G_a,
Tr(K_actual,a(t)) = Tr(K_actual,0(t)),
T_actual(a) = 0,
Tr(D_a(t)) = integral_s Tr(D_a(t,s)) dμ(s),
Tr(D_a(t,s)) = Tr(H'_a K_a(t)),
integral_region Tr(D_a(t)) dt = Tr(D_region,a),
countertermDerivative(a) = Tr(C'_a),
C'_a - D_short,a = G_ref,a H'_ref,a + B_a,
D_long,a = B_a,
finitePartLogDerivative(a) = Tr(G_ref,a H'_ref,a),
Im(zeta'_ref,a(0)) = 0,
T_reference(a) = -Tr(G_ref,a H'_ref,a),
T_relative(a) = Tr(G_ref,a H'_ref,a).
```

The actual/reference subtraction statement is interpreted in the D11 frame,
where the actual coefficient vanishes.

## Canonical Schwarz reflection

No Mellin conjugation statement is supplied per reference.

For a real heat trace the Mellin kernel satisfies pointwise

```text
kernel(s,t) = conj(kernel(conj s,t)).
```

The certified half-plane integrability and the real continuous-linear
conjugation map move conjugation through the Bochner integral.  Mathlib's Gamma
conjugation then gives Schwarz symmetry of the normalized Mellin candidate.

For every reference parameter the remaining analytic data are:

* one open preconnected domain;
* zero and one Mellin seed in that domain;
* stability of the domain under complex conjugation;
* analyticity of the original zeta continuation there.

A generic real-Fréchet derivative proof shows automatically that

```text
s ↦ conj(zeta(conj s))
```

is analytic on the same domain.  The identity principle propagates the Mellin
Schwarz equality to zero.  Restriction to the real axis then forces
`Im(zeta'(0)) = 0`.

## Removed independent inputs

The strongest interface no longer contains independent fields for:

```text
bounded/nuclear trace cyclicity,
trace of a Duhamel slice after cyclic rotation,
trace of the probability average,
probability collapse,
integral Tr = Tr integral,
counterterm derivative = nuclear trace,
short-time boundary identity,
long-time boundary identity,
global Duhamel-Green trace identity,
Mellin integral conjugation,
normalized Mellin conjugation,
analyticity of the reflected continuation,
reality of zeta'(0),
generated trace = selected trace,
generated operator = selected operator,
reference zeta coefficient,
relative zeta coefficient.
```

## Remaining irreducible reference-side proofs

For the base reference and each local spectral-cut reference:

1. Construct the genuine positive-time heat and Duhamel operators on the fixed
   reduced Hilbert space.
2. Prove their intrinsic nuclearity and parameter differentiability.
3. Construct the common rank-one systems for simplex slices, collapsed
   `H'_a K_a(t)` operators and counterterm variations.
4. Prove nuclear-norm and scalar-trace summability.
5. Prove the simplex, short-time and long-time sum/integral exchanges.
6. Prove the heat semigroup law and identify every slice with
   `K_left (H' K_right)`.
7. Prove the renormalized short-time cutoff convergence directly to the
   selected `G_ref H'_ref` operator, modulo the matching term.
8. Prove the finite long-time primitive identity and decay of its terminal
   primitive.
9. Construct one conjugation-invariant open preconnected continuation domain
   joining the Mellin half-plane to zero and prove analyticity of the original
   reference continuation on it.

## Elaboration status

The newly added Schwarz-reflection derivative layer, invariant-domain adapter,
selected-reference boundary packet, selected-reference finite-part assembly,
Candidate-A adapter and terminal import were checked individually with
`lake env lean` in the local branch checkout.

This is not a full repository build.  Earlier modules in the long PR chain may
still expose independent elaboration or instance-synthesis failures when the
complete branch is built.
