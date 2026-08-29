# HESSIAN-GLOBAL-01 — family-index and intrinsic reference-atlas route

## Status

This document records the continuation of the preferred five-sector route on
PR #60.  It is an implementation and dependency map.  It does **not** claim
that the current branch elaborates successfully in Lean.

The pointwise H14 theorem is now followed by one operator-family route:

```text
H_a on the full Candidate-A Hilbert space
→ genuine fibres (ker H_a)ᗮ
→ unitary trivialization to (ker H_0)ᗮ
→ uniformly gapped reduced family
→ differentiable Green family
→ intrinsic Tr(G_a H'_a)
→ relative Bismut--Freed connection
→ reference-generated spectral-cut atlas
→ Quillen clutching and holonomy.
```

The finite kernels are transported separately by one fixed named basis type,
so the zero-mode determinant line is also a genuine family rather than only a
basepoint object.

## 1. Uniformly gapped reduced families

### Fixed-space gap and Green family

`P0EFTJanusProgramPSelfAdjointUniformGapFamily4D.lean`

A family on one fixed real Hilbert space stores:

```text
H_a = H_a†
c > 0
c ‖x‖ ≤ ‖H_a x‖  for every a and x.
```

It constructs, for every parameter:

```text
H_a : E ≃L E
G_a = H_a⁻¹
H_a G_a = 1
G_a H_a = 1
‖G_a‖ ≤ c⁻¹
ker H_a = 0.
```

### Varying actual-kernel complements

`P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D.lean`

The actual reduced spaces are not treated as definitionally equal.  The input
is a certified unitary family

```text
T_a : (ker H_0)ᗮ ≃L (ker H_a)ᗮ.
```

The transported operator is

```text
H̃_a = T_a⁻¹ H_a,red T_a.
```

Self-adjointness and the lower bound are transported to the fixed base fibre.
No second reduced operator family is supplied independently.

### Uniform resolvent and no crossing

`P0EFTJanusProgramPSelfAdjointUniformGapFamilyResolvent4D.lean`

For every family parameter and every real spectral parameter satisfying

```text
|λ| < c,
```

the file constructs

```text
(H̃_a - λ)⁻¹
```

with the uniform estimate

```text
‖(H̃_a - λ)⁻¹‖ ≤ (c - |λ|)⁻¹.
```

It also exports an explicit no-zero-crossing certificate for the reduced
family.  This is deliberately not advertised as a complete formal spectral
flow theorem; it is the precise uniform-gap statement from which vanishing of
reduced crossings follows.

## 2. Differentiable inverse and logarithmic derivative

`P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D.lean`

A differentiable operator family has a specified derivative `H'_a`.  The
inverse derivative is constrained to the canonical formula

```text
G'_a = -G_a H'_a G_a.
```

The logarithmic derivative operator is fixed to

```text
L_a = G_a H'_a.
```

The inverse derivative cannot be replaced by an unrelated bounded family.

## 3. Intrinsic Bismut--Freed trace

`P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D.lean`

At every parameter, `L_a = G_a H'_a` is equipped with an
`IntrinsicNuclearTraceData` certificate.  Consequently

```text
Tr_intrinsic(G_a H'_a)
```

is independent of the chosen certified summable rank-one presentation.

For an actual/reference pair the relative trace is

```text
Tr_rel(a)
  = Tr_intrinsic(G_a H'_a)
  - Tr_intrinsic(G^ref_a (H^ref_a)').
```

The complex connection coefficient uses the zeta-prime convention

```text
A_BF(a) = -Tr_rel(a).
```

`P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D.lean`

identifies the derivative of the Mellin/zeta family with this exact operator
trace.  It then proves:

```text
∇_BF detζ = 0
(d/da) log det_finite-part = Tr_rel(a)
metric derivative = 2 Tr_rel(a) · metric weight.
```

## 4. Circle bridge and phase holonomy

`P0EFTJanusProgramPRelativeBismutFreedCircleTraceBridge4D.lean`

The intrinsic trace coefficient is identified with the explicit circle
Quillen coefficient.  The existing endpoint clutching condition then gives:

```text
Tr_rel(a) = -A_circle
circle-parallel determinant
endpoint large-gauge clutching
Hol_Quillen = phaseζ(0) / phaseζ(1).
```

Thus the circle bridge is no longer merely an equality between two unrelated
scalar one-forms; one side is the intrinsic operator trace.

## 5. Candidate-A family-index specialization

`P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D.lean`

combines:

* varying actual-kernel complements;
* their unitary trivialization;
* uniform reduced gap;
* differentiable Green family;
* intrinsic logarithmic derivatives;
* one reference family;
* the anchored Mellin/zeta family.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.lean`

specializes this construction to the genuine Candidate-A operator.  At
parameter zero the transported reduced family is identified with the exact H14
operator on the orthogonal complement of its actual kernel.  The output also
contains the common resolvent interval, no-crossing certificate, circle trace
identity and phase holonomy.

## 6. Change of reference and spectral-cut cocycle

`P0EFTJanusProgramPIntrinsicRelativeTraceReferenceCocycle4D.lean`

For one actual family and references `R_i`, it defines

```text
T_i     = Tr(H/R_i)
T_ij    = Tr(R_i/R_j).
```

The identities

```text
T_j = T_i + T_ij
T_ii = 0
T_ji = -T_ij
T_ij + T_jk = T_ik
```

are algebraic consequences of the intrinsic traces.

`P0EFTJanusProgramPIntrinsicBismutFreedReferenceAtlas4D.lean`

attaches one honest Mellin/zeta family to each reference and requires only the
local Bismut--Freed identity.  It derives:

```text
A_i - A_j = T_ij
(g_ij)' = T_ij g_ij
g_jk g_ij = g_ik
connection gauge covariance
finite-part logarithm change = T_ij.
```

`P0EFTJanusProgramPIntrinsicBismutFreedReferenceQuillenAtlas4D.lean`

selects one reference chart as the circle chart and combines the generated
spectral-cut atlas with circle parallelism, clutching and holonomy.

## 7. Candidate-A generated spectral-cut atlas

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D.lean`

replaces the freely supplied multi-chart atlas by the operator-generated
reference atlas.  Its selected chart is exactly the previously anchored
Candidate-A family, so at parameter zero:

```text
local determinant = intrinsic Candidate-A determinant.
```

All other chart transitions are generated by intrinsic reference-change
traces.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFamilyIndexClosure4D.lean`

exports one terminal certificate containing:

```text
intrinsic H14--Quillen closure
actual reduced family
uniform Green and resolvent bounds
absence of reduced zero crossings
Bismut--Freed trace formula
reference trace cocycle
determinant transition cocycle
connection gauge law
circle clutching and phase holonomy.
```

## 8. Finite zero-mode family and determinant line

`P0EFTJanusProgramPFiniteKernelBasisFamily4D.lean`

A fixed finite type `ZeroMode` indexes a basis of `ker H_a` at every parameter.
Keeping coordinates fixed constructs canonical transports

```text
ker H_a ≃ₗ ker H_b.
```

They preserve every named basis vector, compose exactly and prove

```text
finrank ker H_a = card ZeroMode
```

for all parameters.  A fixed five-sector assignment gives constant sector
multiplicities.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D.lean`

specializes the construction to Candidate-A.  At parameter zero the family
basis agrees with the exact action-generator basis from H14.  At every
parameter:

```text
H_a e_i(a) = 0
finrank ker H_a = Σ_s multiplicity_s.
```

`P0EFTJanusProgramPFiniteKernelDeterminantLineFamily4D.lean`

constructs the top exterior power

```text
DetKer_a = ⋀^(card ZeroMode) ker H_a.
```

It proves that every fibre is one-dimensional, the named top wedge is nonzero,
and kernel transport induces determinant-line transport preserving that named
volume exactly.

## Remaining irreducible proofs

The new architecture isolates the following family-level mathematical work.

### A. Actual Candidate-A family

Construct `H_a` from a genuine family of Candidate-A configurations and prove
self-adjointness for every parameter.

### B. Kernel-complement trivialization

Construct the unitary maps

```text
T_a : (ker H_0)ᗮ ≃L (ker H_a)ᗮ
```

and prove the uniform reduced gap.

### C. Differentiability and inverse differentiation

Prove differentiability of the transported reduced family and the Banach-space
inverse formula `G' = -G H' G`.

### D. Intrinsic nuclear logarithmic trace

Construct a presentation-independent nuclear trace for every exact operator
`G_a H'_a` and for each reference family.

### E. Zeta/Bismut--Freed comparison

Prove that the derivative at zero of the honest Mellin continuation equals the
negative intrinsic relative logarithmic trace.

### F. Reference families and spectral cuts

Construct the local reference operators associated with the actual spectral
cuts or parametrices and prove that their Mellin families satisfy the local
trace comparison.

### G. Kernel basis family

Construct the named basis `e_i(a)` of every actual kernel, prove its agreement
with the H14 action generators at the basepoint and prove the desired
regularity of this finite kernel frame.

### H. Geometric family-index identification

Identify the intrinsic trace connection with the geometric Bismut--Freed
connection beyond the one-dimensional circle model, including the appropriate
local family-index curvature formula.

## Terminal logical chain

After the pointwise H10--H14 obligations and the family-level obligations above,
the implemented route is:

```text
genuine Candidate-A action family
→ self-adjoint Hessian family H_a
→ named finite kernels + true complements
→ unitary fixed-space reduction
→ uniform Green/resolvent family
→ intrinsic logarithmic derivative trace
→ Bismut--Freed determinant connection
→ operator-generated spectral-cut atlas
→ finite kernel determinant line
→ Quillen metric, clutching and holonomy.
```
