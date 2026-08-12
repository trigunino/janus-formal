# HESSIAN-GLOBAL-01 — preferred five-sector actual-kernel route

## Status

This document records the implementation frontier on PR #60. It is an
architectural and mathematical dependency map; it does **not** claim that the
current branch elaborates successfully in Lean.

The preferred route uses one physical Hilbert decomposition throughout:

```text
E ≃ M × A × S × L × B
```

with the five factors

1. metric/diffeomorphism,
2. Abelian gauge,
3. primitive SpinC matter,
4. longitudinal/LL,
5. boundary/finite BV.

No second decomposition is introduced on the kernel complement, no finite
projection replaces the actual kernel, and the determinant route now uses an
intrinsic relative trace on `(ker H)ᗮ`.

## Implemented chain

### 1. Completion coordinates and the genuine smooth core

`P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D.lean`

* converts the completion isometry to the orthogonal product resolution used by
  H12;
* proves agreement with the canonical bulk/matter/LL smooth-core projectors;
* transports reconstruction and Pythagoras to the embedded Candidate-A core.

### 2. Exact action-symmetry generators

`P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryGenerators4D.lean`

* assumes only local invariance of the genuine augmented action;
* differentiates that identity to obtain `H v = 0`;
* places each generator in the range of its physical projector;
* proves annihilation by every other projector and cross-sector orthogonality;
* contains no Gårding or kernel-completeness assumption.

### 3. Commutation and restriction to the true kernel complement

`P0EFTJanusProgramPFiniteProjectedOffDiagonalCommutation4D.lean`

`P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D.lean`

* reduces projector commutation to vanishing projected off-diagonal blocks;
* proves preservation of the actual kernel;
* restricts the same projectors canonically to `(ker H)ᗮ`;
* derives identity resolution and Pythagoras on that true complement.

### 4. Canonical principal and H11 energies

`P0EFTJanusProgramPKernelComplementAmbientForms4D.lean`

`P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D.lean`

`P0EFTJanusProgramPGlobalCandidateACanonicalReducedPhysicalBound4D.lean`

* restricts the genuine BRST--SpinC--LL principal form to `(ker H)ᗮ`;
* restricts the seven genuine H11 physical blocks to the same space;
* defines the total reduced energy from the actual augmented Hessian;
* proves `E_total = E_principal + E_H11`;
* transports the typed dense-core-to-chart constant to an explicit reduced
  H11 quadratic bound;
* proves the standard energy upper bound against `H_red`.

### 5. Operator-level five-sector Gårding

`P0EFTJanusProgramPCandidateAFiveSectorProductOperatorOffDiagonalGarding4D.lean`

`P0EFTJanusProgramPFiniteProjectionOperatorOffDiagonalGarding4D.lean`

`P0EFTJanusProgramPGlobalCandidateAReducedPrincipalOperator4D.lean`

* constructs the Riesz operator `A_red` of the genuine reduced principal form;
* defines

  ```text
  A_diag = Σ_s P_s A_red P_s
  A_off  = A_red - A_diag;
  ```

* reduces principal Gårding to five diagonal lower bounds and one norm estimate
  for `A_off`;
* proves that the represented off-diagonal form norm is bounded by `‖A_off‖`.

### 6. Canonical H12 and H14 closure

`P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalOperatorGap4D.lean`

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D.lean`

* combines the five principal block estimates, the single operator remainder
  estimate and the canonical H11 constant;
* produces the actual-kernel gap, closed range, Fredholmness, index zero and the
  reduced Green operator;
* keeps exact action generators logically independent from coercivity.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelClosure4D.lean`

* adds exactly one finite-dimensional datum: a basis of the actual kernel whose
  ambient vectors are the action generators;
* constructs the complete named kernel model;
* proves exact reconstruction of every zero mode;
* proves

  ```text
  finrank ker H
    = number of named generators
    = sum of the five sector multiplicities.
  ```

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14Certificate4D.lean`

* packages the named kernel, H12 certificate, real resolvent and quantitative
  stability under all reduced self-adjoint perturbations smaller than the gap.

### 7. Exact reduced exponential and relative heat

`P0EFTJanusProgramPSelfAdjointKernelComplementExponential4D.lean`

`P0EFTJanusProgramPGlobalCandidateAActualKernelExponential4D.lean`

* constructs `exp (-t H_red)` directly on `(ker H)ᗮ`;
* proves the group law, invertibility, self-adjointness and commutation.

`P0EFTJanusProgramPSelfAdjointKernelComplementExponentialCompactNoGo4D.lean`

* proves that compactness of this bounded invertible exponential forces the
  actual complement to be finite-dimensional.

`P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D.lean`

`P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D.lean`

`P0EFTJanusProgramPGlobalCandidateAActualKernelRelativeTrace4D.lean`

* replaces invalid absolute heat compactness by

  ```text
  exp (-t H_red) - exp (-t H_ref);
  ```

* obtains compactness and a summable scalar trace from one summable rank-one
  expansion.

### 8. Presentation-independent actual-kernel trace

`P0EFTJanusProgramPSelfAdjointKernelComplementIntrinsicRelativeTrace4D.lean`

`P0EFTJanusProgramPGlobalCandidateAActualKernelIntrinsicRelativeTrace4D.lean`

* strengthens each positive-time relative heat difference by an
  `IntrinsicNuclearTraceData` certificate;
* retains one expansion only as a witness;
* proves that every certified summable rank-one presentation computes the same
  scalar;
* defines the canonical relative trace used by all subsequent regularization.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicTraceFrontier4D.lean`

* attaches this intrinsic trace to the preferred H14 closure;
* recovers the earlier presentation-level spectral frontier by forgetting only
  the uniqueness theorem;
* keeps H14, the exponential and relative compactness on the same actual-kernel
  operator.

### 9. Finite part and honest Mellin/zeta continuation

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicMellinZetaFrontier4D.lean`

* applies finite-part renormalization to the intrinsic trace;
* requires a Gamma-normalized Mellin formula on a right half-plane;
* continues the same zeta function differentiably to zero;
* obtains a nonzero complex determinant whose norm is the positive finite-part
  determinant;
* provides a definitionally faithful adapter to the earlier scalar frontier.

### 10. Anchored zeta family, metric and connection

`P0EFTJanusProgramPRelativeHeatMellinZetaAnchoredFamily4D.lean`

* forces the parameter-zero heat trace, finite-part logarithm, zeta function
  and zeta derivative of a family to equal one scalar basepoint;
* proves equality of the family determinant and finite-part magnitude at that
  basepoint.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicMellinZetaFamily4D.lean`

* specializes that anchor to the intrinsic Candidate-A determinant;
* derives metric variation and the unitary phase without a second scalar
  determinant.

### 11. Quillen circle, atlas and holonomy

`P0EFTJanusProgramPRelativeHeatMellinZetaQuillenAtlas4D.lean`

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenAtlas4D.lean`

* uses the same anchored Mellin family for the circle connection and the
  selected chart of a multi-chart determinant-line atlas;
* derives local parallelism, the Čech cocycle, gauge covariance, metric
  variation, endpoint clutching and phase unitarity.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenMetricAnchor4D.lean`

* places the preferred complex determinant in the periodic circle determinant
  fiber;
* proves that its Quillen norm square is the square of the intrinsic finite-part
  magnitude.

`P0EFTJanusProgramPRelativeZetaCircleHolonomyPhase4D.lean`

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorQuillenHolonomy4D.lean`

* proves that the endpoint determinant ratio is the large-gauge clutching
  multiplier;
* proves that the ratio of normalized zeta phases is the closed unitary Quillen
  holonomy.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorIntrinsicQuillenClosure4D.lean`

* exports one terminal certificate containing the intrinsic trace, H14,
  determinant, metric, connection, atlas, clutching and holonomy;
* reuses compatibility façades only by forgetting proofs, never by changing the
  underlying operator or determinant.

## Irreducible mathematical proofs still required

The implemented structures isolate the remaining content rather than
postulating downstream consequences separately.

### A. Physical five-sector completion

Construct the single completion isometry and prove its refinement of the
diagonal bulk factor agrees with the actual smooth-core fields.

### B. Exact action generators

Write the finite diffeomorphism, Abelian, SpinC, LL and boundary/BV generators
and prove local invariance of the genuine augmented Candidate-A action.

### C. Actual-Hessian sector invariance

Prove the generated projectors commute with the actual augmented Hessian. The
implemented interface reduces this to the exact projected off-diagonal block
identities.

### D. Principal operator estimates

On the automatically inherited actual-kernel-complement sectors, prove:

```text
c_s ‖P_s x‖² ≤ ⟪A_red P_s x, P_s x⟫
```

for all five sectors, and prove

```text
‖A_red - Σ_s P_s A_red P_s‖ < c_floor.
```

### E. Canonical H11 smallness

Prove that the explicit constant generated by the typed dense-core-to-chart
bound satisfies

```text
C_H11 < c_floor - ‖A_off‖.
```

### F. Named-kernel completeness

Identify the action generators with a basis of the actual kernel. Once this is
proved, all reconstruction and sector multiplicity statements are automatic.

### G. Intrinsic relative trace theorem

For every positive time, construct a summable rank-one presentation of the
actual-minus-reference heat difference and prove presentation independence.
This is now the only trace-uniqueness input; no separate scalar trace is
accepted downstream.

### H. Uniform finite-part and Mellin analysis

Prove the short-time subtraction, long-time integrability, right-half-plane
Mellin integrability, continuation to zero and differentiability in the family.

### I. Quillen/Bismut--Freed comparison

Identify the family zeta connection coefficient with the geometric
Bismut--Freed/circle one-form and prove endpoint clutching and multi-chart
spectral-cut coherence for the actual Candidate-A family.

## Logical endpoint

After A--F, the implemented gates provide the full preferred H10--H14 package:

```text
same genuine action
→ actual Hessian
→ exact named kernel
→ one inherited kernel-complement decomposition
→ positive reduced gap
→ closed range and Fredholm index zero
→ reduced Green and resolvent
→ quantitative perturbative stability.
```

After G--I, the same actual-kernel route continues without changing operator or
completion:

```text
intrinsic relative heat trace
→ finite-part determinant
→ Mellin/zeta determinant
→ differentiable determinant family
→ Quillen metric and compatible connection
→ determinant-line atlas and clutching
→ unitary zeta phase = closed Quillen holonomy.
```
