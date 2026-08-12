# HESSIAN-GLOBAL-01 — preferred five-sector actual-kernel route

## Status

This document records the implementation frontier on PR #60.  It is an
architectural and mathematical dependency map; it does **not** claim that the
current branch elaborates successfully in Lean.

The preferred route now uses one physical Hilbert decomposition throughout:

```text
E ≃ M × A × S × L × B
```

with the five factors

1. metric/diffeomorphism,
2. Abelian gauge,
3. primitive SpinC matter,
4. longitudinal/LL,
5. boundary/finite BV.

No second decomposition is introduced on the kernel complement.

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

### 7. Honest reduced spectral frontier

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

* replaces invalid absolute heat compactness by a relative difference
  `exp (-t H_red) - exp (-t H_ref)`;
* obtains compactness and a summable scalar trace from one summable rank-one
  expansion.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralFrontier4D.lean`

* attaches that relative trace to the H14 closure.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMellinZetaFrontier4D.lean`

* attaches finite-part renormalization and an honest right-half-plane Mellin
  representation;
* obtains a nonzero complex relative zeta determinant with the prescribed
  finite-part magnitude.

## Irreducible mathematical proofs still required

The current preferred structures isolate the remaining content rather than
postulating downstream consequences separately.

### A. Physical five-sector completion

Construct the single completion isometry and prove its three-way refinement of
the diagonal bulk factor agrees with the actual smooth-core fields.

### B. Exact action generators

Write the finite diffeomorphism, Abelian, SpinC, LL and boundary/BV generators
and prove local invariance of the genuine augmented Candidate-A action.

### C. Actual-Hessian sector invariance

Prove the generated projectors commute with the actual augmented Hessian.  The
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

Identify the action generators with a basis of the actual kernel.  Once this is
proved, all reconstruction and sector multiplicity statements are automatic.

### G. Relative spectral analysis

For determinant/Quillen outputs, prove a representation-independent relative
trace, short-time subtraction, long-time integrability and Mellin continuation.
The bounded Riesz exponential itself must not be declared nuclear in an
infinite-dimensional realization.

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

After G, the same actual-kernel route reaches the relative zeta determinant and
is ready for the existing determinant-line/Quillen family coherence layer.
