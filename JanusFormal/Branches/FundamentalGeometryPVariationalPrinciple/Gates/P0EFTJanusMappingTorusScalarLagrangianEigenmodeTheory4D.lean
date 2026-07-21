import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianResolventIdentity4D

/-!
# Eigenmode theory for closed Lagrangian scalar realizations

This file formulates eigenspaces directly in the genuine closed operator domain.
It proves orthogonality of distinct operator eigenvalues and identifies every
operator eigenspace away from a reference resolvent parameter with the
corresponding nonzero eigenspace of the bounded ambient resolvent.

For compact resolvent, the identification gives finite multiplicity of every
operator eigenvalue away from the reference point.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianResolventIdentity4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Eigenspace of the genuine closed Lagrangian operator. -/
def canonicalScalarClosedLagrangianOperatorEigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real) :
    Submodule Real
      (canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition) :=
  LinearMap.ker
    (canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition -
      eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)

@[simp] theorem mem_canonicalScalarClosedLagrangianOperatorEigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    field ∈ canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition eigenvalue ↔
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field := by
  rw [canonicalScalarClosedLagrangianOperatorEigenspace,
    LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    LinearMap.smul_apply]

/-- The ambient inclusion of an arbitrary Lagrangian operator domain is
injective. -/
theorem canonicalScalarClosedLagrangianDomainInclusion_injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Function.Injective
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition) := by
  intro first second hEqual
  apply Subtype.ext
  apply Subtype.ext
  exact hEqual

/-- Distinct eigenvalues of a symmetric Lagrangian realization have orthogonal
ambient eigenfields. -/
theorem canonicalScalarClosedLagrangian_eigenfields_orthogonal
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (first second : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition)
    (hFirst :
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition first =
        firstEigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition first)
    (hSecond :
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition second =
        secondEigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition second) :
    inner Real
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition first)
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition second) = 0 := by
  have hSymmetric := canonicalScalarClosedLagrangianDomainOperator_symmetric
    data hClosable traceBound condition first second
  rw [hFirst, hSecond,
    real_inner_smul_left, real_inner_smul_right] at hSymmetric
  have hMultiple :
      (firstEigenvalue - secondEigenvalue) *
        inner Real
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition first)
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition second) = 0 := by
    linarith
  exact (mul_eq_zero.mp hMultiple).resolve_left
    (sub_ne_zero.mpr hDistinct)

/-- Submodule-level orthogonality of distinct closed-operator eigenspaces. -/
theorem canonicalScalarClosedLagrangianOperatorEigenspaces_isOrtho
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue) :
    ∀ first : canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition firstEigenvalue,
      ∀ second : canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition secondEigenvalue,
      inner Real
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition first.1)
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition second.1) = 0 := by
  intro first second
  exact canonicalScalarClosedLagrangian_eigenfields_orthogonal
    data hClosable traceBound condition firstEigenvalue secondEigenvalue
      hDistinct first.1 second.1
      ((mem_canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition firstEigenvalue first.1).1 first.2)
      ((mem_canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition secondEigenvalue second.1).1 second.2)

/-- Operator eigenfields give eigenvectors of a bounded ambient resolvent. -/
theorem canonicalScalarClosedLagrangian_operatorEigenfield_to_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - referenceParameter ≠ 0)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition)
    (hField :
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        operatorEigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field) :
    bounded.ambientResolvent
        data hClosable traceBound condition referenceParameter
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field) =
      (operatorEigenvalue - referenceParameter)⁻¹ •
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field := by
  let difference := operatorEigenvalue - referenceParameter
  have hShifted :
      canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition referenceParameter field =
        difference • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field := by
    rw [canonicalScalarClosedLagrangianShiftedOperator_apply, hField]
    dsimp [difference]
    module
  have hTarget :
      canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition referenceParameter
          (difference⁻¹ • field) =
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field := by
    rw [map_smul, hShifted, smul_smul]
    simp [difference, hDifference]
  have hDomain :
      bounded.resolvent
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition field) =
        difference⁻¹ • field := by
    apply (bounded.resolventPoint
      data hClosable traceBound condition referenceParameter).1
    rw [bounded.left_inverse, hTarget]
  change canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition
      (bounded.resolvent
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field)) = _
  rw [hDomain, map_smul]

/-- Linear map from an operator eigenspace to the corresponding nonzero
resolvent eigenspace. -/
noncomputable def canonicalScalarClosedLagrangianOperatorToResolventEigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - referenceParameter ≠ 0)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter) :
    canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition operatorEigenvalue →ₗ[Real]
      LinearMap.eigenspace
        (bounded.ambientResolvent
          data hClosable traceBound condition referenceParameter).toLinearMap
        (operatorEigenvalue - referenceParameter)⁻¹ where
  toFun field :=
    ⟨canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.1,
      by
        rw [mem_eigenspace_iff]
        exact canonicalScalarClosedLagrangian_operatorEigenfield_to_resolvent
          data hClosable traceBound condition referenceParameter operatorEigenvalue
            hDifference bounded field.1
            ((mem_canonicalScalarClosedLagrangianOperatorEigenspace
              data hClosable traceBound condition operatorEigenvalue field.1).1
                field.2)⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- The operator-to-resolvent eigenspace map is injective. -/
theorem canonicalScalarClosedLagrangianOperatorToResolventEigenspace_injective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - referenceParameter ≠ 0)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter) :
    Function.Injective
      (canonicalScalarClosedLagrangianOperatorToResolventEigenspace
        data hClosable traceBound condition referenceParameter operatorEigenvalue
          hDifference bounded) := by
  intro first second hEqual
  apply Subtype.ext
  apply canonicalScalarClosedLagrangianDomainInclusion_injective
    data hClosable traceBound condition
  exact congrArg Subtype.val hEqual

/-- Every resolvent eigenvector at the reciprocal eigenvalue reconstructs an
operator eigenfield. -/
noncomputable def canonicalScalarClosedLagrangianResolventToOperatorEigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - referenceParameter ≠ 0)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter) :
    LinearMap.eigenspace
        (bounded.ambientResolvent
          data hClosable traceBound condition referenceParameter).toLinearMap
        (operatorEigenvalue - referenceParameter)⁻¹ →ₗ[Real]
      canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition operatorEigenvalue where
  toFun vector := by
    let difference := operatorEigenvalue - referenceParameter
    let field : canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :=
      difference • bounded.resolvent vector.1
    have hVector :
        bounded.ambientResolvent
            data hClosable traceBound condition referenceParameter vector.1 =
          difference⁻¹ • vector.1 := by
      exact (mem_eigenspace_iff.mp vector.2)
    have hTransfer := canonicalScalarClosedLagrangianResolvent_eigenvector_transfer
      data hClosable traceBound condition referenceParameter bounded
        difference⁻¹ (inv_ne_zero hDifference) vector.1 hVector
    refine ⟨field, ?_⟩
    apply (mem_canonicalScalarClosedLagrangianOperatorEigenspace
      data hClosable traceBound condition operatorEigenvalue field).2
    have hCoefficient :
        referenceParameter + (difference⁻¹)⁻¹ = operatorEigenvalue := by
      rw [inv_inv]
      dsimp [difference]
      ring
    simpa [field, hCoefficient] using hTransfer.2
  map_add' first second := by
    apply Subtype.ext
    simp [map_add]
  map_smul' scalar field := by
    apply Subtype.ext
    simp [map_smul]

/-- Exact linear equivalence between operator and reciprocal resolvent
eigenspaces. -/
noncomputable def canonicalScalarClosedLagrangianOperatorResolventEigenspaceEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - referenceParameter ≠ 0)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter) :
    canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition operatorEigenvalue ≃ₗ[Real]
      LinearMap.eigenspace
        (bounded.ambientResolvent
          data hClosable traceBound condition referenceParameter).toLinearMap
        (operatorEigenvalue - referenceParameter)⁻¹ where
  toFun := canonicalScalarClosedLagrangianOperatorToResolventEigenspace
    data hClosable traceBound condition referenceParameter operatorEigenvalue
      hDifference bounded
  invFun := canonicalScalarClosedLagrangianResolventToOperatorEigenspace
    data hClosable traceBound condition referenceParameter operatorEigenvalue
      hDifference bounded
  left_inv := by
    intro field
    apply Subtype.ext
    apply canonicalScalarClosedLagrangianDomainInclusion_injective
      data hClosable traceBound condition
    let difference := operatorEigenvalue - referenceParameter
    have hVector := canonicalScalarClosedLagrangian_operatorEigenfield_to_resolvent
      data hClosable traceBound condition referenceParameter operatorEigenvalue
        hDifference bounded field.1
        ((mem_canonicalScalarClosedLagrangianOperatorEigenspace
          data hClosable traceBound condition operatorEigenvalue field.1).1 field.2)
    change canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (difference • bounded.resolvent
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition field.1)) =
      canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.1
    rw [map_smul]
    change difference •
        (bounded.ambientResolvent
          data hClosable traceBound condition referenceParameter
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition field.1)) = _
    rw [hVector, smul_smul]
    simp [difference, hDifference]
  right_inv := by
    intro vector
    apply Subtype.ext
    let difference := operatorEigenvalue - referenceParameter
    have hVector :
        bounded.ambientResolvent
            data hClosable traceBound condition referenceParameter vector.1 =
          difference⁻¹ • vector.1 :=
      mem_eigenspace_iff.mp vector.2
    have hTransfer := canonicalScalarClosedLagrangianResolvent_eigenvector_transfer
      data hClosable traceBound condition referenceParameter bounded
        difference⁻¹ (inv_ne_zero hDifference) vector.1 hVector
    change canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (difference • bounded.resolvent vector.1) = vector.1
    simpa [difference] using hTransfer.1
  map_add' := by
    intro first second
    exact (canonicalScalarClosedLagrangianOperatorToResolventEigenspace
      data hClosable traceBound condition referenceParameter operatorEigenvalue
        hDifference bounded).map_add first second
  map_smul' := by
    intro scalar field
    exact (canonicalScalarClosedLagrangianOperatorToResolventEigenspace
      data hClosable traceBound condition referenceParameter operatorEigenvalue
        hDifference bounded).map_smul scalar field

/-- Compact resolvent gives finite multiplicity of every operator eigenvalue
away from the reference resolvent parameter. -/
theorem canonicalScalarClosedLagrangianOperatorEigenspace_finiteDimensional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - referenceParameter ≠ 0)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition operatorEigenvalue) := by
  letI : FiniteDimensional Real
      (LinearMap.eigenspace
        (compact.bounded.ambientResolvent
          data hClosable traceBound condition referenceParameter).toLinearMap
        (operatorEigenvalue - referenceParameter)⁻¹) :=
    compact.finiteDimensional_eigenspace
      data hClosable traceBound condition referenceParameter
        (operatorEigenvalue - referenceParameter)⁻¹
        (inv_ne_zero hDifference)
  exact FiniteDimensional.of_injective
    (canonicalScalarClosedLagrangianOperatorToResolventEigenspace
      data hClosable traceBound condition referenceParameter operatorEigenvalue
        hDifference compact.bounded)
    (canonicalScalarClosedLagrangianOperatorToResolventEigenspace_injective
      data hClosable traceBound condition referenceParameter operatorEigenvalue
        hDifference compact.bounded)

/-- Eigenmode certificate: orthogonality and finite multiplicity under compact
resolvent. -/
theorem canonicalScalarLagrangianEigenmodeTheory_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter firstEigenvalue secondEigenvalue : Real)
    (hFirstReference : firstEigenvalue - referenceParameter ≠ 0)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    FiniteDimensional Real
        (canonicalScalarClosedLagrangianOperatorEigenspace
          data hClosable traceBound condition firstEigenvalue) ∧
      (∀ first : canonicalScalarClosedLagrangianOperatorEigenspace
          data hClosable traceBound condition firstEigenvalue,
        ∀ second : canonicalScalarClosedLagrangianOperatorEigenspace
          data hClosable traceBound condition secondEigenvalue,
        inner Real
            (canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition first.1)
            (canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition second.1) = 0) :=
  ⟨canonicalScalarClosedLagrangianOperatorEigenspace_finiteDimensional
      data hClosable traceBound condition referenceParameter firstEigenvalue
        hFirstReference compact,
    canonicalScalarClosedLagrangianOperatorEigenspaces_isOrtho
      data hClosable traceBound condition firstEigenvalue secondEigenvalue
        hDistinct⟩

end
end P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
end JanusFormal
