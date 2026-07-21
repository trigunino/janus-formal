import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCoerciveCompactResolvent4D

/-!
# Eigenvalue correspondence between the closed operator and its resolvent

For a bounded resolvent `R_lambda = (A - lambda)⁻¹`, an operator eigenvalue
`nu ≠ lambda` corresponds to the nonzero resolvent eigenvalue
`(nu - lambda)⁻¹`.  Conversely, every nonzero resolvent eigenvalue `mu`
produces the operator eigenvalue `lambda + mu⁻¹`.

The statements below are formulated directly for the genuine closed separated
operator and its ambient resolvent.  They retain the actual domain vector and
its ambient inclusion, so later multiplicity and mode-completeness arguments can
reuse the same witnesses without rebuilding the graph realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarResolventEigenvalueCorrespondence4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D
open P0EFTJanusMappingTorusScalarClosedResolvent4D
open P0EFTJanusMappingTorusScalarCompactResolventSpectrum4D
open P0EFTJanusMappingTorusScalarCoerciveCompactResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Eigenspace of the unbounded closed separated operator, represented inside
its actual operator domain. -/
def canonicalScalarClosedOperatorEigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b eigenvalue : Real) :
    Submodule Real
      (canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b) :=
  LinearMap.ker
    (canonicalScalarClosedSeparatedDomainOperator
        data hClosable traceBound a b -
      eigenvalue • canonicalScalarClosedSeparatedDomainInclusion
        data hClosable traceBound a b)

@[simp] theorem mem_canonicalScalarClosedOperatorEigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b eigenvalue : Real)
    (field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b) :
    field ∈ canonicalScalarClosedOperatorEigenspace
        data hClosable traceBound a b eigenvalue ↔
      canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b field =
        eigenvalue • canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field := by
  rw [canonicalScalarClosedOperatorEigenspace,
    LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    LinearMap.smul_apply]

/-- Nonzero eigenvalue witness for the closed separated operator. -/
def CanonicalScalarClosedHasEigenvalue
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b eigenvalue : Real) : Prop :=
  ∃ field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b,
    field ≠ 0 ∧
      canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b field =
        eigenvalue • canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field

/-- Nonzero eigenvalue witness for the bounded ambient resolvent. -/
def CanonicalScalarAmbientResolventHasEigenvalue
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter resolventEigenvalue : Real)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter) : Prop :=
  ∃ vector : Ambient, vector ≠ 0 ∧
    CanonicalScalarClosedBoundedResolventAt.ambientResolvent
        data hClosable traceBound a b spectralParameter bounded vector =
      resolventEigenvalue • vector

/-- Operator eigenfields give ambient resolvent eigenvectors. -/
theorem canonicalScalarClosedOperator_eigenfield_to_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - spectralParameter ≠ 0)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter)
    (field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b)
    (hField :
      canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b field =
        operatorEigenvalue • canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field) :
    CanonicalScalarClosedBoundedResolventAt.ambientResolvent
        data hClosable traceBound a b spectralParameter bounded
        (canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field) =
      (operatorEigenvalue - spectralParameter)⁻¹ •
        canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field := by
  let difference := operatorEigenvalue - spectralParameter
  have hDifference' : difference ≠ 0 := hDifference
  have hShiftedField :
      canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter field =
        difference • canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field := by
    rw [canonicalScalarClosedSeparatedShiftedOperator_apply, hField]
    dsimp [difference]
    module
  have hTarget :
      canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter
          (difference⁻¹ • field) =
        canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field := by
    rw [map_smul, hShiftedField, smul_smul]
    simp [hDifference']
  have hDomain :
      bounded.resolvent
          (canonicalScalarClosedSeparatedDomainInclusion
            data hClosable traceBound a b field) =
        difference⁻¹ • field := by
    apply (bounded.resolventPoint
      data hClosable traceBound a b spectralParameter).1
    rw [bounded.left_inverse, hTarget]
  change canonicalScalarClosedSeparatedDomainInclusion
      data hClosable traceBound a b
      (bounded.resolvent
        (canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field)) =
    difference⁻¹ • canonicalScalarClosedSeparatedDomainInclusion
      data hClosable traceBound a b field
  rw [hDomain, map_smul]

/-- Every nonzero ambient resolvent eigenvalue gives an eigenfield of the
original closed operator. -/
theorem canonicalScalarClosedResolvent_eigenvector_to_operator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter resolventEigenvalue : Real)
    (hResolventEigenvalue : resolventEigenvalue ≠ 0)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter)
    (vector : Ambient)
    (hVector :
      CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter bounded vector =
        resolventEigenvalue • vector) :
    ∃ field : canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b,
      canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field = vector ∧
        canonicalScalarClosedSeparatedDomainOperator
            data hClosable traceBound a b field =
          (spectralParameter + resolventEigenvalue⁻¹) • vector := by
  let field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b :=
    resolventEigenvalue⁻¹ • bounded.resolvent vector
  have hTransfer := canonicalScalarClosedResolvent_eigenvector_transfer
    data hClosable traceBound a b spectralParameter bounded
      resolventEigenvalue hResolventEigenvalue vector hVector
  exact ⟨field, hTransfer.1, hTransfer.2⟩

/-- Exact nonzero eigenvalue correspondence between the closed operator and one
bounded ambient resolvent. -/
theorem canonicalScalarClosedHasEigenvalue_iff_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - spectralParameter ≠ 0)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter) :
    CanonicalScalarClosedHasEigenvalue
        data hClosable traceBound a b operatorEigenvalue ↔
      CanonicalScalarAmbientResolventHasEigenvalue
        data hClosable traceBound a b spectralParameter
          (operatorEigenvalue - spectralParameter)⁻¹ bounded := by
  constructor
  · rintro ⟨field, hFieldNonzero, hField⟩
    refine ⟨canonicalScalarClosedSeparatedDomainInclusion
      data hClosable traceBound a b field, ?_, ?_⟩
    · intro hZero
      apply hFieldNonzero
      exact canonicalScalarClosedSeparatedDomainInclusion_injective
        data hClosable traceBound a b hZero
    · exact canonicalScalarClosedOperator_eigenfield_to_resolvent
        data hClosable traceBound a b spectralParameter operatorEigenvalue
          hDifference bounded field hField
  · rintro ⟨vector, hVectorNonzero, hVector⟩
    have hInverseNonzero :
        (operatorEigenvalue - spectralParameter)⁻¹ ≠ 0 :=
      inv_ne_zero hDifference
    obtain ⟨field, hInclusion, hOperator⟩ :=
      canonicalScalarClosedResolvent_eigenvector_to_operator
        data hClosable traceBound a b spectralParameter
          (operatorEigenvalue - spectralParameter)⁻¹
          hInverseNonzero bounded vector hVector
    refine ⟨field, ?_, ?_⟩
    · intro hFieldZero
      apply hVectorNonzero
      rw [← hInclusion, hFieldZero]
      simp
    · have hCoefficient :
          spectralParameter +
              ((operatorEigenvalue - spectralParameter)⁻¹)⁻¹ =
            operatorEigenvalue := by
        rw [inv_inv]
        ring
      rw [hCoefficient, ← hInclusion] at hOperator
      exact hOperator

/-- Compact-resolvent specialization of the eigenvalue correspondence. -/
theorem canonicalScalarClosedCompactHasEigenvalue_iff_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter operatorEigenvalue : Real)
    (hDifference : operatorEigenvalue - spectralParameter ≠ 0)
    (compact : CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter) :
    CanonicalScalarClosedHasEigenvalue
        data hClosable traceBound a b operatorEigenvalue ↔
      CanonicalScalarAmbientResolventHasEigenvalue
        data hClosable traceBound a b spectralParameter
          (operatorEigenvalue - spectralParameter)⁻¹ compact.bounded :=
  canonicalScalarClosedHasEigenvalue_iff_resolvent
    data hClosable traceBound a b spectralParameter operatorEigenvalue
      hDifference compact.bounded

end
end P0EFTJanusMappingTorusScalarResolventEigenvalueCorrespondence4D
end JanusFormal
