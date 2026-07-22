import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

/-!
# Fredholm alternative directly on a completed scalar boundary triple

Fix a compact direct resolvent at `rho`.  For every other real parameter
`lambda`, the exact factorization

`A - lambda = (I - (lambda-rho) R_rho) (A-rho)`

reduces the unbounded problem to the compact Fredholm alternative on the ambient
Hilbert space.  Thus every `lambda != rho` is either an eigenvalue of the direct
completed Lagrangian realization or a genuine direct resolvent point.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Ambient Fredholm factor `I - (lambda-rho) R_rho`. -/
def lagrangianFredholmFactor
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : triple.LagrangianBoundedResolventAt
      condition referenceParameter) :
    Ambient →L[Real] Ambient :=
  ContinuousLinearMap.id Real Ambient -
    (targetParameter - referenceParameter) •
      referenceResolvent.ambientResolvent
        triple condition referenceParameter

@[simp] theorem lagrangianFredholmFactor_apply
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : triple.LagrangianBoundedResolventAt
      condition referenceParameter)
    (source : Ambient) :
    triple.lagrangianFredholmFactor condition referenceParameter
        targetParameter referenceResolvent source =
      source - (targetParameter - referenceParameter) •
        referenceResolvent.ambientResolvent
          triple condition referenceParameter source :=
  rfl

/-- Exact factorization of the target shift through the reference shift. -/
theorem lagrangianShifted_factorization
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : triple.LagrangianBoundedResolventAt
      condition referenceParameter)
    (field : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianFredholmFactor condition referenceParameter
        targetParameter referenceResolvent
        (triple.lagrangianShiftedOperator
          condition referenceParameter field) =
      triple.lagrangianShiftedOperator condition targetParameter field := by
  rw [triple.lagrangianFredholmFactor_apply]
  change triple.lagrangianShiftedOperator
        condition referenceParameter field -
      (targetParameter - referenceParameter) •
        triple.lagrangianInclusion condition
          (referenceResolvent.resolvent
            (triple.lagrangianShiftedOperator
              condition referenceParameter field)) = _
  rw [referenceResolvent.right_inverse]
  rw [triple.lagrangianShiftedOperator_apply,
    triple.lagrangianShiftedOperator_apply]
  module

/-- A nonzero scalar multiple of a bijective continuous linear map is
bijective. -/
theorem continuousLinearMap_smul_bijective
    (scalar : Real) (hScalar : scalar ≠ 0)
    (operator : Ambient →L[Real] Ambient)
    (hOperator : Function.Bijective operator) :
    Function.Bijective (scalar • operator) := by
  constructor
  · intro first second hEqual
    have hOperatorEqual : operator first = operator second :=
      (smul_right_injective Ambient hScalar) hEqual
    exact hOperator.1 hOperatorEqual
  · intro target
    obtain ⟨source, hSource⟩ := hOperator.2 (scalar⁻¹ • target)
    refine ⟨source, ?_⟩
    change scalar • operator source = target
    rw [hSource, smul_smul]
    simp [hScalar]

/-- An ambient resolvent point of the compact reference resolvent makes the
Fredholm factor bijective. -/
theorem lagrangianFredholmFactor_bijective_of_mem_resolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (hDifference : targetParameter - referenceParameter ≠ 0)
    (referenceResolvent : triple.LagrangianBoundedResolventAt
      condition referenceParameter)
    (hAmbientResolvent :
      (targetParameter - referenceParameter)⁻¹ ∈ resolventSet Real
        (referenceResolvent.ambientResolvent
          triple condition referenceParameter)) :
    Function.Bijective
      (triple.lagrangianFredholmFactor condition referenceParameter
        targetParameter referenceResolvent) := by
  let difference := targetParameter - referenceParameter
  let inverseDifference := difference⁻¹
  let ambientResolvent := referenceResolvent.ambientResolvent
    triple condition referenceParameter
  have hCoreUnit : IsUnit
      (inverseDifference • (1 : Ambient →L[Real] Ambient) - ambientResolvent) := by
    simpa [inverseDifference, ambientResolvent, resolventSet,
      Algebra.algebraMap_eq_smul_one] using hAmbientResolvent
  have hCoreBijective : Function.Bijective
      (inverseDifference • (1 : Ambient →L[Real] Ambient) - ambientResolvent) := by
    rw [← ContinuousLinearMap.isUnit_iff_bijective]
    exact hCoreUnit
  have hScaledBijective : Function.Bijective
      (difference •
        (inverseDifference • (1 : Ambient →L[Real] Ambient) -
          ambientResolvent)) :=
    continuousLinearMap_smul_bijective difference hDifference _ hCoreBijective
  have hFactorEquality :
      triple.lagrangianFredholmFactor condition referenceParameter
          targetParameter referenceResolvent =
        difference •
          (inverseDifference • (1 : Ambient →L[Real] Ambient) -
            ambientResolvent) := by
    ext source
    dsimp [lagrangianFredholmFactor, difference,
      inverseDifference, ambientResolvent]
    rw [smul_sub, smul_smul]
    rw [mul_inv_cancel₀ hDifference, one_smul]
    rfl
  rw [hFactorEquality]
  exact hScaledBijective

/-- Bijectivity of the Fredholm factor implies a direct target resolvent point. -/
theorem lagrangianResolventPoint_of_factor_bijective
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : triple.LagrangianBoundedResolventAt
      condition referenceParameter)
    (hFactor : Function.Bijective
      (triple.lagrangianFredholmFactor condition referenceParameter
        targetParameter referenceResolvent)) :
    triple.LagrangianResolventPoint condition targetParameter := by
  let referenceShift := triple.lagrangianShiftedOperator
    condition referenceParameter
  let targetShift := triple.lagrangianShiftedOperator
    condition targetParameter
  let factor := triple.lagrangianFredholmFactor condition
    referenceParameter targetParameter referenceResolvent
  have hReference := referenceResolvent.resolventPoint
    triple condition referenceParameter
  constructor
  · intro first second hEqual
    have hFactorEqual : factor (referenceShift first) =
        factor (referenceShift second) := by
      calc
        factor (referenceShift first) = targetShift first :=
          triple.lagrangianShifted_factorization condition
            referenceParameter targetParameter referenceResolvent first
        _ = targetShift second := hEqual
        _ = factor (referenceShift second) :=
          (triple.lagrangianShifted_factorization condition
            referenceParameter targetParameter referenceResolvent second).symm
    exact hReference.1 (hFactor.1 hFactorEqual)
  · intro target
    obtain ⟨middle, hMiddle⟩ := hFactor.2 target
    obtain ⟨field, hField⟩ := hReference.2 middle
    refine ⟨field, ?_⟩
    calc
      targetShift field = factor (referenceShift field) :=
        (triple.lagrangianShifted_factorization condition
          referenceParameter targetParameter referenceResolvent field).symm
      _ = factor middle := by rw [hField]
      _ = target := hMiddle

/-- Existence of a nonzero direct operator eigenfield. -/
def LagrangianHasEigenvalue
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real) : Prop :=
  ∃ field : triple.lagrangianDomainSubmodule condition,
    field ≠ 0 ∧
      triple.lagrangianOperator condition field =
        eigenvalue • triple.lagrangianInclusion condition field

/-- A nonzero ambient resolvent eigenvector reconstructs a direct operator
eigenfield. -/
theorem lagrangianResolvent_eigenvector_transfer
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition referenceParameter)
    (resolventEigenvalue : Real) (hEigenvalue : resolventEigenvalue ≠ 0)
    (vector : Ambient)
    (hVector : bounded.ambientResolvent triple condition referenceParameter vector =
      resolventEigenvalue • vector) :
    let field : triple.lagrangianDomainSubmodule condition :=
      resolventEigenvalue⁻¹ • bounded.resolvent vector
    triple.lagrangianInclusion condition field = vector ∧
      triple.lagrangianOperator condition field =
        (referenceParameter + resolventEigenvalue⁻¹) • vector := by
  let field : triple.lagrangianDomainSubmodule condition :=
    resolventEigenvalue⁻¹ • bounded.resolvent vector
  have hInclusion : triple.lagrangianInclusion condition field = vector := by
    dsimp [field]
    rw [map_smul]
    change resolventEigenvalue⁻¹ •
        bounded.ambientResolvent triple condition referenceParameter vector = vector
    rw [hVector, smul_smul]
    simp [hEigenvalue]
  have hShifted :
      triple.lagrangianShiftedOperator condition referenceParameter field =
        resolventEigenvalue⁻¹ • vector := by
    change triple.lagrangianShiftedOperator condition referenceParameter
      (resolventEigenvalue⁻¹ • bounded.resolvent vector) = _
    rw [map_smul, bounded.left_inverse]
  refine ⟨hInclusion, ?_⟩
  have hExpanded := triple.lagrangianShiftedOperator_apply
    condition referenceParameter field
  rw [hShifted, hInclusion] at hExpanded
  have hAdded := congrArg
    (fun value => value + referenceParameter • vector) hExpanded
  simpa [add_smul, add_assoc, add_comm, add_left_comm] using hAdded.symm

/-- Direct Fredholm alternative for the unbounded Lagrangian realization. -/
theorem lagrangian_fredholmAlternative
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (hDifference : targetParameter - referenceParameter ≠ 0)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    triple.LagrangianHasEigenvalue condition targetParameter ∨
      triple.LagrangianResolventPoint condition targetParameter := by
  let resolventEigenvalue := (targetParameter - referenceParameter)⁻¹
  have hResolventEigenvalue : resolventEigenvalue ≠ 0 :=
    inv_ne_zero hDifference
  rcases compact.fredholmAlternative triple condition referenceParameter
      resolventEigenvalue hResolventEigenvalue with hEigen | hResolvent
  · left
    obtain ⟨vector, hVector⟩ := hEigen.exists_hasEigenvector
    have hVectorEquation :
        compact.bounded.ambientResolvent triple condition referenceParameter vector =
          resolventEigenvalue • vector :=
      hVector.apply_eq_smul
    have hTransfer := triple.lagrangianResolvent_eigenvector_transfer
      condition referenceParameter compact.bounded
      resolventEigenvalue hResolventEigenvalue vector hVectorEquation
    let field : triple.lagrangianDomainSubmodule condition :=
      resolventEigenvalue⁻¹ • compact.bounded.resolvent vector
    refine ⟨field, ?_, ?_⟩
    · intro hField
      apply hVector.2
      dsimp [field] at hField
      have hResolventZero : compact.bounded.resolvent vector = 0 := by
        apply (smul_right_injective _ (inv_ne_zero hResolventEigenvalue))
        simpa using hField
      rw [← compact.bounded.left_inverse vector, hResolventZero, map_zero]
    · have hCoefficient :
          referenceParameter + resolventEigenvalue⁻¹ = targetParameter := by
        dsimp [resolventEigenvalue]
        rw [inv_inv]
        ring
      dsimp [field] at hTransfer ⊢
      rw [hTransfer.1]
      simpa [hCoefficient] using hTransfer.2
  · right
    apply triple.lagrangianResolventPoint_of_factor_bijective
      condition referenceParameter targetParameter compact.bounded
    exact triple.lagrangianFredholmFactor_bijective_of_mem_resolvent
      condition referenceParameter targetParameter hDifference
      compact.bounded hResolvent

/-- Away from the reference point, failure of the direct resolvent condition is
exactly existence of a nonzero eigenfield. -/
theorem not_resolvent_iff_hasEigenvalue
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (hDifference : targetParameter - referenceParameter ≠ 0)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    ¬ triple.LagrangianResolventPoint condition targetParameter ↔
      triple.LagrangianHasEigenvalue condition targetParameter := by
  constructor
  · intro hNotResolvent
    rcases triple.lagrangian_fredholmAlternative condition referenceParameter
        targetParameter hDifference compact with hEigen | hResolvent
    · exact hEigen
    · exact False.elim (hNotResolvent hResolvent)
  · rintro ⟨field, hFieldNonzero, hField⟩ hResolvent
    apply hFieldNonzero
    exact hResolvent.1 (by
      rw [triple.lagrangianShiftedOperator_apply, hField]
      simpa using sub_self
        (targetParameter • triple.lagrangianInclusion condition field))

/-- Direct discrete-spectrum certificate. -/
theorem directFredholmAlternative_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    ∀ targetParameter : Real,
      targetParameter ≠ referenceParameter →
        triple.LagrangianHasEigenvalue condition targetParameter ∨
          triple.LagrangianResolventPoint condition targetParameter := by
  intro targetParameter hTarget
  exact triple.lagrangian_fredholmAlternative condition referenceParameter
    targetParameter (sub_ne_zero.mpr hTarget) compact

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
end JanusFormal
