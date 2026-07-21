import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D

/-!
# Fredholm alternative for the closed scalar operator

Fix a compact bounded resolvent at a real reference parameter `rho`.  For every
other real parameter `lambda`, the factorization

`A - lambda = (I - (lambda-rho) R_rho) (A-rho)`

reduces invertibility of the unbounded shifted operator to the Fredholm
alternative for the compact ambient resolvent.  Consequently every
`lambda ≠ rho` is either an operator eigenvalue or a genuine resolvent point.

This is the central discrete-spectrum alternative for every closed Lagrangian
scalar boundary realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Fredholm factor `I - (lambda-rho) R_rho` on the ambient Hilbert space. -/
def canonicalScalarClosedLagrangianFredholmFactor
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter) :
    Ambient →L[Real] Ambient :=
  ContinuousLinearMap.id Real Ambient -
    (targetParameter - referenceParameter) •
      referenceResolvent.ambientResolvent
        data hClosable traceBound condition referenceParameter

@[simp] theorem canonicalScalarClosedLagrangianFredholmFactor_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter)
    (source : Ambient) :
    canonicalScalarClosedLagrangianFredholmFactor
        data hClosable traceBound condition referenceParameter targetParameter
          referenceResolvent source =
      source - (targetParameter - referenceParameter) •
        referenceResolvent.ambientResolvent
          data hClosable traceBound condition referenceParameter source :=
  rfl

/-- Exact factorization of the target shifted operator through the reference
shift and reference ambient resolvent. -/
theorem canonicalScalarClosedLagrangianShiftedOperator_factorization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianFredholmFactor
        data hClosable traceBound condition referenceParameter targetParameter
          referenceResolvent
        (canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition referenceParameter field) =
      canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition targetParameter field := by
  rw [canonicalScalarClosedLagrangianFredholmFactor_apply]
  change canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition referenceParameter field -
      (targetParameter - referenceParameter) •
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition
          (referenceResolvent.resolvent
            (canonicalScalarClosedLagrangianShiftedOperator
              data hClosable traceBound condition referenceParameter field)) = _
  rw [referenceResolvent.right_inverse]
  rw [canonicalScalarClosedLagrangianShiftedOperator_apply,
    canonicalScalarClosedLagrangianShiftedOperator_apply]
  module

/-- Bijectivity of a nonzero scalar multiple of a bijective continuous linear
map. -/
theorem continuousLinearMap_smul_bijective
    (scalar : Real) (hScalar : scalar ≠ 0)
    (operator : Ambient →L[Real] Ambient)
    (hOperator : Function.Bijective operator) :
    Function.Bijective (scalar • operator) := by
  constructor
  · intro first second hEqual
    have hOperatorEqual : operator first = operator second := by
      exact (smul_left_cancel₀ Ambient hScalar).mp hEqual
    exact hOperator.1 hOperatorEqual
  · intro target
    obtain ⟨source, hSource⟩ := hOperator.2 (scalar⁻¹ • target)
    refine ⟨source, ?_⟩
    change scalar • operator source = target
    rw [hSource, smul_smul]
    simp [hScalar]

/-- A bounded-resolvent point of the compact ambient resolvent makes the
Fredholm factor bijective. -/
theorem canonicalScalarClosedLagrangianFredholmFactor_bijective_of_mem_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (hDifference : targetParameter - referenceParameter ≠ 0)
    (referenceResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter)
    (hAmbientResolvent :
      (targetParameter - referenceParameter)⁻¹ ∈ resolventSet Real
        (referenceResolvent.ambientResolvent
          data hClosable traceBound condition referenceParameter)) :
    Function.Bijective
      (canonicalScalarClosedLagrangianFredholmFactor
        data hClosable traceBound condition referenceParameter targetParameter
          referenceResolvent) := by
  let difference := targetParameter - referenceParameter
  let inverseDifference := difference⁻¹
  let ambientResolvent := referenceResolvent.ambientResolvent
    data hClosable traceBound condition referenceParameter
  have hCoreUnit : IsUnit
      (inverseDifference • ContinuousLinearMap.id Real Ambient - ambientResolvent) := by
    simpa [inverseDifference, ambientResolvent, resolventSet,
      Algebra.algebraMap_eq_smul_one] using hAmbientResolvent
  have hCoreBijective : Function.Bijective
      (inverseDifference • ContinuousLinearMap.id Real Ambient - ambientResolvent) := by
    rw [← ContinuousLinearMap.isUnit_iff_bijective]
    exact hCoreUnit
  have hScaledBijective : Function.Bijective
      (difference •
        (inverseDifference • ContinuousLinearMap.id Real Ambient -
          ambientResolvent)) :=
    continuousLinearMap_smul_bijective difference hDifference _ hCoreBijective
  have hFactorEquality :
      canonicalScalarClosedLagrangianFredholmFactor
          data hClosable traceBound condition referenceParameter targetParameter
            referenceResolvent =
        difference •
          (inverseDifference • ContinuousLinearMap.id Real Ambient -
            ambientResolvent) := by
    ext source
    dsimp [canonicalScalarClosedLagrangianFredholmFactor,
      difference, inverseDifference, ambientResolvent]
    simp [hDifference]
    module
  rw [hFactorEquality]
  exact hScaledBijective

/-- Bijectivity of the Fredholm factor implies that the target parameter is a
resolvent point of the closed Lagrangian operator. -/
theorem canonicalScalarClosedLagrangianResolventPoint_of_factor_bijective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (referenceResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition referenceParameter)
    (hFactor : Function.Bijective
      (canonicalScalarClosedLagrangianFredholmFactor
        data hClosable traceBound condition referenceParameter targetParameter
          referenceResolvent)) :
    CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition targetParameter := by
  let referenceShift := canonicalScalarClosedLagrangianShiftedOperator
    data hClosable traceBound condition referenceParameter
  let targetShift := canonicalScalarClosedLagrangianShiftedOperator
    data hClosable traceBound condition targetParameter
  let factor := canonicalScalarClosedLagrangianFredholmFactor
    data hClosable traceBound condition referenceParameter targetParameter
      referenceResolvent
  have hReference := referenceResolvent.resolventPoint
    data hClosable traceBound condition referenceParameter
  constructor
  · intro first second hEqual
    have hFactorEqual : factor (referenceShift first) = factor (referenceShift second) := by
      simpa [factor, referenceShift, targetShift,
        canonicalScalarClosedLagrangianShiftedOperator_factorization] using hEqual
    exact hReference.1 (hFactor.1 hFactorEqual)
  · intro target
    obtain ⟨middle, hMiddle⟩ := hFactor.2 target
    obtain ⟨field, hField⟩ := hReference.2 middle
    refine ⟨field, ?_⟩
    calc
      targetShift field = factor (referenceShift field) := by
        symm
        exact canonicalScalarClosedLagrangianShiftedOperator_factorization
          data hClosable traceBound condition referenceParameter targetParameter
            referenceResolvent field
      _ = factor middle := by rw [hField]
      _ = target := hMiddle

/-- Existence predicate for a nonzero eigenfield of the closed Lagrangian
operator. -/
def CanonicalScalarClosedLagrangianHasEigenvalue
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real) : Prop :=
  ∃ field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition,
    field ≠ 0 ∧
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field

/-- Fredholm alternative for the genuine closed Lagrangian operator: every real
parameter distinct from the compact-resolvent reference is either an eigenvalue
or a resolvent point. -/
theorem canonicalScalarClosedLagrangian_fredholmAlternative
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (hDifference : targetParameter - referenceParameter ≠ 0)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        data hClosable traceBound condition targetParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        data hClosable traceBound condition targetParameter := by
  let resolventEigenvalue := (targetParameter - referenceParameter)⁻¹
  have hResolventEigenvalue : resolventEigenvalue ≠ 0 :=
    inv_ne_zero hDifference
  rcases compact.fredholmAlternative
      data hClosable traceBound condition referenceParameter
        resolventEigenvalue hResolventEigenvalue with hEigen | hResolvent
  · left
    obtain ⟨vector, hVector⟩ := hEigen.exists_hasEigenvector
    have hVectorEquation :
        compact.bounded.ambientResolvent
            data hClosable traceBound condition referenceParameter vector =
          resolventEigenvalue • vector :=
      hVector.apply_eq_smul
    have hTransfer := canonicalScalarClosedLagrangianResolvent_eigenvector_transfer
      data hClosable traceBound condition referenceParameter compact.bounded
        resolventEigenvalue hResolventEigenvalue vector hVectorEquation
    let field : canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :=
      resolventEigenvalue⁻¹ • compact.bounded.resolvent vector
    refine ⟨field, ?_, ?_⟩
    · intro hField
      apply hVector.2
      rw [← hTransfer.1, hField]
      simp
    · have hCoefficient :
          referenceParameter + resolventEigenvalue⁻¹ = targetParameter := by
        dsimp [resolventEigenvalue]
        rw [inv_inv]
        ring
      simpa [field, hCoefficient] using hTransfer.2
  · right
    apply canonicalScalarClosedLagrangianResolventPoint_of_factor_bijective
      data hClosable traceBound condition referenceParameter targetParameter
        compact.bounded
    exact canonicalScalarClosedLagrangianFredholmFactor_bijective_of_mem_resolvent
      data hClosable traceBound condition referenceParameter targetParameter
        hDifference compact.bounded hResolvent

/-- Away from the reference point, failure of the resolvent condition is exactly
existence of a nonzero eigenfield. -/
theorem canonicalScalarClosedLagrangian_not_resolvent_iff_hasEigenvalue
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter targetParameter : Real)
    (hDifference : targetParameter - referenceParameter ≠ 0)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    ¬ CanonicalScalarClosedLagrangianResolventPoint
        data hClosable traceBound condition targetParameter ↔
      CanonicalScalarClosedLagrangianHasEigenvalue
        data hClosable traceBound condition targetParameter := by
  constructor
  · intro hNotResolvent
    rcases canonicalScalarClosedLagrangian_fredholmAlternative
        data hClosable traceBound condition referenceParameter targetParameter
          hDifference compact with hEigen | hResolvent
    · exact hEigen
    · exact False.elim (hNotResolvent hResolvent)
  · rintro ⟨field, hFieldNonzero, hField⟩ hResolvent
    apply hFieldNonzero
    exact hResolvent.1 (by
      rw [canonicalScalarClosedLagrangianShiftedOperator_apply, hField]
      module)

/-- Discrete-spectrum certificate for an arbitrary compact-resolvent Lagrangian
boundary realization. -/
theorem canonicalScalarClosedLagrangianFredholmAlternative_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    ∀ targetParameter : Real,
      targetParameter ≠ referenceParameter →
        CanonicalScalarClosedLagrangianHasEigenvalue
            data hClosable traceBound condition targetParameter ∨
          CanonicalScalarClosedLagrangianResolventPoint
            data hClosable traceBound condition targetParameter := by
  intro targetParameter hTarget
  apply canonicalScalarClosedLagrangian_fredholmAlternative
    data hClosable traceBound condition referenceParameter targetParameter
      (sub_ne_zero.mpr hTarget) compact

end
end P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
end JanusFormal
