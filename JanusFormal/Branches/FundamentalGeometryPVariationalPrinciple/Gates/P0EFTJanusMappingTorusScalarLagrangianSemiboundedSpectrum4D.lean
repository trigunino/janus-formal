import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D

/-!
# Semibounded scalar Lagrangian spectrum

The variational input for a scalar realization is a lower bound on its quadratic
form

`<A u, u> ≥ m ‖u‖²`.

This file keeps that estimate explicit and derives its spectral consequences:
operator eigenvalues lie above `m`; every real parameter below `m` is a
resolvent point once one compact resolvent is known; and a strictly positive
lower bound makes zero a resolvent point.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Lower-semibounded quadratic-form data for one closed Lagrangian scalar
realization. -/
structure CanonicalScalarClosedLagrangianSemiboundedData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  lowerBound : Real
  bound : ∀ field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition,
    lowerBound *
        ‖canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field‖ ^ 2 ≤
      inner Real
        (canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field)
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field)

/-- Every nonzero operator eigenfield has nonzero ambient image. -/
theorem canonicalScalarClosedLagrangian_eigenfield_inclusion_ne_zero
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition)
    (hField : field ≠ 0) :
    canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field ≠ 0 := by
  intro hZero
  apply hField
  exact canonicalScalarClosedLagrangianDomainInclusion_injective
    data hClosable traceBound condition hZero

/-- Every eigenvalue of a lower-semibounded realization is at least the lower
form bound. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.eigenvalue_ge_lowerBound
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (eigenvalue : Real)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition)
    (hField : field ≠ 0)
    (hEigen :
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field) :
    semibounded.lowerBound ≤ eigenvalue := by
  let ambientField := canonicalScalarClosedLagrangianDomainInclusion
    data hClosable traceBound condition field
  have hAmbientNonzero : ambientField ≠ 0 :=
    canonicalScalarClosedLagrangian_eigenfield_inclusion_ne_zero
      data hClosable traceBound condition field hField
  have hNormPositive : 0 < ‖ambientField‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hAmbientNonzero)
  have hBound := semibounded.bound field
  rw [hEigen, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hBound
  nlinarith

/-- No eigenvalue can lie strictly below the lower form bound. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.not_hasEigenvalue_of_lt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (spectralParameter : Real)
    (hParameter : spectralParameter < semibounded.lowerBound) :
    ¬ CanonicalScalarClosedLagrangianHasEigenvalue
      data hClosable traceBound condition spectralParameter := by
  rintro ⟨field, hField, hEigen⟩
  have hLower := semibounded.eigenvalue_ge_lowerBound
    data hClosable traceBound condition spectralParameter field hField hEigen
  linarith

/-- Under compact resolvent, every parameter below the lower form bound and
distinct from the reference point lies in the resolvent set of the unbounded
operator. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.resolventPoint_of_lt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (referenceParameter spectralParameter : Real)
    (hReference : spectralParameter ≠ referenceParameter)
    (hParameter : spectralParameter < semibounded.lowerBound)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition spectralParameter := by
  rcases canonicalScalarClosedLagrangian_fredholmAlternative
      data hClosable traceBound condition referenceParameter spectralParameter
        (sub_ne_zero.mpr hReference) compact with hEigen | hResolvent
  · exact False.elim
      (semibounded.not_hasEigenvalue_of_lt
        data hClosable traceBound condition spectralParameter hParameter hEigen)
  · exact hResolvent

/-- The entire open half-line below the lower bound, except possibly the chosen
reference point itself, belongs to the unbounded resolvent set. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.lower_halfLine_resolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (referenceParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    Set.Iio semibounded.lowerBound \ {referenceParameter} ⊆
      canonicalScalarClosedLagrangianResolventSet
        data hClosable traceBound condition := by
  intro spectralParameter hParameter
  exact semibounded.resolventPoint_of_lt
    data hClosable traceBound condition referenceParameter spectralParameter
      hParameter.2 hParameter.1 compact

/-- A strictly positive lower form bound excludes zero as an eigenvalue. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.not_hasEigenvalue_zero
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (hPositive : 0 < semibounded.lowerBound) :
    ¬ CanonicalScalarClosedLagrangianHasEigenvalue
      data hClosable traceBound condition 0 :=
  semibounded.not_hasEigenvalue_of_lt
    data hClosable traceBound condition 0 hPositive

/-- With compact resolvent and a strictly positive form bound, zero is a genuine
resolvent point. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.zero_resolventPoint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (referenceParameter : Real)
    (hReference : referenceParameter ≠ 0)
    (hPositive : 0 < semibounded.lowerBound)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    CanonicalScalarClosedLagrangianResolventPoint
      data hClosable traceBound condition 0 :=
  semibounded.resolventPoint_of_lt
    data hClosable traceBound condition referenceParameter 0
      hReference.symm hPositive compact

/-- Strict positivity makes the zero eigenspace trivial. -/
theorem CanonicalScalarClosedLagrangianSemiboundedData.zero_eigenspace_eq_bot
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (hPositive : 0 < semibounded.lowerBound) :
    canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition 0 = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro first second hEqual
  have hDifference : first - second ∈
      canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition 0 := by
    rw [canonicalScalarClosedLagrangianOperatorEigenspace, LinearMap.mem_ker]
    simp only [zero_smul, sub_zero]
    simp only [zero_smul, sub_zero] at hEqual
    rw [map_sub, hEqual, sub_self]
  by_contra hFields
  have hNonzero : first - second ≠ 0 := sub_ne_zero.mpr hFields
  apply semibounded.not_hasEigenvalue_zero
    data hClosable traceBound condition hPositive
  exact ⟨first - second, hNonzero,
    (mem_canonicalScalarClosedLagrangianOperatorEigenspace
      data hClosable traceBound condition 0 (first - second)).1 hDifference⟩

/-- Semibounded compact-spectrum certificate. -/
theorem canonicalScalarLagrangianSemiboundedSpectrum_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (referenceParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition referenceParameter) :
    (∀ eigenvalue : Real,
      CanonicalScalarClosedLagrangianHasEigenvalue
          data hClosable traceBound condition eigenvalue →
        semibounded.lowerBound ≤ eigenvalue) ∧
      Set.Iio semibounded.lowerBound \ {referenceParameter} ⊆
        canonicalScalarClosedLagrangianResolventSet
          data hClosable traceBound condition := by
  refine ⟨?_, semibounded.lower_halfLine_resolvent
      data hClosable traceBound condition referenceParameter compact⟩
  intro eigenvalue hEigen
  rcases hEigen with ⟨field, hField, hEquation⟩
  exact semibounded.eigenvalue_ge_lowerBound
    data hClosable traceBound condition eigenvalue field hField hEquation

end
end P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
end JanusFormal
