import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D

/-!
# Semibounded spectrum on a completed scalar boundary triple

A lower quadratic-form bound on the direct completed Lagrangian realization
places every operator eigenvalue above the same bound.  Combined with one compact
reference resolvent, the direct Fredholm alternative puts the entire lower open
half-line in the resolvent set.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Direct operator eigenspace. -/
def lagrangianOperatorEigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real) :
    Submodule Real (triple.lagrangianDomainSubmodule condition) :=
  LinearMap.ker
    ((triple.lagrangianOperator condition).toLinearMap -
      eigenvalue • (triple.lagrangianInclusion condition).toLinearMap)

@[simp] theorem mem_lagrangianOperatorEigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : triple.lagrangianDomainSubmodule condition) :
    field ∈ triple.lagrangianOperatorEigenspace condition eigenvalue ↔
      triple.lagrangianOperator condition field =
        eigenvalue • triple.lagrangianInclusion condition field := by
  rw [lagrangianOperatorEigenspace, LinearMap.mem_ker]
  exact sub_eq_zero

/-- Lower-semibounded direct quadratic-form data. -/
structure LagrangianSemiboundedData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  lowerBound : Real
  bound : ∀ field : triple.lagrangianDomainSubmodule condition,
    lowerBound * ‖triple.lagrangianInclusion condition field‖ ^ 2 ≤
      inner Real (triple.lagrangianOperator condition field)
        (triple.lagrangianInclusion condition field)

/-- A nonzero domain vector has nonzero ambient image. -/
theorem lagrangianInclusion_ne_zero
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : triple.lagrangianDomainSubmodule condition)
    (hField : field ≠ 0) :
    triple.lagrangianInclusion condition field ≠ 0 := by
  intro hZero
  apply hField
  exact triple.lagrangianInclusion_injective condition hZero

/-- Every direct eigenvalue is above the lower form bound. -/
theorem LagrangianSemiboundedData.eigenvalue_ge_lowerBound
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (eigenvalue : Real)
    (field : triple.lagrangianDomainSubmodule condition)
    (hField : field ≠ 0)
    (hEigen : triple.lagrangianOperator condition field =
      eigenvalue • triple.lagrangianInclusion condition field) :
    semibounded.lowerBound ≤ eigenvalue := by
  let ambientField := triple.lagrangianInclusion condition field
  have hAmbientNonzero : ambientField ≠ 0 :=
    triple.lagrangianInclusion_ne_zero condition field hField
  have hNormPositive : 0 < ‖ambientField‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hAmbientNonzero)
  have hBound := semibounded.bound field
  rw [hEigen, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hBound
  nlinarith

/-- No direct eigenvalue lies below the lower bound. -/
theorem LagrangianSemiboundedData.not_hasEigenvalue_of_lt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (spectralParameter : Real)
    (hParameter : spectralParameter < semibounded.lowerBound) :
    ¬ triple.LagrangianHasEigenvalue condition spectralParameter := by
  rintro ⟨field, hField, hEigen⟩
  have hLower := semibounded.eigenvalue_ge_lowerBound
    triple condition spectralParameter field hField hEigen
  linarith

/-- Under compact resolvent, every nonreference parameter below the lower bound
is a direct resolvent point. -/
theorem LagrangianSemiboundedData.resolventPoint_of_lt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (referenceParameter spectralParameter : Real)
    (hReference : spectralParameter ≠ referenceParameter)
    (hParameter : spectralParameter < semibounded.lowerBound)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    triple.LagrangianResolventPoint condition spectralParameter := by
  rcases triple.lagrangian_fredholmAlternative condition referenceParameter
      spectralParameter (sub_ne_zero.mpr hReference) compact with
      hEigen | hResolvent
  · exact False.elim
      (semibounded.not_hasEigenvalue_of_lt
        triple condition spectralParameter hParameter hEigen)
  · exact hResolvent

/-- The lower open half-line, except the chosen reference point, lies in the
direct resolvent set. -/
theorem LagrangianSemiboundedData.lower_halfLine_resolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (referenceParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    Set.Iio semibounded.lowerBound \ {referenceParameter} ⊆
      triple.lagrangianResolventSet condition := by
  intro spectralParameter hParameter
  exact semibounded.resolventPoint_of_lt triple condition
    referenceParameter spectralParameter hParameter.2 hParameter.1 compact

/-- Strict positivity excludes zero as an eigenvalue. -/
theorem LagrangianSemiboundedData.not_hasEigenvalue_zero
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (hPositive : 0 < semibounded.lowerBound) :
    ¬ triple.LagrangianHasEigenvalue condition 0 :=
  semibounded.not_hasEigenvalue_of_lt triple condition 0 hPositive

/-- With compact resolvent and strict positivity, zero is a direct resolvent
point. -/
theorem LagrangianSemiboundedData.zero_resolventPoint
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (referenceParameter : Real)
    (hReference : referenceParameter ≠ 0)
    (hPositive : 0 < semibounded.lowerBound)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    triple.LagrangianResolventPoint condition 0 :=
  semibounded.resolventPoint_of_lt triple condition
    referenceParameter 0 hReference.symm hPositive compact

/-- Strict positivity makes the direct zero eigenspace trivial. -/
theorem LagrangianSemiboundedData.zero_eigenspace_eq_bot
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (hPositive : 0 < semibounded.lowerBound) :
    triple.lagrangianOperatorEigenspace condition 0 = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro first second hEqual
  have hDifference : first - second ∈
      triple.lagrangianOperatorEigenspace condition 0 := by
    rw [triple.mem_lagrangianOperatorEigenspace]
    simp only [zero_smul]
    have hOperatorEqual :
        triple.lagrangianOperator condition first =
          triple.lagrangianOperator condition second := by
      simpa using hEqual
    rw [map_sub, hOperatorEqual, sub_self]
  by_contra hFields
  have hNonzero : first - second ≠ 0 := sub_ne_zero.mpr hFields
  apply semibounded.not_hasEigenvalue_zero triple condition hPositive
  exact ⟨first - second, hNonzero,
    (triple.mem_lagrangianOperatorEigenspace
      condition 0 (first - second)).1 hDifference⟩

/-- Direct semibounded-spectrum certificate. -/
theorem directSemiboundedSpectrum_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : triple.LagrangianSemiboundedData condition)
    (referenceParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    (∀ eigenvalue : Real,
      triple.LagrangianHasEigenvalue condition eigenvalue →
        semibounded.lowerBound ≤ eigenvalue) ∧
      Set.Iio semibounded.lowerBound \ {referenceParameter} ⊆
        triple.lagrangianResolventSet condition := by
  constructor
  · intro eigenvalue hEigen
    rcases hEigen with ⟨field, hField, hEquation⟩
    exact semibounded.eigenvalue_ge_lowerBound
      triple condition eigenvalue field hField hEquation
  · exact semibounded.lower_halfLine_resolvent
      triple condition referenceParameter compact

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
