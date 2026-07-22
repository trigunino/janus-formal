import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

/-!
# Direct operator eigenspaces and compact resolvent eigenspaces

At a bounded reference resolvent `R_rho`, every direct operator eigenfield of
eigenvalue `lambda != rho` maps injectively, by ambient inclusion, into the
resolvent eigenspace of eigenvalue `(lambda-rho)⁻¹`.

Consequently compactness of the reference resolvent gives finite-dimensional
direct operator eigenspaces.  Symmetry of the completed Lagrangian realization
also gives orthogonality of distinct direct eigenvalues.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Reference-resolvent eigenvalue corresponding to an operator eigenvalue. -/
def lagrangianResolventEigenvalue
    (referenceParameter eigenvalue : Real) : Real :=
  (eigenvalue - referenceParameter)⁻¹

/-- The shifted equation of a direct operator eigenfield. -/
theorem shifted_eq_smul_inclusion_of_mem_eigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter eigenvalue : Real)
    (field : triple.lagrangianOperatorEigenspace condition eigenvalue) :
    triple.lagrangianShiftedOperator condition referenceParameter field.1 =
      (eigenvalue - referenceParameter) •
        triple.lagrangianInclusion condition field.1 := by
  have hEigen := (triple.mem_lagrangianOperatorEigenspace
    condition eigenvalue field.1).1 field.2
  rw [triple.lagrangianShiftedOperator_apply, hEigen]
  module

/-- Ambient inclusion of an operator eigenfield is a resolvent eigenvector. -/
theorem ambientResolvent_inclusion_of_mem_eigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter eigenvalue : Real)
    (hDifference : eigenvalue ≠ referenceParameter)
    (bounded : triple.LagrangianBoundedResolventAt
      condition referenceParameter)
    (field : triple.lagrangianOperatorEigenspace condition eigenvalue) :
    bounded.ambientResolvent triple condition referenceParameter
        (triple.lagrangianInclusion condition field.1) =
      triple.lagrangianResolventEigenvalue referenceParameter eigenvalue •
        triple.lagrangianInclusion condition field.1 := by
  let difference := eigenvalue - referenceParameter
  have hDifferenceZero : difference ≠ 0 := sub_ne_zero.mpr hDifference
  have hShift := triple.shifted_eq_smul_inclusion_of_mem_eigenspace
    condition referenceParameter eigenvalue field
  have hRight := bounded.right_inverse field.1
  rw [hShift, map_smul] at hRight
  have hInclusion := congrArg
    (triple.lagrangianInclusion condition) hRight
  change difference •
      bounded.ambientResolvent triple condition referenceParameter
        (triple.lagrangianInclusion condition field.1) =
    triple.lagrangianInclusion condition field.1 at hInclusion
  calc
    bounded.ambientResolvent triple condition referenceParameter
        (triple.lagrangianInclusion condition field.1) =
      1 • bounded.ambientResolvent triple condition referenceParameter
        (triple.lagrangianInclusion condition field.1) := by simp
    _ = (difference⁻¹ * difference) •
        bounded.ambientResolvent triple condition referenceParameter
          (triple.lagrangianInclusion condition field.1) := by
      rw [inv_mul_cancel₀ hDifferenceZero]
    _ = difference⁻¹ •
        (difference •
          bounded.ambientResolvent triple condition referenceParameter
            (triple.lagrangianInclusion condition field.1)) := by
      rw [smul_smul]
    _ = difference⁻¹ •
        triple.lagrangianInclusion condition field.1 := by rw [hInclusion]
    _ = _ := rfl

/-- Linear injection from the direct operator eigenspace to the ambient
resolvent eigenspace. -/
def operatorEigenspaceToResolventEigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter eigenvalue : Real)
    (hDifference : eigenvalue ≠ referenceParameter)
    (bounded : triple.LagrangianBoundedResolventAt
      condition referenceParameter) :
    triple.lagrangianOperatorEigenspace condition eigenvalue →ₗ[Real]
      Module.End.eigenspace
        (bounded.ambientResolvent
          triple condition referenceParameter).toLinearMap
        (triple.lagrangianResolventEigenvalue
          referenceParameter eigenvalue) where
  toFun field :=
    ⟨triple.lagrangianInclusion condition field.1, by
      rw [Module.End.mem_eigenspace_iff]
      exact triple.ambientResolvent_inclusion_of_mem_eigenspace
        condition referenceParameter eigenvalue hDifference bounded field⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- The eigenspace transfer is injective. -/
theorem operatorEigenspaceToResolventEigenspace_injective
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter eigenvalue : Real)
    (hDifference : eigenvalue ≠ referenceParameter)
    (bounded : triple.LagrangianBoundedResolventAt
      condition referenceParameter) :
    Function.Injective
      (triple.operatorEigenspaceToResolventEigenspace
        condition referenceParameter eigenvalue hDifference bounded) := by
  intro first second hEqual
  apply Subtype.ext
  apply triple.lagrangianInclusion_injective condition
  exact congrArg Subtype.val hEqual

/-- Compact reference resolvent gives finite-dimensional direct operator
eigenspaces away from the reference point. -/
theorem LagrangianCompactResolventAt.finiteDimensional_operatorEigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter eigenvalue : Real)
    (hDifference : eigenvalue ≠ referenceParameter)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    FiniteDimensional Real
      (triple.lagrangianOperatorEigenspace condition eigenvalue) := by
  let resolventEigenvalue :=
    triple.lagrangianResolventEigenvalue referenceParameter eigenvalue
  have hResolventEigenvalue : resolventEigenvalue ≠ 0 := by
    unfold resolventEigenvalue lagrangianResolventEigenvalue
    exact inv_ne_zero (sub_ne_zero.mpr hDifference)
  letI : FiniteDimensional Real
      (Module.End.eigenspace
        (compact.bounded.ambientResolvent
          triple condition referenceParameter).toLinearMap
        resolventEigenvalue) :=
    compact.finiteDimensional_eigenspace
      triple condition referenceParameter resolventEigenvalue
      hResolventEigenvalue
  exact FiniteDimensional.of_injective
    (triple.operatorEigenspaceToResolventEigenspace
      condition referenceParameter eigenvalue hDifference compact.bounded)
    (triple.operatorEigenspaceToResolventEigenspace_injective
      condition referenceParameter eigenvalue hDifference compact.bounded)

/-- Direct eigenfields of distinct eigenvalues are ambient-orthogonal. -/
theorem lagrangianEigenfields_orthogonal
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (first : triple.lagrangianOperatorEigenspace condition firstEigenvalue)
    (second : triple.lagrangianOperatorEigenspace condition secondEigenvalue) :
    inner Real
        (triple.lagrangianInclusion condition first.1)
        (triple.lagrangianInclusion condition second.1) = 0 := by
  have hFirst := (triple.mem_lagrangianOperatorEigenspace
    condition firstEigenvalue first.1).1 first.2
  have hSecond := (triple.mem_lagrangianOperatorEigenspace
    condition secondEigenvalue second.1).1 second.2
  have hSymmetric := triple.lagrangianOperator_symmetric
    condition first.1 second.1
  rw [hFirst, hSecond,
    real_inner_smul_left, real_inner_smul_right] at hSymmetric
  have hCoefficient : firstEigenvalue - secondEigenvalue ≠ 0 :=
    sub_ne_zero.mpr hDistinct
  apply (mul_eq_zero.mp ?_).resolve_left hCoefficient
  nlinarith

/-- Direct eigenspace certificate. -/
theorem directEigenspace_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (referenceParameter eigenvalue : Real)
    (hDifference : eigenvalue ≠ referenceParameter)
    (compact : triple.LagrangianCompactResolventAt
      condition referenceParameter) :
    Function.Injective
        (triple.operatorEigenspaceToResolventEigenspace
          condition referenceParameter eigenvalue hDifference compact.bounded) ∧
      FiniteDimensional Real
        (triple.lagrangianOperatorEigenspace condition eigenvalue) :=
  ⟨triple.operatorEigenspaceToResolventEigenspace_injective
      condition referenceParameter eigenvalue hDifference compact.bounded,
    compact.finiteDimensional_operatorEigenspace
      triple condition referenceParameter eigenvalue hDifference⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
end JanusFormal
