import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

/-!
# Gaussian response on a completed scalar boundary triple

At a bounded direct resolvent point, the classical sourced field is the
domain-valued resolvent.  The on-shell shifted source action is

`-1/2 <f, R_lambda f>`,

so the Gaussian generating functional is `1/2 <f,R_lambda f>`.  Symmetry of the
ambient resolvent gives a symmetric bilinear response, exact polarization and
quadratic homogeneity.  Coercivity of the shifted form makes the generating
functional nonnegative.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Classical domain-valued source solution. -/
def lagrangianClassicalSourceSolution
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    Ambient →L[Real] triple.lagrangianDomainSubmodule condition :=
  bounded.resolvent

/-- Symmetric Gaussian source pairing. -/
def lagrangianGaussianPairing
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (first second : Ambient) : Real :=
  inner Real first
    (bounded.ambientResolvent triple condition spectralParameter second)

/-- Gaussian generating functional. -/
def lagrangianGaussianGeneratingFunctional
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (source : Ambient) : Real :=
  (1 / 2 : Real) *
    triple.lagrangianGaussianPairing
      condition spectralParameter bounded source source

/-- Classical source equation. -/
theorem lagrangianClassicalSourceSolution_equation
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (source : Ambient) :
    triple.lagrangianShiftedOperator condition spectralParameter
        (triple.lagrangianClassicalSourceSolution
          condition spectralParameter bounded source) = source :=
  bounded.left_inverse source

/-- Symmetry of the Gaussian pairing. -/
theorem lagrangianGaussianPairing_comm
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (first second : Ambient) :
    triple.lagrangianGaussianPairing condition spectralParameter bounded
        first second =
      triple.lagrangianGaussianPairing condition spectralParameter bounded
        second first :=
  bounded.ambient_isSymmetric triple condition spectralParameter first second

/-- On-shell shifted source action. -/
theorem lagrangianSourceAction_onShell
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (source : Ambient) :
    triple.lagrangianSourceAction condition spectralParameter source
        (triple.lagrangianClassicalSourceSolution
          condition spectralParameter bounded source) =
      -(1 / 2 : Real) *
        triple.lagrangianGaussianPairing condition spectralParameter bounded
          source source := by
  unfold lagrangianSourceAction lagrangianShiftedQuadraticFunctional
    lagrangianShiftedJacobiPairing lagrangianGaussianPairing
    lagrangianClassicalSourceSolution
  rw [bounded.left_inverse]
  ring

/-- Generating functional is minus the on-shell source action. -/
theorem lagrangianGaussianGeneratingFunctional_eq_neg_onShell
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (source : Ambient) :
    triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
        bounded source =
      -triple.lagrangianSourceAction condition spectralParameter source
        (triple.lagrangianClassicalSourceSolution
          condition spectralParameter bounded source) := by
  rw [triple.lagrangianSourceAction_onShell]
  unfold lagrangianGaussianGeneratingFunctional
  ring

/-- Exact polarization identity. -/
theorem lagrangianGaussianGeneratingFunctional_add
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (first second : Ambient) :
    triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
        bounded (first + second) =
      triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
          bounded first +
        triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
          bounded second +
        triple.lagrangianGaussianPairing condition spectralParameter bounded
          first second := by
  unfold lagrangianGaussianGeneratingFunctional lagrangianGaussianPairing
  simp only [map_add, inner_add_left, inner_add_right]
  rw [triple.lagrangianGaussianPairing_comm condition spectralParameter
    bounded second first]
  unfold lagrangianGaussianPairing
  ring

/-- Quadratic homogeneity. -/
theorem lagrangianGaussianGeneratingFunctional_smul
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (scalar : Real) (source : Ambient) :
    triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
        bounded (scalar • source) =
      scalar ^ 2 *
        triple.lagrangianGaussianGeneratingFunctional condition
          spectralParameter bounded source := by
  unfold lagrangianGaussianGeneratingFunctional lagrangianGaussianPairing
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Shifted-form coercivity makes the Gaussian generating functional
nonnegative. -/
theorem LagrangianShiftedFormCoerciveData.gaussian_nonnegative
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition))
    (source : Ambient) :
    0 ≤ triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
      (coercive.boundedResolvent
        triple condition spectralParameter hDense) source := by
  let bounded := coercive.boundedResolvent
    triple condition spectralParameter hDense
  let solution := bounded.resolvent source
  have hEquation := bounded.left_inverse source
  have hCoercive := coercive.coercive solution
  rw [triple.lagrangianShiftedForm_apply] at hCoercive
  unfold lagrangianGaussianGeneratingFunctional lagrangianGaussianPairing
    LagrangianBoundedResolventAt.ambientResolvent
  change 0 ≤ (1 / 2 : Real) *
    inner Real source (triple.lagrangianInclusion condition solution)
  rw [← hEquation]
  linarith [sq_nonneg ‖solution‖]

/-- Direct Gaussian certificate. -/
theorem directGaussian_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (source : Ambient) :
    triple.lagrangianShiftedOperator condition spectralParameter
        (triple.lagrangianClassicalSourceSolution
          condition spectralParameter bounded source) = source ∧
      triple.lagrangianGaussianGeneratingFunctional condition spectralParameter
          bounded source =
        -triple.lagrangianSourceAction condition spectralParameter source
          (triple.lagrangianClassicalSourceSolution
            condition spectralParameter bounded source) :=
  ⟨triple.lagrangianClassicalSourceSolution_equation
      condition spectralParameter bounded source,
    triple.lagrangianGaussianGeneratingFunctional_eq_neg_onShell
      condition spectralParameter bounded source⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D
end JanusFormal
