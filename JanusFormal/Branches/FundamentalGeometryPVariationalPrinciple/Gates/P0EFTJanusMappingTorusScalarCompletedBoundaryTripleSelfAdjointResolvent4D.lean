import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

/-!
# Self-adjointness from one real resolvent

A densely defined symmetric realization does not need a separate maximal-adjoint
regularity theorem once one real shifted operator is surjective.

Let `y` be an actual Hilbert-adjoint vector with adjoint value `z`.  Solve

`(A - ρ) x = z - ρ y`.

For every domain test vector `v`, the adjoint relation and symmetry give

`<(A - ρ)v, y - x> = 0`.

Surjectivity of `A - ρ` lets us choose `v` whose shifted image is `y - x`, so
`‖y - x‖² = 0`.  Hence `y = x` belongs to the original realization domain.

Thus any bounded direct resolvent at a real parameter proves actual Hilbert
self-adjointness.  This removes maximal-adjoint graph regularity from the final
analytic input package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

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

/-- A bounded real resolvent gives the reverse actual-adjoint domain inclusion. -/
theorem actualAdjointDomain_subset_realizationDomain_of_boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    triple.actualAdjointDomain condition ⊆
      triple.realizationDomain condition := by
  intro candidate hCandidate
  rcases hCandidate with ⟨adjointValue, hPair⟩
  let source : Ambient := adjointValue - spectralParameter • candidate
  let field : triple.lagrangianDomainSubmodule condition :=
    bounded.resolvent source
  have hFieldEquation :
      triple.lagrangianShiftedOperator condition spectralParameter field =
        source := by
    dsimp [field]
    exact bounded.left_inverse source
  have hActualShifted
      (test : triple.lagrangianDomainSubmodule condition) :
      inner Real
          (triple.lagrangianShiftedOperator
            condition spectralParameter test)
          candidate =
        inner Real (triple.lagrangianInclusion condition test) source := by
    unfold source
    rw [triple.lagrangianShiftedOperator_apply,
      inner_sub_left, hPair test, inner_sub_right]
    simp only [real_inner_smul_left, real_inner_smul_right]
  have hShiftedSymmetric
      (test : triple.lagrangianDomainSubmodule condition) :
      inner Real
          (triple.lagrangianShiftedOperator
            condition spectralParameter test)
          (triple.lagrangianInclusion condition field) =
        inner Real
          (triple.lagrangianInclusion condition test)
          (triple.lagrangianShiftedOperator
            condition spectralParameter field) := by
    have hOperator := triple.lagrangianOperator_symmetric
      condition test field
    rw [triple.lagrangianShiftedOperator_apply,
      triple.lagrangianShiftedOperator_apply,
      inner_sub_left, inner_sub_right, hOperator]
    simp only [real_inner_smul_left, real_inner_smul_right]
  let residual : Ambient :=
    candidate - triple.lagrangianInclusion condition field
  have hOrthogonal
      (test : triple.lagrangianDomainSubmodule condition) :
      inner Real
          (triple.lagrangianShiftedOperator
            condition spectralParameter test)
          residual = 0 := by
    unfold residual
    rw [inner_sub_right, hActualShifted test,
      hShiftedSymmetric test, hFieldEquation, sub_self]
  let residualTest : triple.lagrangianDomainSubmodule condition :=
    bounded.resolvent residual
  have hResidualTestEquation :
      triple.lagrangianShiftedOperator condition spectralParameter residualTest =
        residual := by
    dsimp [residualTest]
    exact bounded.left_inverse residual
  have hSelf := hOrthogonal residualTest
  rw [hResidualTestEquation] at hSelf
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hSelf
  have hNorm : ‖residual‖ = 0 := by
    nlinarith [sq_nonneg ‖residual‖]
  have hResidualZero : residual = 0 := norm_eq_zero.mp hNorm
  refine ⟨field, ?_⟩
  unfold residual at hResidualZero
  exact (sub_eq_zero.mp hResidualZero).symm

/-- A bounded real resolvent proves actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    triple.actualAdjointDomain condition =
      triple.realizationDomain condition :=
  Set.Subset.antisymm
    (triple.actualAdjointDomain_subset_realizationDomain_of_boundedResolvent
      condition spectralParameter bounded)
    (triple.realizationDomain_subset_actualAdjointDomain condition)

/-- Resolvent-based self-adjointness certificate. -/
theorem boundedResolvent_selfAdjoint_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter) :
    triple.LagrangianResolventPoint condition spectralParameter ∧
      triple.actualAdjointDomain condition =
        triple.realizationDomain condition :=
  ⟨bounded.resolventPoint triple condition spectralParameter,
    triple.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      condition spectralParameter bounded⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
