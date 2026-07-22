import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointSequentialClosure4D

/-!
# Adjoint graph regularity from a real resolvent

A bounded real resolvent gives more than equality of actual adjoint and
realization domains.  If the realization domain is dense, the adjoint value of a
realization vector is uniquely its operator value.  Therefore every actual
adjoint pair is represented by the corresponding completed maximal graph
vector.

Consequently a bounded real resolvent plus the already automatic domain density
constructs:

* adjoint-pair graph regularity;
* maximal adjoint regularity;
* a sequence of smooth graph vectors approximating every adjoint pair.

The former adjoint regularity input is thus fully redundant in the physical
endpoint.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolventAdjointRegularity4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolventAdjointRegularity4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointSequentialClosure4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D

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

/-- On a dense symmetric realization, an actual adjoint value attached to a
domain vector is uniquely the original operator value. -/
theorem actualAdjointValue_eq_operator_of_dense
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : triple.lagrangianDomainSubmodule condition)
    (adjointValue : Ambient)
    (hPair : ∀ test : triple.lagrangianDomainSubmodule condition,
      inner Real (triple.lagrangianOperator condition test)
          (triple.lagrangianInclusion condition field) =
        inner Real (triple.lagrangianInclusion condition test) adjointValue)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    adjointValue = triple.lagrangianOperator condition field := by
  let residual := adjointValue - triple.lagrangianOperator condition field
  have hOrthogonal (test : triple.lagrangianDomainSubmodule condition) :
      inner Real (triple.lagrangianInclusion condition test) residual = 0 := by
    unfold residual
    rw [inner_sub_right, ← hPair test]
    exact sub_eq_zero.mpr
      (triple.lagrangianOperator_symmetric condition test field)
  let good : Set Ambient := {test | inner Real test residual = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (triple.lagrangianInclusion condition) ⊆ good := by
    rintro test ⟨domainTest, rfl⟩
    exact hOrthogonal domainTest
  have hClosure : closure
      (Set.range (triple.lagrangianInclusion condition)) = Set.univ :=
    hDense.closure_range
  have hResidualMem : residual ∈ closure
      (Set.range (triple.lagrangianInclusion condition)) := by
    rw [hClosure]
    trivial
  have hSelf : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hSelf
  have hNorm : ‖residual‖ = 0 := by
    nlinarith [sq_nonneg ‖residual‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- A bounded real resolvent and dense domain generate adjoint-pair graph
regularity. -/
theorem adjointPairGraphRegularity_of_boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.AdjointPairGraphRegularity condition := by
  intro candidate adjointValue hPair
  have hActual : candidate ∈ triple.actualAdjointDomain condition :=
    ⟨adjointValue, hPair⟩
  have hRealization : candidate ∈ triple.realizationDomain condition :=
    triple.actualAdjointDomain_subset_realizationDomain_of_boundedResolvent
      condition spectralParameter bounded hActual
  rcases hRealization with ⟨field, hFieldCandidate⟩
  have hPairField : ∀ test : triple.lagrangianDomainSubmodule condition,
      inner Real (triple.lagrangianOperator condition test)
          (triple.lagrangianInclusion condition field) =
        inner Real (triple.lagrangianInclusion condition test) adjointValue := by
    intro test
    rw [hFieldCandidate]
    exact hPair test
  have hAdjointValue :
      adjointValue = triple.lagrangianOperator condition field :=
    triple.actualAdjointValue_eq_operator_of_dense
      condition field adjointValue hPairField hDense
  have hPairEquality :
      field.1.1 = WithLp.toLp 2 (candidate, adjointValue) := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · exact hFieldCandidate
    · exact hAdjointValue.symm
  rw [← hPairEquality]
  exact field.1.2

/-- Maximal adjoint regularity generated by a bounded real resolvent. -/
def maximalAdjointRegularity_of_boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.MaximalAdjointRegularity condition :=
  triple.maximalAdjointRegularity_of_graphRegularity condition
    (triple.adjointPairGraphRegularity_of_boundedResolvent
      condition spectralParameter bounded hDense)

/-- Smooth adjoint-pair approximation generated by a bounded real resolvent. -/
noncomputable def adjointPairSmoothApproximationData_of_boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.AdjointPairSmoothApproximationData condition :=
  triple.smoothApproximationData_of_graphRegularity condition
    (triple.adjointPairGraphRegularity_of_boundedResolvent
      condition spectralParameter bounded hDense)

/-- Complete resolvent-generated adjoint regularity certificate. -/
theorem boundedResolvent_adjointRegularity_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : triple.LagrangianBoundedResolventAt
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.AdjointPairGraphRegularity condition ∧
      Nonempty (triple.MaximalAdjointRegularity condition) ∧
      Nonempty (triple.AdjointPairSmoothApproximationData condition) ∧
      triple.actualAdjointDomain condition =
        triple.realizationDomain condition :=
  ⟨triple.adjointPairGraphRegularity_of_boundedResolvent
      condition spectralParameter bounded hDense,
    ⟨triple.maximalAdjointRegularity_of_boundedResolvent
      condition spectralParameter bounded hDense⟩,
    ⟨triple.adjointPairSmoothApproximationData_of_boundedResolvent
      condition spectralParameter bounded hDense⟩,
    triple.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      condition spectralParameter bounded⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
