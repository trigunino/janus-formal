import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D

/-!
# Adjoint regularity as membership in the completed scalar graph

The true analytic content of maximal-adjoint regularity is that every Hilbert
adjoint pair `(candidate,adjointValue)` belongs to the closure of the smooth
operator graph.

This file proves that this graph-membership statement is equivalent to the
representation interface used by the actual-adjoint theorem.  It also supplies
a practical sequential criterion: it is enough to approximate every adjoint
pair by smooth core fields whose ambient values and operator values converge in
`L²`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- One actual Hilbert adjoint pair for the selected realization. -/
def IsActualAdjointPair
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate adjointValue : Ambient) : Prop :=
  ∀ test : triple.lagrangianDomainSubmodule condition,
    inner Real (triple.lagrangianOperator condition test) candidate =
      inner Real (triple.lagrangianInclusion condition test) adjointValue

/-- Graph-membership formulation of maximal adjoint regularity. -/
def AdjointPairGraphRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) : Prop :=
  ∀ candidate adjointValue : Ambient,
    triple.IsActualAdjointPair condition candidate adjointValue →
      (candidate, adjointValue) ∈
        canonicalScalarGreenCoreGraphSubmodule core

/-- Graph membership gives the maximal graph representative. -/
theorem maximalAdjointRegularity_of_graphRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition) :
    triple.MaximalAdjointRegularity condition where
  represent := by
    intro candidate adjointValue hPair
    exact ⟨⟨(candidate, adjointValue),
      regularity candidate adjointValue hPair⟩, rfl, rfl⟩

/-- A maximal graph representative gives graph membership. -/
theorem graphRegularity_of_maximalAdjointRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.MaximalAdjointRegularity condition) :
    triple.AdjointPairGraphRegularity condition := by
  intro candidate adjointValue hPair
  obtain ⟨maximal, hCandidate, hAdjoint⟩ :=
    regularity.represent candidate adjointValue hPair
  have hPairEquality : maximal.1 = (candidate, adjointValue) := by
    apply Prod.ext
    · exact hCandidate
    · exact hAdjoint
  rw [← hPairEquality]
  exact maximal.2

/-- Equivalence of the two maximal-regularity formulations. -/
theorem adjointPairGraphRegularity_iff_maximalAdjointRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    triple.AdjointPairGraphRegularity condition ↔
      Nonempty (triple.MaximalAdjointRegularity condition) := by
  constructor
  · intro regularity
    exact ⟨triple.maximalAdjointRegularity_of_graphRegularity
      condition regularity⟩
  · rintro ⟨regularity⟩
    exact triple.graphRegularity_of_maximalAdjointRegularity
      condition regularity

/-- Smooth sequential approximation of every Hilbert adjoint pair. -/
structure AdjointPairSmoothApproximationData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  approximation : ∀ (candidate adjointValue : Ambient),
    triple.IsActualAdjointPair condition candidate adjointValue →
      Nat → Domain
  inclusion_tendsto : ∀ (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue),
    Tendsto
      (fun index => core.inclusion
        (approximation candidate adjointValue hPair index))
      atTop (𝓝 candidate)
  operator_tendsto : ∀ (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue),
    Tendsto
      (fun index => core.operator
        (approximation candidate adjointValue hPair index))
      atTop (𝓝 adjointValue)

namespace AdjointPairSmoothApproximationData

/-- Smooth graph approximation gives membership in the completed maximal graph. -/
theorem graphRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (approximationData : triple.AdjointPairSmoothApproximationData condition) :
    triple.AdjointPairGraphRegularity condition := by
  intro candidate adjointValue hPair
  let approximation := approximationData.approximation
    candidate adjointValue hPair
  have hPairTendsto :
      Tendsto
        (fun index =>
          (core.inclusion (approximation index),
            core.operator (approximation index)))
        atTop (𝓝 (candidate, adjointValue)) :=
    (approximationData.inclusion_tendsto candidate adjointValue hPair).prodMk_nhds
      (approximationData.operator_tendsto candidate adjointValue hPair)
  change (candidate, adjointValue) ∈ closure
    (Set.range (canonicalScalarGreenCoreGraphLinearMap core))
  exact mem_closure_of_tendsto hPairTendsto
    (Filter.Eventually.of_forall fun index =>
      ⟨approximation index, rfl⟩)

/-- Sequential approximation gives the representation interface. -/
def maximalAdjointRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (approximationData : triple.AdjointPairSmoothApproximationData condition) :
    triple.MaximalAdjointRegularity condition :=
  triple.maximalAdjointRegularity_of_graphRegularity
    condition (approximationData.graphRegularity triple condition)

/-- Sequential maximal-regularity certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (approximationData : triple.AdjointPairSmoothApproximationData condition) :
    triple.AdjointPairGraphRegularity condition ∧
      Nonempty (triple.MaximalAdjointRegularity condition) ∧
      triple.actualAdjointDomain condition =
        triple.realizationDomain condition :=
  ⟨approximationData.graphRegularity triple condition,
    ⟨approximationData.maximalAdjointRegularity triple condition⟩,
    triple.actualAdjointDomain_eq_realizationDomain condition
      (approximationData.maximalAdjointRegularity triple condition)⟩

end AdjointPairSmoothApproximationData

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
end JanusFormal
