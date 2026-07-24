import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D

/-!
# Smooth adjoint approximation from graph membership

The maximal graph is a closed subspace of a normed product space and is defined
as the closure of the smooth operator graph.  Hence, in this metrizable space,
membership in the maximal graph automatically supplies a convergent sequence of
smooth graph vectors.

This file proves the converse missing from the previous sequential reduction:
`AdjointPairGraphRegularity` constructs
`AdjointPairSmoothApproximationData`.  Therefore the genuinely minimal adjoint
input is only graph membership; the approximating sequence is no longer an
independent field.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointSequentialClosure4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointSequentialClosure4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D

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

/-- Chosen sequence of smooth-graph vectors converging to one adjoint pair. -/
noncomputable def adjointGraphApproximationPair
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue) :
    Nat → WithLp 2 (Ambient × Ambient) :=
  Classical.choose
    ((mem_closure_iff_seq_limit).1
      (regularity candidate adjointValue hPair))

/-- Every chosen graph vector lies in the smooth graph range. -/
theorem adjointGraphApproximationPair_mem_range
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue)
    (index : Nat) :
    triple.adjointGraphApproximationPair condition regularity
        candidate adjointValue hPair index ∈
      Set.range (canonicalScalarGreenCoreGraphLinearMap core) :=
  (Classical.choose_spec
    ((mem_closure_iff_seq_limit).1
      (regularity candidate adjointValue hPair))).1 index

/-- The chosen graph vectors converge to the desired adjoint pair. -/
theorem adjointGraphApproximationPair_tendsto
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue) :
    Tendsto
      (triple.adjointGraphApproximationPair condition regularity
        candidate adjointValue hPair)
      atTop (𝓝 (WithLp.toLp 2 (candidate, adjointValue))) :=
  (Classical.choose_spec
    ((mem_closure_iff_seq_limit).1
      (regularity candidate adjointValue hPair))).2

/-- Chosen smooth field representing one graph approximation vector. -/
noncomputable def adjointGraphApproximationField
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue)
    (index : Nat) : Domain :=
  Classical.choose
    (triple.adjointGraphApproximationPair_mem_range
      condition regularity candidate adjointValue hPair index)

/-- Smooth graph image of the chosen field. -/
theorem canonicalScalarGreenCoreGraphLinearMap_adjointGraphApproximationField
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue)
    (index : Nat) :
    canonicalScalarGreenCoreGraphLinearMap core
        (triple.adjointGraphApproximationField condition regularity
          candidate adjointValue hPair index) =
      triple.adjointGraphApproximationPair condition regularity
        candidate adjointValue hPair index :=
  Classical.choose_spec
    (triple.adjointGraphApproximationPair_mem_range
      condition regularity candidate adjointValue hPair index)

/-- The ambient values of the chosen smooth fields converge to the candidate. -/
theorem adjointGraphApproximationField_inclusion_tendsto
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue) :
    Tendsto
      (fun index => core.inclusion
        (triple.adjointGraphApproximationField condition regularity
          candidate adjointValue hPair index))
      atTop (𝓝 candidate) := by
  have hPairTendsto : Tendsto
      (fun index => WithLp.ofLp
        (triple.adjointGraphApproximationPair condition regularity
          candidate adjointValue hPair index))
      atTop (𝓝 (candidate, adjointValue)) :=
    ((WithLp.prod_continuous_ofLp 2 Ambient Ambient).tendsto
      (WithLp.toLp 2 (candidate, adjointValue))).comp
        (triple.adjointGraphApproximationPair_tendsto
          condition regularity candidate adjointValue hPair)
  have hFst := continuous_fst.continuousAt.tendsto.comp hPairTendsto
  apply hFst.congr
  intro index
  change
    (WithLp.ofLp
      (triple.adjointGraphApproximationPair condition regularity
        candidate adjointValue hPair index)).1 =
      core.inclusion
        (triple.adjointGraphApproximationField condition regularity
          candidate adjointValue hPair index)
  rw [← canonicalScalarGreenCoreGraphLinearMap_adjointGraphApproximationField]
  rfl

/-- The Euler images of the chosen smooth fields converge to the adjoint value. -/
theorem adjointGraphApproximationField_operator_tendsto
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition)
    (candidate adjointValue : Ambient)
    (hPair : triple.IsActualAdjointPair condition candidate adjointValue) :
    Tendsto
      (fun index => core.operator
        (triple.adjointGraphApproximationField condition regularity
          candidate adjointValue hPair index))
      atTop (𝓝 adjointValue) := by
  have hPairTendsto : Tendsto
      (fun index => WithLp.ofLp
        (triple.adjointGraphApproximationPair condition regularity
          candidate adjointValue hPair index))
      atTop (𝓝 (candidate, adjointValue)) :=
    ((WithLp.prod_continuous_ofLp 2 Ambient Ambient).tendsto
      (WithLp.toLp 2 (candidate, adjointValue))).comp
        (triple.adjointGraphApproximationPair_tendsto
          condition regularity candidate adjointValue hPair)
  have hSnd := continuous_snd.continuousAt.tendsto.comp hPairTendsto
  apply hSnd.congr
  intro index
  change
    (WithLp.ofLp
      (triple.adjointGraphApproximationPair condition regularity
        candidate adjointValue hPair index)).2 =
      core.operator
        (triple.adjointGraphApproximationField condition regularity
          candidate adjointValue hPair index)
  rw [← canonicalScalarGreenCoreGraphLinearMap_adjointGraphApproximationField]
  rfl

/-- Graph regularity automatically constructs the sequential approximation
package. -/
noncomputable def smoothApproximationData_of_graphRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition) :
    triple.AdjointPairSmoothApproximationData condition where
  approximation := triple.adjointGraphApproximationField condition regularity
  inclusion_tendsto :=
    triple.adjointGraphApproximationField_inclusion_tendsto condition regularity
  operator_tendsto :=
    triple.adjointGraphApproximationField_operator_tendsto condition regularity

/-- Equivalence between graph membership and smooth sequential approximation. -/
theorem adjointPairGraphRegularity_iff_smoothApproximation
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    triple.AdjointPairGraphRegularity condition ↔
      Nonempty (triple.AdjointPairSmoothApproximationData condition) := by
  constructor
  · intro regularity
    exact ⟨triple.smoothApproximationData_of_graphRegularity
      condition regularity⟩
  · rintro ⟨approximation⟩
    exact approximation.graphRegularity triple condition

/-- Sequential-closure certificate. -/
theorem sequentialClosure_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : triple.AdjointPairGraphRegularity condition) :
    Nonempty (triple.AdjointPairSmoothApproximationData condition) ∧
      Nonempty (triple.MaximalAdjointRegularity condition) ∧
      triple.actualAdjointDomain condition =
        triple.realizationDomain condition :=
  ⟨⟨triple.smoothApproximationData_of_graphRegularity
      condition regularity⟩,
    ⟨triple.maximalAdjointRegularity_of_graphRegularity
      condition regularity⟩,
    triple.actualAdjointDomain_eq_realizationDomain condition
      (triple.maximalAdjointRegularity_of_graphRegularity
        condition regularity)⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
