import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

/-!
# Closed scalar operator graph with completed boundary trace

This file isolates the analytic mechanism needed after boundary Lagrangian
maximality.  Starting from an algebraic scalar Green system with values in a
real Hilbert ambient space, it closes the graph of `(u, A u)`.

If the paired boundary trace `(gamma_0 u, gamma_1 u)` is bounded by that graph
norm, it extends uniquely to the graph completion.  The completed trace remains
surjective, and the exact Green identity extends from the dense algebraic core
to the whole completed graph by continuity.

The graph-bound hypothesis is the honest remaining normal-trace estimate.  No
unbounded-operator adjoint is manufactured here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Algebraic scalar Green system already expressed in a Hilbert boundary
trace space. -/
structure CanonicalScalarHilbertGreenSystem where
  inclusion : Domain →ₗ[Real] Ambient
  operator : Domain →ₗ[Real] Ambient
  boundaryTrace : Domain →ₗ[Real]
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace)
  boundary_surjective : Function.Surjective boundaryTrace
  green_identity : ∀ first second : Domain,
    inner Real (operator first) (inclusion second) -
        inner Real (inclusion first) (operator second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (boundaryTrace first) (boundaryTrace second)

/-- Algebraic graph map `u ↦ (u, A u)`. -/
def canonicalScalarOperatorGraphLinearMap
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    Domain →ₗ[Real] Ambient × Ambient where
  toFun field := (data.inclusion field, data.operator field)
  map_add' first second := by
    simp
  map_smul' scalar field := by
    simp

@[simp] theorem canonicalScalarOperatorGraphLinearMap_fst
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (field : Domain) :
    (canonicalScalarOperatorGraphLinearMap data field).1 =
      data.inclusion field :=
  rfl

@[simp] theorem canonicalScalarOperatorGraphLinearMap_snd
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (field : Domain) :
    (canonicalScalarOperatorGraphLinearMap data field).2 =
      data.operator field :=
  rfl

/-- Closed graph submodule in `Ambient × Ambient`. -/
def canonicalScalarOperatorGraphSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    Submodule Real (Ambient × Ambient) :=
  (LinearMap.range (canonicalScalarOperatorGraphLinearMap data)).topologicalClosure

/-- Completed scalar graph domain.  A point stores its ambient value and its
operator value together. -/
abbrev CanonicalScalarOperatorGraphSpace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :=
  canonicalScalarOperatorGraphSubmodule data

/-- Dense inclusion of the algebraic core into its graph completion. -/
def canonicalScalarSmoothToOperatorGraphLinearMap
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    Domain →ₗ[Real] CanonicalScalarOperatorGraphSpace data where
  toFun field :=
    ⟨canonicalScalarOperatorGraphLinearMap data field,
      (LinearMap.range
        (canonicalScalarOperatorGraphLinearMap data)).le_topologicalClosure
          (LinearMap.mem_range_self
            (canonicalScalarOperatorGraphLinearMap data) field)⟩
  map_add' first second :=
    Subtype.ext ((canonicalScalarOperatorGraphLinearMap data).map_add first second)
  map_smul' scalar field :=
    Subtype.ext ((canonicalScalarOperatorGraphLinearMap data).map_smul scalar field)

/-- The algebraic graph core is dense by construction. -/
theorem canonicalScalarSmoothToOperatorGraph_denseRange
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    DenseRange (canonicalScalarSmoothToOperatorGraphLinearMap data) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let graph := canonicalScalarOperatorGraphLinearMap data
  have hRange :
      Subtype.val '' Set.range
          (canonicalScalarSmoothToOperatorGraphLinearMap data) =
        (LinearMap.range graph : Set (Ambient × Ambient)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨field, rfl⟩, rfl⟩
      exact ⟨field, rfl⟩
    · rintro ⟨field, rfl⟩
      exact ⟨canonicalScalarSmoothToOperatorGraphLinearMap data field,
        ⟨field, rfl⟩, rfl⟩
  change closure (LinearMap.range graph : Set (Ambient × Ambient)) ⊆
    closure (Subtype.val '' Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data))
  rw [hRange]

/-- Completeness inherited from the closed subspace of the product Hilbert
space. -/
@[implicit_reducible]
def canonicalScalarOperatorGraphCompleteSpace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    CompleteSpace (CanonicalScalarOperatorGraphSpace data) := by
  letI : CompleteSpace (Ambient × Ambient) := inferInstance
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range (canonicalScalarOperatorGraphLinearMap data))

/-- Ambient field coordinate on the graph completion. -/
def canonicalScalarOperatorGraphInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    CanonicalScalarOperatorGraphSpace data →L[Real] Ambient :=
  (ContinuousLinearMap.fst Real Ambient Ambient).comp
    (canonicalScalarOperatorGraphSubmodule data).subtypeL

/-- Operator coordinate on the graph completion. -/
def canonicalScalarOperatorGraphOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    CanonicalScalarOperatorGraphSpace data →L[Real] Ambient :=
  (ContinuousLinearMap.snd Real Ambient Ambient).comp
    (canonicalScalarOperatorGraphSubmodule data).subtypeL

@[simp] theorem canonicalScalarOperatorGraphInclusion_smooth
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (field : Domain) :
    canonicalScalarOperatorGraphInclusion data
        (canonicalScalarSmoothToOperatorGraphLinearMap data field) =
      data.inclusion field :=
  rfl

@[simp] theorem canonicalScalarOperatorGraphOperator_smooth
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (field : Domain) :
    canonicalScalarOperatorGraphOperator data
        (canonicalScalarSmoothToOperatorGraphLinearMap data field) =
      data.operator field :=
  rfl

/-- Exact graph-norm hypothesis needed to complete both value and normal
boundary traces. -/
structure HasCanonicalScalarHilbertBoundaryGraphBound
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : Domain,
    ‖data.boundaryTrace field‖ ≤
      constant * ‖canonicalScalarSmoothToOperatorGraphLinearMap data field‖

/-- Unique continuous paired boundary trace on the closed graph. -/
def canonicalScalarCompletedBoundaryTrace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    CanonicalScalarOperatorGraphSpace data →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
  data.boundaryTrace.extendOfNorm
    (canonicalScalarSmoothToOperatorGraphLinearMap data)

/-- Completed trace agrees with the original trace on the algebraic core. -/
theorem canonicalScalarCompletedBoundaryTrace_agrees_on_smooth
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : Domain) :
    canonicalScalarCompletedBoundaryTrace data traceBound
        (canonicalScalarSmoothToOperatorGraphLinearMap data field) =
      data.boundaryTrace field :=
  LinearMap.extendOfNorm_eq
    (canonicalScalarSmoothToOperatorGraph_denseRange data)
    ⟨traceBound.constant, traceBound.bound⟩ field

/-- Uniform norm estimate on the completed boundary trace. -/
theorem canonicalScalarCompletedBoundaryTrace_norm_le
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    ‖canonicalScalarCompletedBoundaryTrace data traceBound field‖ ≤
      traceBound.constant * ‖field‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    (canonicalScalarSmoothToOperatorGraph_denseRange data)
    traceBound.constant traceBound.bound field

/-- Uniqueness of the completed paired trace. -/
theorem canonicalScalarCompletedBoundaryTrace_unique
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (candidate : CanonicalScalarOperatorGraphSpace data →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace))
    (hCandidate : ∀ field : Domain,
      candidate (canonicalScalarSmoothToOperatorGraphLinearMap data field) =
        data.boundaryTrace field) :
    canonicalScalarCompletedBoundaryTrace data traceBound = candidate := by
  apply LinearMap.extendOfNorm_unique
    (canonicalScalarSmoothToOperatorGraph_denseRange data)
    traceBound.constant traceBound.bound
  apply LinearMap.ext
  intro field
  exact hCandidate field

/-- Value component of the completed trace. -/
def canonicalScalarCompletedValueTrace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    CanonicalScalarOperatorGraphSpace data →L[Real] Trace :=
  (ContinuousLinearMap.fst Real Trace Trace).comp
    (canonicalScalarCompletedBoundaryTrace data traceBound)

/-- Normal component of the completed trace. -/
def canonicalScalarCompletedNormalTrace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    CanonicalScalarOperatorGraphSpace data →L[Real] Trace :=
  (ContinuousLinearMap.snd Real Trace Trace).comp
    (canonicalScalarCompletedBoundaryTrace data traceBound)

@[simp] theorem canonicalScalarCompletedValueTrace_smooth
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : Domain) :
    canonicalScalarCompletedValueTrace data traceBound
        (canonicalScalarSmoothToOperatorGraphLinearMap data field) =
      (data.boundaryTrace field).1 := by
  rw [canonicalScalarCompletedValueTrace,
    canonicalScalarCompletedBoundaryTrace_agrees_on_smooth]
  rfl

@[simp] theorem canonicalScalarCompletedNormalTrace_smooth
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : Domain) :
    canonicalScalarCompletedNormalTrace data traceBound
        (canonicalScalarSmoothToOperatorGraphLinearMap data field) =
      (data.boundaryTrace field).2 := by
  rw [canonicalScalarCompletedNormalTrace,
    canonicalScalarCompletedBoundaryTrace_agrees_on_smooth]
  rfl

/-- Surjectivity survives completion because the algebraic core already realizes
every Hilbert boundary pair. -/
theorem canonicalScalarCompletedBoundaryTrace_surjective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Surjective
      (canonicalScalarCompletedBoundaryTrace data traceBound) := by
  intro boundary
  obtain ⟨field, hField⟩ := data.boundary_surjective boundary
  refine ⟨canonicalScalarSmoothToOperatorGraphLinearMap data field, ?_⟩
  rw [canonicalScalarCompletedBoundaryTrace_agrees_on_smooth, hField]

/-- Completed boundary Green pairing. -/
def canonicalScalarCompletedBoundaryGreenPairing
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (first second : CanonicalScalarOperatorGraphSpace data) : Real :=
  2 * canonicalScalarHilbertBoundarySymplecticForm
    (canonicalScalarCompletedBoundaryTrace data traceBound first)
    (canonicalScalarCompletedBoundaryTrace data traceBound second)

private theorem canonicalScalarCompletedGreenIdentity_left_smooth
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (test : Domain) (first : CanonicalScalarOperatorGraphSpace data) :
    inner Real (canonicalScalarOperatorGraphOperator data first)
          (canonicalScalarOperatorGraphInclusion data
            (canonicalScalarSmoothToOperatorGraphLinearMap data test)) -
        inner Real (canonicalScalarOperatorGraphInclusion data first)
          (canonicalScalarOperatorGraphOperator data
            (canonicalScalarSmoothToOperatorGraphLinearMap data test)) =
      canonicalScalarCompletedBoundaryGreenPairing data traceBound first
        (canonicalScalarSmoothToOperatorGraphLinearMap data test) := by
  let smooth := canonicalScalarSmoothToOperatorGraphLinearMap data
  let good : Set (CanonicalScalarOperatorGraphSpace data) :=
    {candidate |
      inner Real (canonicalScalarOperatorGraphOperator data candidate)
            (canonicalScalarOperatorGraphInclusion data (smooth test)) -
          inner Real (canonicalScalarOperatorGraphInclusion data candidate)
            (canonicalScalarOperatorGraphOperator data (smooth test)) =
        canonicalScalarCompletedBoundaryGreenPairing data traceBound candidate
          (smooth test)}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq
    · fun_prop
    · unfold canonicalScalarCompletedBoundaryGreenPairing
      unfold canonicalScalarHilbertBoundarySymplecticForm
      fun_prop
  have hRange : Set.range smooth ⊆ good := by
    rintro candidate ⟨field, rfl⟩
    change inner Real (data.operator field) (data.inclusion test) -
        inner Real (data.inclusion field) (data.operator test) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (canonicalScalarCompletedBoundaryTrace data traceBound (smooth field))
        (canonicalScalarCompletedBoundaryTrace data traceBound (smooth test))
    rw [canonicalScalarCompletedBoundaryTrace_agrees_on_smooth,
      canonicalScalarCompletedBoundaryTrace_agrees_on_smooth]
    exact data.green_identity field test
  have hClosure : closure (Set.range smooth) = Set.univ :=
    (canonicalScalarSmoothToOperatorGraph_denseRange data).closure_range
  have hFirstClosure : first ∈ closure (Set.range smooth) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hFirstClosure

/-- The exact Green identity extends to the full closed graph. -/
theorem canonicalScalarCompletedGreenIdentity
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (first second : CanonicalScalarOperatorGraphSpace data) :
    inner Real (canonicalScalarOperatorGraphOperator data first)
          (canonicalScalarOperatorGraphInclusion data second) -
        inner Real (canonicalScalarOperatorGraphInclusion data first)
          (canonicalScalarOperatorGraphOperator data second) =
      canonicalScalarCompletedBoundaryGreenPairing data traceBound first second := by
  let smooth := canonicalScalarSmoothToOperatorGraphLinearMap data
  let good : Set (CanonicalScalarOperatorGraphSpace data) :=
    {candidate |
      inner Real (canonicalScalarOperatorGraphOperator data first)
            (canonicalScalarOperatorGraphInclusion data candidate) -
          inner Real (canonicalScalarOperatorGraphInclusion data first)
            (canonicalScalarOperatorGraphOperator data candidate) =
        canonicalScalarCompletedBoundaryGreenPairing data traceBound first candidate}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq
    · fun_prop
    · unfold canonicalScalarCompletedBoundaryGreenPairing
      unfold canonicalScalarHilbertBoundarySymplecticForm
      fun_prop
  have hRange : Set.range smooth ⊆ good := by
    rintro candidate ⟨test, rfl⟩
    exact canonicalScalarCompletedGreenIdentity_left_smooth
      data traceBound test first
  have hClosure : closure (Set.range smooth) = Set.univ :=
    (canonicalScalarSmoothToOperatorGraph_denseRange data).closure_range
  have hSecondClosure : second ∈ closure (Set.range smooth) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hSecondClosure

/-- Graph-completion certificate collecting density, trace extension,
surjectivity and the completed Green identity. -/
theorem canonicalScalarOperatorGraphCompletion_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    DenseRange (canonicalScalarSmoothToOperatorGraphLinearMap data) ∧
      Function.Surjective
        (canonicalScalarCompletedBoundaryTrace data traceBound) ∧
      (∀ first second : CanonicalScalarOperatorGraphSpace data,
        inner Real (canonicalScalarOperatorGraphOperator data first)
              (canonicalScalarOperatorGraphInclusion data second) -
            inner Real (canonicalScalarOperatorGraphInclusion data first)
              (canonicalScalarOperatorGraphOperator data second) =
          canonicalScalarCompletedBoundaryGreenPairing
            data traceBound first second) := by
  exact ⟨canonicalScalarSmoothToOperatorGraph_denseRange data,
    canonicalScalarCompletedBoundaryTrace_surjective data traceBound,
    canonicalScalarCompletedGreenIdentity data traceBound⟩

end
end P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
end JanusFormal
