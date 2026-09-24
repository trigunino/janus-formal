import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! A genuine operator core from dense ambient samples by orthogonal graph projection. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProjectedGraphCore4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12ClosedFeatureCore4D
variable {D H : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (operator : H →ₗ.[Real] H) (hClosed : operator.IsClosed)

private def hilbertGraph : Submodule Real (WithLp 2 (H × H)) :=
  operator.graph.comap (WithLp.prodContinuousLinearEquiv 2 Real H H).toLinearMap

include hClosed in
omit [CompleteSpace H] in
private theorem hilbertGraph_closed : IsClosed (hilbertGraph operator : Set (WithLp 2 (H × H))) :=
  hClosed.preimage (WithLp.prodContinuousLinearEquiv 2 Real H H).continuous

/-- Both coordinates of the orthogonal projection onto the actual closed graph. -/
def closedGraphProjection : WithLp 2 (H × H) →L[Real] H × H := by
  letI : CompleteSpace (hilbertGraph operator) := (hilbertGraph_closed operator hClosed).completeSpace_coe
  exact (WithLp.prodContinuousLinearEquiv 2 Real H H).toContinuousLinearMap.comp
    (hilbertGraph operator).starProjection

theorem closedGraphProjection_mem (point : WithLp 2 (H × H)) :
    closedGraphProjection operator hClosed point ∈ operator.graph := by
  letI : CompleteSpace (hilbertGraph operator) := (hilbertGraph_closed operator hClosed).completeSpace_coe
  exact (hilbertGraph operator).starProjection_apply_mem point

theorem closedGraphProjection_fixed (point : H × H) (hPoint : point ∈ operator.graph) :
    closedGraphProjection operator hClosed (WithLp.toLp 2 point) = point := by
  letI : CompleteSpace (hilbertGraph operator) := (hilbertGraph_closed operator hClosed).completeSpace_coe
  have h : (hilbertGraph operator).starProjection (WithLp.toLp 2 point) = WithLp.toLp 2 point :=
    (hilbertGraph operator).starProjection_eq_self_iff.mpr hPoint
  exact congrArg (WithLp.ofLp (p := 2)) h

theorem closedGraphProjection_orthogonality (point : WithLp 2 (H × H))
    (test : H × H) (hTest : test ∈ operator.graph) :
    inner Real (point.fst - (closedGraphProjection operator hClosed point).1) test.1 +
      inner Real (point.snd - (closedGraphProjection operator hClosed point).2) test.2 = 0 := by
  letI : CompleteSpace (hilbertGraph operator) := (hilbertGraph_closed operator hClosed).completeSpace_coe
  have h := (hilbertGraph operator).sub_starProjection_mem_orthogonal point
  exact ((hilbertGraph operator).mem_orthogonal' _).mp h (WithLp.toLp 2 test) hTest

variable (samples : D →ₗ[Real] WithLp 2 (H × H))

def projectedGraphSamples : D →ₗ[Real] H × H :=
  (closedGraphProjection operator hClosed).toLinearMap.comp samples

def projectedCoreInput : D →ₗ[Real] H :=
  (LinearMap.fst Real H H).comp (projectedGraphSamples operator hClosed samples)

def projectedCoreOutput : D →ₗ[Real] H :=
  (LinearMap.snd Real H H).comp (projectedGraphSamples operator hClosed samples)

theorem projectedCore_mem_domain (point : D) :
    projectedCoreInput operator hClosed samples point ∈ operator.domain := by
  obtain ⟨state, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (closedGraphProjection_mem operator hClosed (samples point))
  change state.val = projectedCoreInput operator hClosed samples point at hInput
  exact hInput ▸ state.property

theorem projectedCore_apply (point : D) :
    operator ⟨projectedCoreInput operator hClosed samples point,
      projectedCore_mem_domain operator hClosed samples point⟩ = projectedCoreOutput operator hClosed samples point := by
  obtain ⟨state, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (closedGraphProjection_mem operator hClosed (samples point))
  change state.val = projectedCoreInput operator hClosed samples point at hInput
  change operator state = projectedCoreOutput operator hClosed samples point at hOutput
  rw [← hOutput]
  exact congrArg operator (Subtype.ext hInput.symm)

theorem projectedGraphSamples_closure (hDense : DenseRange samples) :
    (projectedGraphSamples operator hClosed samples).range.topologicalClosure = operator.graph := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨point, rfl⟩
      exact closedGraphProjection_mem operator hClosed _
    · exact hClosed
  · intro point hPoint
    have h : closedGraphProjection operator hClosed (WithLp.toLp 2 point) ∈
        closure ((projectedGraphSamples operator hClosed samples).range : Set (H × H)) :=
      hDense.induction_on (WithLp.toLp 2 point)
      (isClosed_closure.preimage (closedGraphProjection operator hClosed).continuous)
      (fun sample => show closedGraphProjection operator hClosed (samples sample) ∈
        closure ((projectedGraphSamples operator hClosed samples).range : Set (H × H)) from
          subset_closure ⟨sample, rfl⟩)
    rw [closedGraphProjection_fixed operator hClosed point hPoint] at h
    exact h

/-- L2 density is used before projection; the resulting family is dense in the graph norm. -/
theorem projectedCore_hasCore (hDense : DenseRange samples) :
    operator.HasCore (projectedCoreInput operator hClosed samples).range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨point, rfl⟩
    exact projectedCore_mem_domain operator hClosed samples point
  · have hClosable := hClosed.isClosable.leIsClosable (show
        operator.domRestrict (projectedCoreInput operator hClosed samples).range ≤ operator from LinearPMap.domRestrict_le)
    apply LinearPMap.eq_of_eq_graph
    rw [← hClosable.graph_closure_eq_closure_graph,
      smoothRestriction_graph _ _ operator
        (projectedCore_mem_domain operator hClosed samples) (projectedCore_apply operator hClosed samples)]
    exact projectedGraphSamples_closure operator hClosed samples hDense

theorem projectedCore_adjoint_graph_iff (hDense : DenseRange samples)
    (hDomain : Dense (operator.domain : Set H)) (input output : H) :
    (input, output) ∈ operator.adjoint.graph ↔
    ∀ test, inner Real (projectedCoreOutput operator hClosed samples test) input =
      inner Real (projectedCoreInput operator hClosed samples test) output := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hDomain, Submodule.mem_adjoint_iff]
  constructor
  · intro h test
    exact sub_eq_zero.mp (h _ _ (closedGraphProjection_mem operator hClosed (samples test)))
  · intro h first second hGraph
    rw [← projectedGraphSamples_closure operator hClosed samples hDense] at hGraph
    have hClosedPair : IsClosed {pair : H × H |
        inner Real pair.2 input = inner Real pair.1 output} := by
      apply isClosed_eq <;> fun_prop
    exact sub_eq_zero.mpr (closure_minimal
      (by rintro pair ⟨test, rfl⟩; exact h test) hClosedPair hGraph)

/-- Tests on the projected family determine the full self-adjoint graph. -/
theorem projectedCore_selfAdjoint_graph_iff (hDense : DenseRange samples)
    (hDomain : Dense (operator.domain : Set H)) (hSelf : IsSelfAdjoint operator)
    (input output : H) :
    (input, output) ∈ operator.graph ↔
    ∀ test, inner Real (projectedCoreOutput operator hClosed samples test) input =
      inner Real (projectedCoreInput operator hClosed samples test) output := by
  have h := projectedCore_adjoint_graph_iff operator hClosed samples hDense hDomain input output
  rwa [LinearPMap.isSelfAdjoint_def.mp hSelf] at h

end
end JanusFormal.P0EFTJanusProgramPT12ProjectedGraphCore4D
