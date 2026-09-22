import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Doublet4D

/-! The bounded doublet contraction survives completion of the actual BRST
graph. No single-valuedness of that closed relation is assumed here. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismDoubletGraphClosure4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
open P0EFTJanusProgramPT12DiffeomorphismL2Doublet4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

theorem diffeomorphismL2BRST_closedGraph_contract
    (x y : DiffeomorphismL2 period hPeriod (metric .plus))
    (hxy : (x, y) ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure) :
    (diffeomorphismL2Homotopy period hPeriod metric x,
      diffeomorphismL2DoubletProjection period hPeriod metric x -
        diffeomorphismL2Homotopy period hPeriod metric y) ∈
      (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure := by
  let H := DiffeomorphismL2 period hPeriod (metric .plus)
  let q := diffeomorphismL2BRST period hPeriod metric
  let h := diffeomorphismL2Homotopy period hPeriod metric
  let p := diffeomorphismL2DoubletProjection period hPeriod metric
  let lift : (H × H) →L[Real] (H × H) :=
    (h.comp (ContinuousLinearMap.fst Real H H)).prod
      (p.comp (ContinuousLinearMap.fst Real H H) -
        h.comp (ContinuousLinearMap.snd Real H H))
  have hMaps : Set.MapsTo lift (q.graph : Set (H × H)) (q.graph : Set (H × H)) := by
    intro pair hPair
    obtain ⟨u, hu, hv⟩ := q.mem_graph_iff.mp hPair
    apply q.mem_graph_iff.mpr
    refine ⟨⟨h u, diffeomorphismL2Homotopy_mem_domain period hPeriod metric u⟩, ?_, ?_⟩
    · change h u = h pair.1
      exact congrArg h hu
    · change q _ = p pair.1 - h pair.2
      rw [← hu, ← hv]
      exact eq_sub_iff_add_eq.mpr (diffeomorphismL2BRST_contract period hPeriod metric u)
  exact hMaps.closure lift.continuous hxy

/-- A cycle in the completed graph still has an explicit doublet primitive. -/
theorem diffeomorphismL2BRST_closedGraph_doublet_cycle_exact
    (x : DiffeomorphismL2 period hPeriod (metric .plus))
    (hCycle : (x, 0) ∈ (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure) :
    (diffeomorphismL2Homotopy period hPeriod metric x,
      diffeomorphismL2DoubletProjection period hPeriod metric x) ∈
      (diffeomorphismL2BRST period hPeriod metric).graph.topologicalClosure := by
  simpa only [map_zero, sub_zero] using
    diffeomorphismL2BRST_closedGraph_contract period hPeriod metric x 0 hCycle

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismDoubletGraphClosure4D
