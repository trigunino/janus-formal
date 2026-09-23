import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonReducedAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostReducedAdjoint4D

/-! Exact ghost / metric–B splitting of the full minimal and maximal Hessian graphs. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianReducedGraphSplit4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D
open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
open P0EFTJanusProgramPT12HessianL2OperatorClosed4D
open P0EFTJanusProgramPT12HessianL2Adjoint4D
open P0EFTJanusProgramPT12HessianGhostMinimal4D
open P0EFTJanusProgramPT12HessianGhostMaximal4D
open P0EFTJanusProgramPT12HessianGhostReduced4D
open P0EFTJanusProgramPT12HessianGhostReducedAdjoint4D
open P0EFTJanusProgramPT12HessianBosonReduced4D
open P0EFTJanusProgramPT12HessianBosonReducedAdjoint4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
variable (couplings : GlobalCandidateAActionCouplings)

attribute [local irreducible] hessianL2Minimal hessianL2Maximal hessianGhostReduced hessianBosonReduced
  hessianGhostReducedAdjoint hessianBosonReducedAdjoint
  diffeomorphismGhostProjection diffeomorphismBosonProjection

theorem hessianL2Minimal_graph_iff_ghost_boson
    (input output : DiffeomorphismL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianL2Minimal period hPeriod reference metric couplings).graph ↔
      ((diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict input,
       (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict output) ∈
        (hessianGhostReduced period hPeriod reference metric couplings).graph ∧
      ((diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict input,
       (diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict output) ∈
        (hessianBosonReduced period hPeriod reference metric couplings).graph := by
  rw [hessianGhostReduced_graph_iff, hessianBosonReduced_graph_iff]
  change (input, output) ∈ (hessianL2Minimal period hPeriod reference metric couplings).graph ↔
    (diffeomorphismGhostProjection period hPeriod (metric .plus) input,
     diffeomorphismGhostProjection period hPeriod (metric .plus) output) ∈
      (hessianL2Minimal period hPeriod reference metric couplings).graph ∧
    (diffeomorphismBosonProjection period hPeriod (metric .plus) input,
     diffeomorphismBosonProjection period hPeriod (metric .plus) output) ∈
      (hessianL2Minimal period hPeriod reference metric couplings).graph
  constructor
  · intro h
    exact ⟨hessianL2Minimal_graph_ghost period hPeriod reference metric couplings _ h,
      hessianL2Minimal_graph_boson period hPeriod reference metric couplings _ h⟩
  · rintro ⟨hGhost, hBoson⟩
    have h := (hessianL2Minimal period hPeriod reference metric couplings).graph.add_mem hGhost hBoson
    change (diffeomorphismGhostProjection period hPeriod (metric .plus) input +
      diffeomorphismBosonProjection period hPeriod (metric .plus) input,
      diffeomorphismGhostProjection period hPeriod (metric .plus) output +
      diffeomorphismBosonProjection period hPeriod (metric .plus) output) ∈ _ at h
    rwa [diffeomorphismGhostBoson_decomposition, diffeomorphismGhostBoson_decomposition] at h

theorem hessianL2Maximal_graph_iff_ghost_boson
    (input output : DiffeomorphismL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianL2Maximal period hPeriod reference metric couplings).graph ↔
      ((diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict input,
       (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict output) ∈
        (hessianGhostReducedAdjoint period hPeriod reference metric couplings).graph ∧
      ((diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict input,
       (diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict output) ∈
        (hessianBosonReducedAdjoint period hPeriod reference metric couplings).graph := by
  rw [hessianGhostReducedAdjoint_graph_iff, hessianBosonReducedAdjoint_graph_iff]
  change (input, output) ∈ (hessianL2Maximal period hPeriod reference metric couplings).graph ↔
    (diffeomorphismGhostProjection period hPeriod (metric .plus) input,
     diffeomorphismGhostProjection period hPeriod (metric .plus) output) ∈
      (hessianL2Maximal period hPeriod reference metric couplings).graph ∧
    (diffeomorphismBosonProjection period hPeriod (metric .plus) input,
     diffeomorphismBosonProjection period hPeriod (metric .plus) output) ∈
      (hessianL2Maximal period hPeriod reference metric couplings).graph
  constructor
  · intro h
    exact ⟨hessianL2Maximal_graph_ghost period hPeriod reference metric couplings _ h,
      hessianL2Maximal_graph_boson period hPeriod reference metric couplings _ h⟩
  · rintro ⟨hGhost, hBoson⟩
    have h := (hessianL2Maximal period hPeriod reference metric couplings).graph.add_mem hGhost hBoson
    change (diffeomorphismGhostProjection period hPeriod (metric .plus) input +
      diffeomorphismBosonProjection period hPeriod (metric .plus) input,
      diffeomorphismGhostProjection period hPeriod (metric .plus) output +
      diffeomorphismBosonProjection period hPeriod (metric .plus) output) ∈ _ at h
    rwa [diffeomorphismGhostBoson_decomposition, diffeomorphismGhostBoson_decomposition] at h

end
end JanusFormal.P0EFTJanusProgramPT12HessianReducedGraphSplit4D