import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianReducedGraphSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GhostBosonIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalProductAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderExtension4D
/-! Exact ghost / metric–B splitting of the full minimal and maximal Hessian graphs. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianExtension4D
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

open P0EFTJanusProgramPT12GhostBosonIsometry4D
open P0EFTJanusProgramPT12DiagonalProductPMap4D
open P0EFTJanusProgramPT12DiagonalProductAdjoint4D
open P0EFTJanusProgramPT12WeightedFPBlock4D
open P0EFTJanusProgramPT12WeightedFPExtension4D
open P0EFTJanusProgramPT12WeightedDeDonderExtension4D

local instance ghostInnerProductSpace : InnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus)) (diffeomorphismGhostProjection period hPeriod (metric .plus)).range
local instance bosonInnerProductSpace : InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus)) (diffeomorphismBosonProjection period hPeriod (metric .plus)).range
local instance pairInnerProductSpace : InnerProductSpace Real (GhostBosonPairL2 period hPeriod (metric .plus)) :=
  @WithLp.instProdInnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    _ _ (ghostInnerProductSpace period hPeriod metric) _ (bosonInnerProductSpace period hPeriod metric)
local instance pairStar : Star (GhostBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real] GhostBosonPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real) (E := GhostBosonPairL2 period hPeriod (metric .plus))

open P0EFTJanusProgramPT12DiffeomorphismHessianSum4D
open P0EFTJanusProgramPT12IsometricPMapTransport4D
open P0EFTJanusProgramPT12IsometricPMapAdjoint4D

local instance fullInnerProductSpace : InnerProductSpace Real (DiffeomorphismL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2Ambient period hPeriod)
    (diffeomorphismL2Space period hPeriod (metric .plus))
local instance fullStar : Star (DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real] DiffeomorphismL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))

open P0EFTJanusProgramPT12DiffeomorphismHessianRealization4D
open P0EFTJanusProgramPT12HessianReducedGraphSplit4D
open P0EFTJanusProgramPT12HessianSmoothRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

attribute [local irreducible] diffeomorphismHessianRealization hessianL2Minimal hessianL2Maximal
  weightedFPActualGhostBlock weightedDeDonderBosonHessian
  hessianGhostReduced hessianBosonReduced hessianGhostReducedAdjoint hessianBosonReducedAdjoint
  diffeomorphismGhostProjection diffeomorphismBosonProjection

theorem hessianL2Minimal_le_realization : hessianL2Minimal period hPeriod reference metric couplings ≤ diffeomorphismHessianRealization period hPeriod reference metric couplings := by
  apply LinearPMap.le_of_le_graph
  intro pair hPair
  have h := (hessianL2Minimal_graph_iff_ghost_boson period hPeriod reference metric couplings pair.1 pair.2).mp hPair
  apply (diffeomorphismHessianRealization_graph_iff period hPeriod reference metric couplings pair.1 pair.2).mpr
  exact ⟨LinearPMap.le_graph_of_le (hessianGhostReduced_le_weightedFPBlock period hPeriod reference metric couplings) h.1,
    LinearPMap.le_graph_of_le (hessianBosonReduced_le_weightedDeDonderBosonHessian period hPeriod reference metric couplings) h.2⟩

theorem diffeomorphismHessianRealization_le_maximal :
    diffeomorphismHessianRealization period hPeriod reference metric couplings ≤ hessianL2Maximal period hPeriod reference metric couplings := by
  apply LinearPMap.le_of_le_graph
  intro pair hPair
  have h := (diffeomorphismHessianRealization_graph_iff period hPeriod reference metric couplings pair.1 pair.2).mp hPair
  apply (hessianL2Maximal_graph_iff_ghost_boson period hPeriod reference metric couplings pair.1 pair.2).mpr
  exact ⟨LinearPMap.le_graph_of_le (weightedFPBlock_le_hessianGhostReducedAdjoint period hPeriod reference metric couplings) h.1,
    LinearPMap.le_graph_of_le (weightedDeDonderBosonHessian_le_reducedAdjoint period hPeriod reference metric couplings) h.2⟩

theorem diffeomorphismHessianRealization_smooth_graph (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismL2Smooth period hPeriod (metric .plus) field,
      hessianSmoothRiesz period hPeriod reference metric couplings field) ∈ (diffeomorphismHessianRealization period hPeriod reference metric couplings).graph := by
  have h := (hessianL2Minimal period hPeriod reference metric couplings).mem_graph (hessianL2SmoothDomain period hPeriod reference metric couplings field)
  rw [hessianL2Minimal_smooth] at h
  exact LinearPMap.le_graph_of_le (hessianL2Minimal_le_realization period hPeriod reference metric couplings) h

def diffeomorphismHessianRealizationSmoothDomain (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismHessianRealization period hPeriod reference metric couplings).domain :=
  ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field,
    (hessianL2Minimal_le_realization period hPeriod reference metric couplings).1 (hessianL2SmoothDomain period hPeriod reference metric couplings field).property⟩

theorem diffeomorphismHessianRealization_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismHessianRealization period hPeriod reference metric couplings (diffeomorphismHessianRealizationSmoothDomain period hPeriod reference metric couplings field) =
      hessianSmoothRiesz period hPeriod reference metric couplings field :=
  ((hessianL2Minimal_le_realization period hPeriod reference metric couplings).2
    (x := hessianL2SmoothDomain period hPeriod reference metric couplings field)
    (y := diffeomorphismHessianRealizationSmoothDomain period hPeriod reference metric couplings field) rfl).symm.trans
      (hessianL2Minimal_smooth period hPeriod reference metric couplings field)

theorem diffeomorphismHessianRealization_actual_pairing (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (diffeomorphismHessianRealization period hPeriod reference metric couplings
      (diffeomorphismHessianRealizationSmoothDomain period hPeriod reference metric couplings first))
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) =
    globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction
      period hPeriod couplings metric first second := by
  rw [diffeomorphismHessianRealization_smooth]
  exact hessianSmoothRiesz_actual_pairing period hPeriod reference metric couplings first second

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianExtension4D
