import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPComponentBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapAdjoint4D

/-! Canonical weighted FP block in the actual ghost Hilbert spaces. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedFPBlock4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
open P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
open P0EFTJanusProgramPT12WeightedFPSmooth4D
open P0EFTJanusProgramPT12WeightedFPClosed4D
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
open P0EFTJanusProgramPT12IsometricPMapTransport4D
open P0EFTJanusProgramPT12IsometricPMapAdjoint4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
variable (couplings : GlobalCandidateAActionCouplings)

local instance componentInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0).range

local instance ghostPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismGhostProjection period hPeriod (metric .plus)).range

local instance componentPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus)) :=
  @WithLp.instProdInnerProductSpace Real
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (componentInnerProductSpace period hPeriod metric)
    _ (componentInnerProductSpace period hPeriod metric)
local instance componentBlockStar :
    Star (DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus))

local instance actualGhostBlockStar :
    Star (DiffeomorphismGhostPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
open P0EFTJanusProgramPT12WeightedFPComponentBlock4D

attribute [local irreducible] weightedFPComponentBlock transportedPMap diffeomorphismGhostPairIsometry

def weightedFPActualGhostBlock :
    DiffeomorphismGhostPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismGhostPairL2 period hPeriod (metric .plus) :=
  transportedPMap
    (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
    (F := DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus))
    (diffeomorphismGhostPairIsometry period hPeriod (metric .plus)).symm
    (weightedFPComponentBlock period hPeriod reference metric couplings)

theorem weightedFPActualGhostBlock_selfAdjoint :
    IsSelfAdjoint (weightedFPActualGhostBlock period hPeriod reference metric couplings) :=
  @transportedPMap_selfAdjoint
    (DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
    (DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus))
    _ (ghostPairInnerProductSpace period hPeriod metric) _
    _ (componentPairInnerProductSpace period hPeriod metric) _
    (diffeomorphismGhostPairIsometry period hPeriod (metric .plus)).symm
    (weightedFPComponentBlock period hPeriod reference metric couplings)
    (weightedFPComponentBlock_selfAdjoint period hPeriod reference metric couplings)

theorem weightedFPActualGhostBlock_graph_iff
    (input output : DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (weightedFPActualGhostBlock period hPeriod reference metric couplings).graph ↔
      ((diffeomorphismGhostPairIsometry period hPeriod (metric .plus)).symm input,
       (diffeomorphismGhostPairIsometry period hPeriod (metric .plus)).symm output) ∈
        (weightedFPComponentBlock period hPeriod reference metric couplings).graph :=
  @transportedPMap_graph_iff
    (DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
    (DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus))
    _ (ghostPairInnerProductSpace period hPeriod metric)
    _ (componentPairInnerProductSpace period hPeriod metric)
    (diffeomorphismGhostPairIsometry period hPeriod (metric .plus)).symm
    (weightedFPComponentBlock period hPeriod reference metric couplings) input output

theorem weightedFPActualGhostBlock_smooth_graph
    (ghost antighost : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ((diffeomorphismGhostPairIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2
        (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 ghost,
         diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 antighost)),
     (diffeomorphismGhostPairIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2
        (weightedFPTransposeSmooth period hPeriod reference metric couplings antighost,
         weightedFPSmooth period hPeriod reference metric couplings ghost))) ∈
      (weightedFPActualGhostBlock period hPeriod reference metric couplings).graph := by
  rw [weightedFPActualGhostBlock_graph_iff, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  exact weightedFPComponentBlock_smooth_graph period hPeriod reference metric couplings ghost antighost
end
end JanusFormal.P0EFTJanusProgramPT12WeightedFPBlock4D
