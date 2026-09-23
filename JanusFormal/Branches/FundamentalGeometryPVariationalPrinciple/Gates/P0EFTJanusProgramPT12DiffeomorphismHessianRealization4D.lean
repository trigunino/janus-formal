import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GhostBosonIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalProductAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderExtension4D
/-! Exact ghost / metric–B splitting of the full minimal and maximal Hessian graphs. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianRealization4D
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

attribute [local irreducible] diffeomorphismHessianSum transportedPMap ghostBosonIsometry

def diffeomorphismHessianRealization : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real] DiffeomorphismL2 period hPeriod (metric .plus) :=
  transportedPMap (E := DiffeomorphismL2 period hPeriod (metric .plus)) (F := GhostBosonPairL2 period hPeriod (metric .plus))
    (ghostBosonIsometry period hPeriod (metric .plus)).symm (diffeomorphismHessianSum period hPeriod reference metric couplings)

theorem diffeomorphismHessianRealization_selfAdjoint :
    IsSelfAdjoint (diffeomorphismHessianRealization period hPeriod reference metric couplings) :=
  @transportedPMap_selfAdjoint (DiffeomorphismL2 period hPeriod (metric .plus)) (GhostBosonPairL2 period hPeriod (metric .plus))
    _ (fullInnerProductSpace period hPeriod metric) _
    _ (pairInnerProductSpace period hPeriod metric) _
    (ghostBosonIsometry period hPeriod (metric .plus)).symm (diffeomorphismHessianSum period hPeriod reference metric couplings)
    (diffeomorphismHessianSum_selfAdjoint period hPeriod reference metric couplings)

theorem diffeomorphismHessianRealization_graph_iff (input output : DiffeomorphismL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (diffeomorphismHessianRealization period hPeriod reference metric couplings).graph ↔
      ((diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict input, (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict output) ∈ (weightedFPActualGhostBlock period hPeriod reference metric couplings).graph ∧
      ((diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict input, (diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict output) ∈ (weightedDeDonderBosonHessian period hPeriod reference metric couplings).graph := by
  have h := @transportedPMap_graph_iff
    (DiffeomorphismL2 period hPeriod (metric .plus)) (GhostBosonPairL2 period hPeriod (metric .plus))
    _ (fullInnerProductSpace period hPeriod metric) _ (pairInnerProductSpace period hPeriod metric)
    (ghostBosonIsometry period hPeriod (metric .plus)).symm
    (diffeomorphismHessianSum period hPeriod reference metric couplings) input output
  erw [ghostBosonIsometry_symm_apply period hPeriod (metric .plus) input,
    ghostBosonIsometry_symm_apply period hPeriod (metric .plus) output,
    diffeomorphismHessianSum_graph_iff] at h
  exact h
theorem diffeomorphismHessianRealization_domain_iff (input : DiffeomorphismL2 period hPeriod (metric .plus)) :
    input ∈ (diffeomorphismHessianRealization period hPeriod reference metric couplings).domain ↔
      (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict input ∈ (weightedFPActualGhostBlock period hPeriod reference metric couplings).domain ∧ (diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict input ∈ (weightedDeDonderBosonHessian period hPeriod reference metric couplings).domain := by
  unfold diffeomorphismHessianRealization transportedPMap
  change (ghostBosonIsometry period hPeriod (metric .plus)).symm input ∈
    (diffeomorphismHessianSum period hPeriod reference metric couplings).domain ↔ _
  rw [ghostBosonIsometry_symm_apply, diffeomorphismHessianSum_domain_iff]
  rfl

theorem diffeomorphismHessianRealization_isClosed :
    (diffeomorphismHessianRealization period hPeriod reference metric couplings).IsClosed :=
  @IsSelfAdjoint.isClosed Real (DiffeomorphismL2 period hPeriod (metric .plus)) _ _ (fullInnerProductSpace period hPeriod metric) _
    (diffeomorphismHessianRealization period hPeriod reference metric couplings) (diffeomorphismHessianRealization_selfAdjoint period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianRealization4D
