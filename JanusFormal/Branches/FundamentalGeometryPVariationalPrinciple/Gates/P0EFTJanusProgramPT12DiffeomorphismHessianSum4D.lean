import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GhostBosonIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalProductAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderExtension4D
/-! Exact ghost / metric–B splitting of the full minimal and maximal Hessian graphs. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianSum4D
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

attribute [local irreducible] weightedFPActualGhostBlock weightedDeDonderBosonHessian

def diffeomorphismHessianSum : GhostBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real] GhostBosonPairL2 period hPeriod (metric .plus) :=
  diagonalProductOperator (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (weightedFPActualGhostBlock period hPeriod reference metric couplings) (weightedDeDonderBosonHessian period hPeriod reference metric couplings)

theorem diffeomorphismHessianSum_selfAdjoint : IsSelfAdjoint (diffeomorphismHessianSum period hPeriod reference metric couplings) :=
  @diagonalProductOperator_selfAdjoint (DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    _ (ghostInnerProductSpace period hPeriod metric) _
    _ (bosonInnerProductSpace period hPeriod metric) _ (weightedFPActualGhostBlock period hPeriod reference metric couplings) (weightedDeDonderBosonHessian period hPeriod reference metric couplings)
    (weightedFPActualGhostBlock_selfAdjoint period hPeriod reference metric couplings) (weightedDeDonderBosonHessian_selfAdjoint period hPeriod reference metric couplings)

attribute [local irreducible] diagonalProductOperator diffeomorphismHessianSum

theorem diffeomorphismHessianSum_graph_iff (input output : GhostBosonPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (diffeomorphismHessianSum period hPeriod reference metric couplings).graph ↔
      (input.fst, output.fst) ∈ (weightedFPActualGhostBlock period hPeriod reference metric couplings).graph ∧ (input.snd, output.snd) ∈ (weightedDeDonderBosonHessian period hPeriod reference metric couplings).graph := by
  unfold diffeomorphismHessianSum
  exact diagonalProductOperator_mem_graph_iff (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (weightedFPActualGhostBlock period hPeriod reference metric couplings) (weightedDeDonderBosonHessian period hPeriod reference metric couplings) input output

theorem diffeomorphismHessianSum_domain_iff (input : GhostBosonPairL2 period hPeriod (metric .plus)) :
    input ∈ (diffeomorphismHessianSum period hPeriod reference metric couplings).domain ↔
      input.fst ∈ (weightedFPActualGhostBlock period hPeriod reference metric couplings).domain ∧ input.snd ∈ (weightedDeDonderBosonHessian period hPeriod reference metric couplings).domain := by
  unfold diffeomorphismHessianSum
  exact diagonalProductOperator_domain_iff (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (weightedFPActualGhostBlock period hPeriod reference metric couplings) (weightedDeDonderBosonHessian period hPeriod reference metric couplings) input

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianSum4D
