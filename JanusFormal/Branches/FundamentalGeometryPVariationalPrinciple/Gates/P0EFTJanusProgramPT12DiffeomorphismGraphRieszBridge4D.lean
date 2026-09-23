import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGraphToL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianReducedGraphSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GhostBosonIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalProductAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderExtension4D
/-! Exact ghost / metric–B splitting of the full minimal and maximal Hessian graphs. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGraphRieszBridge4D
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

open P0EFTJanusProgramPT12DiffeomorphismHessianExtension4D
open P0EFTJanusProgramPT12DiffeomorphismGraphToL24D
open P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace
attribute [local irreducible] hessianSmoothRiesz diffeomorphismGraphToL2 diagonalDiffeomorphismSignedRiesz

theorem hessianSmoothRiesz_graph_pairing
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
    (test : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    inner Real (hessianSmoothRiesz period hPeriod reference metric couplings field)
      (diffeomorphismGraphToL2 period hPeriod metric test) =
    inner Real (diagonalDiffeomorphismSignedRiesz period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric field)) test := by
  refine (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange
    period hPeriod metric).induction_on test ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro smooth
    rw [diffeomorphismGraphToL2_smooth, hessianSmoothRiesz_actual_pairing,
      diagonalDiffeomorphismSignedRiesz_smooth_pairing]

theorem hessianSmoothRiesz_graph_adjoint
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismGraphToL2 period hPeriod metric).adjoint
      (hessianSmoothRiesz period hPeriod reference metric couplings field) =
    diagonalDiffeomorphismSignedRiesz period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric field) := by
  apply ext_inner_right Real
  intro test
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact hessianSmoothRiesz_graph_pairing period hPeriod reference metric couplings field test

theorem diffeomorphismHessianRealization_graph_pairing
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
    (test : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    inner Real (diffeomorphismHessianRealization period hPeriod reference metric couplings
      (diffeomorphismHessianRealizationSmoothDomain period hPeriod reference metric couplings field))
      (diffeomorphismGraphToL2 period hPeriod metric test) =
    inner Real (diagonalDiffeomorphismSignedRiesz period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric field)) test := by
  rw [diffeomorphismHessianRealization_smooth]
  exact hessianSmoothRiesz_graph_pairing period hPeriod reference metric couplings field test

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGraphRieszBridge4D
