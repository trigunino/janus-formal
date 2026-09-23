import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderComponentBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapAdjoint4D

/-! Self-adjoint weighted de Donder block on the metric and B Hilbert components. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderBlock4D
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
open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
open P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D
open P0EFTJanusProgramPT12WeightedDeDonderSmooth4D
open P0EFTJanusProgramPT12WeightedDeDonderClosed4D
open P0EFTJanusProgramPT12RectangularOffDiagonal4D
open P0EFTJanusProgramPT12RectangularSelfAdjoint4D
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

open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
local instance metricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismMetricProjection period hPeriod (metric .plus)).range

local instance auxiliaryInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2).range

local instance bosonInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)).range

local instance componentPairInnerProductSpace :
    InnerProductSpace Real (MetricBAuxiliaryPairL2 period hPeriod (metric .plus)) :=
  @WithLp.instProdInnerProductSpace Real
    (DiffeomorphismMetricL2 period hPeriod (metric .plus))
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2)
    _ _ (metricInnerProductSpace period hPeriod metric)
    _ (auxiliaryInnerProductSpace period hPeriod metric)
local instance componentBlockStar :
    Star (MetricBAuxiliaryPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      MetricBAuxiliaryPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := MetricBAuxiliaryPairL2 period hPeriod (metric .plus))

local instance actualBosonBlockStar :
    Star (DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
open P0EFTJanusProgramPT12WeightedDeDonderClosed4D

open P0EFTJanusProgramPT12WeightedDeDonderComponentBlock4D

attribute [local irreducible] weightedDeDonderComponentBlock transportedPMap metricBAuxiliaryIsometry

def weightedDeDonderActualBosonBlock :
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  transportedPMap
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (F := MetricBAuxiliaryPairL2 period hPeriod (metric .plus))
    (metricBAuxiliaryIsometry period hPeriod (metric .plus)).symm
    (weightedDeDonderComponentBlock period hPeriod reference metric couplings)

theorem weightedDeDonderActualBosonBlock_selfAdjoint :
    IsSelfAdjoint (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings) :=
  @transportedPMap_selfAdjoint
    (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (MetricBAuxiliaryPairL2 period hPeriod (metric .plus))
    _ (bosonInnerProductSpace period hPeriod metric) _
    _ (componentPairInnerProductSpace period hPeriod metric) _
    (metricBAuxiliaryIsometry period hPeriod (metric .plus)).symm
    (weightedDeDonderComponentBlock period hPeriod reference metric couplings)
    (weightedDeDonderComponentBlock_selfAdjoint period hPeriod reference metric couplings)

theorem weightedDeDonderActualBosonBlock_graph_iff
    (input output : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings).graph ↔
      ((metricBAuxiliaryIsometry period hPeriod (metric .plus)).symm input,
       (metricBAuxiliaryIsometry period hPeriod (metric .plus)).symm output) ∈
        (weightedDeDonderComponentBlock period hPeriod reference metric couplings).graph :=
  @transportedPMap_graph_iff
    (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (MetricBAuxiliaryPairL2 period hPeriod (metric .plus))
    _ (bosonInnerProductSpace period hPeriod metric)
    _ (componentPairInnerProductSpace period hPeriod metric)
    (metricBAuxiliaryIsometry period hPeriod (metric .plus)).symm
    (weightedDeDonderComponentBlock period hPeriod reference metric couplings) input output

theorem weightedDeDonderActualBosonBlock_smooth_graph
    (metricField auxiliaryField : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ((metricBAuxiliaryIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2
        (diffeomorphismMetricSmooth period hPeriod (metric .plus) metricField,
         diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2 auxiliaryField)),
     (metricBAuxiliaryIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2
        (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings auxiliaryField,
         weightedDeDonderSmooth period hPeriod reference metric couplings metricField))) ∈
      (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings).graph := by
  rw [weightedDeDonderActualBosonBlock_graph_iff, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  exact weightedDeDonderComponentBlock_smooth_graph period hPeriod reference metric couplings metricField auxiliaryField
end
end JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderBlock4D


