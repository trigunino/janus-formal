import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BosonDeDonderPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderComponentBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapAdjoint4D

/-! Self-adjoint weighted de Donder block on the metric and B Hilbert components. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderActualCore4D
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

open P0EFTJanusProgramPT12WeightedDeDonderBlock4D
open P0EFTJanusProgramPT12WeightedDeDonderPairing4D
open P0EFTJanusProgramPT12BosonDeDonderCore4D
open P0EFTJanusProgramPT12BosonDeDonderPairing4D
open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
open P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D

private theorem weighted_cross_sum (a b x y u v : Real) :
    (a * u + b * v) + (a * x + b * y) = a * (x + u) + b * (y + v) := by ring

theorem weightedDeDonderAssemble_smooth_input (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (metricBAuxiliaryIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2 (diffeomorphismMetricSmooth period hPeriod (metric .plus) field, diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2 field)) =
    diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field := by
  apply Subtype.ext
  change diffeomorphismMetricProjection period hPeriod (metric .plus)
    (diffeomorphismL2Smooth period hPeriod (metric .plus) field) +
    diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field) =
    diffeomorphismBosonProjection period hPeriod (metric .plus)
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field)
  exact diffeomorphismMetricAuxiliary_decomposition period hPeriod (metric .plus) _

theorem bosonDeDonderSectorPairing_eq_weightedCross (sector : Sector) (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    bosonDeDonderSectorPairing period hPeriod reference metric sector first second =
      weightedDeDonderSectorPairing period hPeriod reference metric sector first second +
      weightedDeDonderSectorPairing period hPeriod reference metric sector second first := by
  unfold bosonDeDonderSectorPairing weightedDeDonderSectorPairing
  congr 1
  exact real_inner_comm _ _

attribute [local irreducible] weightedDeDonderSmooth weightedDeDonderTransposeSmooth
  diffeomorphismMetricSmooth diffeomorphismTripletComponentSmooth metricBAuxiliaryIsometry
  bosonDeDonderSmoothOutput

theorem weightedDeDonderAssemble_smooth_output (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (metricBAuxiliaryIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2 (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings field, weightedDeDonderSmooth period hPeriod reference metric couplings field)) =
    bosonDeDonderSmoothOutput period hPeriod reference metric couplings field := by
  apply @DenseRange.eq_of_inner_left (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) Real _ _
    (bosonInnerProductSpace period hPeriod metric) _ _
    (diffeomorphismBosonPairSmooth period hPeriod (metric .plus))
    (diffeomorphismBosonPairSmooth_denseRange period hPeriod (metric .plus))
  intro test
  rw [bosonDeDonderSmoothOutput_pairing]
  rw [← weightedDeDonderAssemble_smooth_input period hPeriod metric test,
    (metricBAuxiliaryIsometry period hPeriod (metric .plus)).inner_map_map]
  change inner Real (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings field) (diffeomorphismMetricSmooth period hPeriod (metric .plus) test) + inner Real (weightedDeDonderSmooth period hPeriod reference metric couplings field) (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2 test) = _
  rw [weightedDeDonderTransposeSmooth_pairing,
    real_inner_comm (weightedDeDonderSmooth period hPeriod reference metric couplings test) (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2 field), weightedDeDonderSmooth_pairing_cross,
    weightedDeDonderSmooth_pairing_cross, bosonDeDonderSectorPairing_eq_weightedCross,
    bosonDeDonderSectorPairing_eq_weightedCross]
  exact weighted_cross_sum _ _ _ _ _ _

theorem weightedDeDonderActualBosonBlock_reduced_smooth_graph (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field,
     bosonDeDonderSmoothOutput period hPeriod reference metric couplings field) ∈
      (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings).graph := by
  have h := weightedDeDonderActualBosonBlock_smooth_graph period hPeriod reference metric couplings field field
  rw [weightedDeDonderAssemble_smooth_input, weightedDeDonderAssemble_smooth_output] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderActualCore4D
