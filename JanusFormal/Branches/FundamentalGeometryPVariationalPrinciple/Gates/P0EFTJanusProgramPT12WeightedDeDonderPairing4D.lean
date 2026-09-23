import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostDiagonal4D

/-! Actual weighted de Donder column and its smooth transpose between metric and B components. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderPairing4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12DeDonderRowAdjoint4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

open P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
open P0EFTJanusProgramPT12RegularGhostL2Recovery4D
open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FaddeevPopovL2Core4D
open P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusProgramPT12FrameCovectorL2Transport4D
open P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
open P0EFTJanusProgramPT12RegularGhostL2Equiv4D
open P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
open P0EFTJanusProgramPT12DeDonderL2Closed4D

open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
open P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
open P0EFTJanusProgramPT12SignedBRSTGram4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace

open P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
open P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

open P0EFTJanusProgramPT12HessianGhostSmooth4D
open P0EFTJanusProgramPT12HessianSmoothRiesz4D
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12HessianGhostCommutation4D
open P0EFTJanusProgramPT12HessianL2OperatorCore4D
open P0EFTJanusProgramPT12HessianL2OperatorClosed4D

open P0EFTJanusProgramPT12HessianGhostMinimal4D
open P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D

open P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

local instance metricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismMetricProjection period hPeriod (metric .plus)).range
local instance auxiliaryInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2).range

open P0EFTJanusProgramPT12WeightedDeDonderSmooth4D
open P0EFTJanusProgramPT12HessianGhostDiagonal4D

theorem metricTransfer_deDonder (sector : Sector) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFeaturesSmooth period hPeriod metric (diffeomorphismMetricTransfer period hPeriod (metric .plus) field) (0, sector)).val =
      (hessianFeaturesSmooth period hPeriod metric field (0, sector)).val := by
  rw [hessianFeaturesSmooth_deDonder, hessianFeaturesSmooth_deDonder, diffeomorphismMetricTransfer_metric]

theorem metricTransfer_B (sector : Sector) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 (diffeomorphismL2Smooth period hPeriod (metric .plus) (diffeomorphismMetricTransfer period hPeriod (metric .plus) field)) = 0 := by
  rw [sectorTripletL2_smooth]
  change globalNormalizedVectorFrameL2LinearMap period hPeriod (metric sector)
    (diffeomorphismMetricTransfer period hPeriod (metric .plus) field).nonminimal.nakanishiLautrup.field = 0
  rw [diffeomorphismMetricTransfer_B]
  exact map_zero _

theorem metricTransfer_BFlat (sector : Sector) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (diffeomorphismMetricTransfer period hPeriod (metric .plus) field)) = 0 := by
  rw [sectorTripletFlatL2_smooth]
  change globalSmoothMetricFlatFrameL2LinearMap period hPeriod (metric sector)
    (diffeomorphismMetricTransfer period hPeriod (metric .plus) field).nonminimal.nakanishiLautrup.field = 0
  rw [diffeomorphismMetricTransfer_B]
  exact map_zero _

theorem metricTransfer_antighost (sector : Sector) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (diffeomorphismMetricTransfer period hPeriod (metric .plus) field)) = 0 := by
  rw [sectorTripletL2_smooth]
  change globalNormalizedVectorFrameL2LinearMap period hPeriod (metric sector)
    (diffeomorphismMetricTransfer period hPeriod (metric .plus) field).nonminimal.antighost.field = 0
  rw [diffeomorphismMetricTransfer_antighost]
  exact map_zero _

theorem auxiliaryTransfer_B (sector : Sector) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 (diffeomorphismL2Smooth period hPeriod (metric .plus) (diffeomorphismTripletTransfer period hPeriod 2 2 field)) =
      sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 (diffeomorphismL2Smooth period hPeriod (metric .plus) field) := by
  rw [sectorTripletL2_smooth, sectorTripletL2_smooth]
  rfl

theorem hessianSectorForm_metric_auxiliary (sector : Sector) (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianSectorForm period hPeriod reference metric sector
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismMetricTransfer period hPeriod (metric .plus) first))
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 2 2 second)) =
    inner Real (hessianFeaturesSmooth period hPeriod metric first (0, sector)).val
      (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) := by
  simp only [hessianSectorForm, hessianFeatureMinimal_smooth]
  simp only [hessianFeatureSmoothDomain, metricTransfer_deDonder, metricTransfer_B,
    metricTransfer_BFlat, metricTransfer_antighost, auxiliaryTransfer_B,
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 2 2 1 (by decide),
    inner_zero_left, inner_zero_right, mul_zero, add_zero, sub_zero]

attribute [local irreducible] hessianSmoothRiesz

theorem weightedDeDonderSmooth_pairing_form (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (weightedDeDonderSmooth period hPeriod reference metric couplings first)
      (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2 second) =
    hessianL2Form period hPeriod reference metric couplings
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismMetricTransfer period hPeriod (metric .plus) first))
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 2 2 second)) := by
  change inner Real
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2
      (hessianSmoothRiesz period hPeriod reference metric couplings (diffeomorphismMetricTransfer period hPeriod (metric .plus) first)))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) = _
  rw [diffeomorphismTripletL2_pairing, diffeomorphismTripletL2_comp_apply, diffeomorphismTripletL2_smooth]
  exact hessianSmoothRiesz_pairing period hPeriod reference metric couplings (diffeomorphismMetricTransfer period hPeriod (metric .plus) first)
    (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 2 2 second))

def weightedDeDonderSectorPairing (sector : Sector) (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) : Real :=
  inner Real (hessianFeaturesSmooth period hPeriod metric first (0, sector)).val
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 (diffeomorphismL2Smooth period hPeriod (metric .plus) second))

theorem weightedDeDonderSmooth_pairing_cross (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (weightedDeDonderSmooth period hPeriod reference metric couplings first)
      (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2 second) =
    candidateAPlusEinsteinKineticWeight couplings *
      weightedDeDonderSectorPairing period hPeriod reference metric .plus first second +
    candidateAMinusEinsteinKineticWeight couplings *
      weightedDeDonderSectorPairing period hPeriod reference metric .minus first second := by
  rw [weightedDeDonderSmooth_pairing_form, hessianL2Form,
    hessianSectorForm_metric_auxiliary, hessianSectorForm_metric_auxiliary]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderPairing4D
