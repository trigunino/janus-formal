import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianSmoothRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D

/-! The actual smooth ghost projection preserves FP and kills metric/multiplier features. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianGhostSmooth4D
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

open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

def hessianGhostSmooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod :=
  { metricPerturbation := 0
    nonminimal :=
      { ghost := field.nonminimal.ghost
        antighost := field.nonminimal.antighost
        nakanishiLautrup := ⟨0⟩ } }

theorem hessianGhostSmooth_eq_transfer (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletTransfer period hPeriod 0 0 field + diffeomorphismTripletTransfer period hPeriod 1 1 field =
      hessianGhostSmooth period hPeriod field := by
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · change (0 : GlobalMetricPerturbationPair period hPeriod) + 0 = 0
    exact add_zero _
  · apply GlobalDiffeomorphismNonminimalFields.ext
    · apply GlobalDiffeomorphismGhostField.ext
      change field.nonminimal.ghost.field + 0 = field.nonminimal.ghost.field
      exact add_zero _
    · apply GlobalDiffeomorphismAntighostField.ext
      change 0 + field.nonminimal.antighost.field = field.nonminimal.antighost.field
      exact zero_add _
    · apply GlobalDiffeomorphismNakanishiLautrupField.ext
      change (0 : SmoothTangentField period hPeriod) + 0 = 0
      exact add_zero _

theorem hessianGhostSmooth_L2 (normalization : SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismGhostProjection period hPeriod normalization (diffeomorphismL2Smooth period hPeriod normalization field) =
      diffeomorphismL2Smooth period hPeriod normalization (hessianGhostSmooth period hPeriod field) := by
  rw [diffeomorphismGhostProjection_smooth, hessianGhostSmooth_eq_transfer]

theorem hessianGhostSmooth_deDonder (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFeaturesSmooth period hPeriod metric (hessianGhostSmooth period hPeriod field) (0, sector)).val = 0 := by
  rw [hessianFeaturesSmooth_deDonder]
  exact (globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod (metric sector)).map_zero

theorem hessianGhostSmooth_fp (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianFeaturesSmooth period hPeriod metric (hessianGhostSmooth period hPeriod field) (1, sector) =
      hessianFeaturesSmooth period hPeriod metric field (1, sector) := rfl

theorem hessianGhostSmooth_B (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (hessianGhostSmooth period hPeriod field)) = 0 := by
  rw [sectorTripletL2_smooth]
  exact (globalNormalizedVectorFrameL2LinearMap period hPeriod (metric sector)).map_zero

theorem hessianGhostSmooth_BFlat (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (hessianGhostSmooth period hPeriod field)) = 0 := by
  rw [sectorTripletFlatL2_smooth]
  exact (globalSmoothMetricFlatFrameL2LinearMap period hPeriod (metric sector)).map_zero

theorem hessianGhostSmooth_antighost (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (hessianGhostSmooth period hPeriod field)) =
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field) := by
  rw [sectorTripletL2_smooth, sectorTripletL2_smooth]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12HessianGhostSmooth4D