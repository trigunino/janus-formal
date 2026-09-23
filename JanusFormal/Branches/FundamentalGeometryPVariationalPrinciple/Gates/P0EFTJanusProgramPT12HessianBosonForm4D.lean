import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonReduced4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMinimal4D

/-! Exact metric–B smooth Hessian: de Donder cross terms and the bounded auxiliary mass. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianBosonForm4D
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

open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D

open P0EFTJanusProgramPT12HessianBosonReduced4D

theorem hessianBosonSmooth_deDonder (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFeaturesSmooth period hPeriod metric (hessianBosonSmooth period hPeriod field) (0, sector)).val =
      (hessianFeaturesSmooth period hPeriod metric field (0, sector)).val := by
  change ((hessianFeaturesSmooth period hPeriod metric)
    (field - hessianGhostSmooth period hPeriod field) (0, sector)).val = _
  rw [map_sub]
  change (hessianFeaturesSmooth period hPeriod metric field (0, sector)).val -
    (hessianFeaturesSmooth period hPeriod metric (hessianGhostSmooth period hPeriod field) (0, sector)).val = _
  rw [hessianGhostSmooth_deDonder, sub_zero]

theorem hessianBosonSmooth_fp (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFeaturesSmooth period hPeriod metric (hessianBosonSmooth period hPeriod field) (1, sector)).val = 0 := by
  change ((hessianFeaturesSmooth period hPeriod metric)
    (field - hessianGhostSmooth period hPeriod field) (1, sector)).val = _
  rw [map_sub]
  change (hessianFeaturesSmooth period hPeriod metric field (1, sector)).val -
    (hessianFeaturesSmooth period hPeriod metric (hessianGhostSmooth period hPeriod field) (1, sector)).val = _
  rw [hessianGhostSmooth_fp, sub_self]

theorem hessianBosonSmooth_B (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (hessianBosonSmooth period hPeriod field)) =
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field) := by
  rw [← hessianBosonSmooth_L2]
  change sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
    (diffeomorphismL2Smooth period hPeriod (metric .plus) field -
      diffeomorphismGhostProjection period hPeriod (metric .plus)
        (diffeomorphismL2Smooth period hPeriod (metric .plus) field)) = _
  rw [map_sub, hessianGhostSmooth_L2, hessianGhostSmooth_B, sub_zero]

theorem hessianBosonSmooth_BFlat (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (hessianBosonSmooth period hPeriod field)) =
    sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field) := by
  rw [← hessianBosonSmooth_L2]
  change sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
    (diffeomorphismL2Smooth period hPeriod (metric .plus) field -
      diffeomorphismGhostProjection period hPeriod (metric .plus)
        (diffeomorphismL2Smooth period hPeriod (metric .plus) field)) = _
  rw [map_sub, hessianGhostSmooth_L2, hessianGhostSmooth_BFlat, sub_zero]

theorem hessianBosonSmooth_antighost (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
      (diffeomorphismL2Smooth period hPeriod (metric .plus) (hessianBosonSmooth period hPeriod field)) = 0 := by
  rw [← hessianBosonSmooth_L2]
  change sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
    (diffeomorphismL2Smooth period hPeriod (metric .plus) field -
      diffeomorphismGhostProjection period hPeriod (metric .plus)
        (diffeomorphismL2Smooth period hPeriod (metric .plus) field)) = _
  rw [map_sub, hessianGhostSmooth_L2, hessianGhostSmooth_antighost, sub_self]

theorem hessianSectorForm_boson_eq_cross_add_mass (sector : Sector)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianSectorForm period hPeriod reference metric sector
      (hessianFeatureSmoothDomain period hPeriod metric (hessianBosonSmooth period hPeriod first))
      (hessianFeatureSmoothDomain period hPeriod metric (hessianBosonSmooth period hPeriod second)) =
    inner Real (hessianFeaturesSmooth period hPeriod metric first (0, sector)).val
      (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
        (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) +
    inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
        (diffeomorphismL2Smooth period hPeriod (metric .plus) first))
      (hessianFeaturesSmooth period hPeriod metric second (0, sector)).val +
    inner Real (auxiliarySectorL2Riesz period hPeriod reference metric sector
      (diffeomorphismL2Smooth period hPeriod (metric .plus) first))
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) := by
  simp only [hessianSectorForm, hessianFeatureMinimal_smooth]
  simp only [hessianFeatureSmoothDomain, hessianBosonSmooth_deDonder, hessianBosonSmooth_B,
    hessianBosonSmooth_BFlat, hessianBosonSmooth_antighost, inner_zero_left, inner_zero_right,
    sub_zero, auxiliarySectorL2Riesz_pairing]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12HessianBosonForm4D