import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Joint smooth de Donder and Faddeev--Popov features of the actual diagonal BRST state. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
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

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
variable (reference : RegularGeneralLorentzMetric period hPeriod)

abbrev HessianFeatureL2 := PiLp 2 fun _ : Fin 2 × Sector => ActualFPCovectorL2 period hPeriod

def hessianCovectorFeature (index : Fin 2 × Sector) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real] ActualSmoothCovector period hPeriod :=
  if index.1 = 0 then
    (globalGeneralMetricDeDonderLinearMap period hPeriod (metric index.2)).comp
      ((globalDiffeomorphismMetricPerturbationProjectionLinearMap period hPeriod).comp
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod index.2))
  else
    (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod (metric index.2)).comp
      ((globalDiffeomorphismGhostProjectionLinearMap period hPeriod).comp
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .plus))

def hessianFeaturesSmooth : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    HessianFeatureL2 period hPeriod where
  toFun field := WithLp.toLp 2 fun index => frameCovectorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)
    (hessianCovectorFeature period hPeriod metric index field)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact ((frameCovectorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).comp
      (hessianCovectorFeature period hPeriod metric index)).map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact ((frameCovectorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).comp
      (hessianCovectorFeature period hPeriod metric index)).map_smul scalar field

theorem hessianFeaturesSmooth_deDonder (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (sector : Sector) :
    (hessianFeaturesSmooth period hPeriod metric field (0, sector)).val =
      globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod (metric sector) (field.metricPerturbation sector) := rfl

theorem hessianFeaturesSmooth_fp (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (sector : Sector) :
    hessianFeaturesSmooth period hPeriod metric field (1, sector) =
      actualFPSmoothOutput period hPeriod metric field.nonminimal.ghost sector := rfl

private def hessianSmoothEquivDomain : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ≃ₗ[Real]
    (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  LinearEquiv.ofInjective (diffeomorphismL2Smooth period hPeriod (metric .plus))
    (diffeomorphismL2Smooth_injective period hPeriod (metric .plus))

def hessianFeatureCore : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real] HessianFeatureL2 period hPeriod where
  domain := (diffeomorphismL2Smooth period hPeriod (metric .plus)).range
  toFun := (hessianFeaturesSmooth period hPeriod metric).comp (hessianSmoothEquivDomain period hPeriod metric).symm.toLinearMap

theorem hessianFeatureCore_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianFeatureCore period hPeriod metric ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field, ⟨field, rfl⟩⟩ =
      hessianFeaturesSmooth period hPeriod metric field := by
  change hessianFeaturesSmooth period hPeriod metric
    ((hessianSmoothEquivDomain period hPeriod metric).symm ((hessianSmoothEquivDomain period hPeriod metric) field)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem hessianFeatureCore_deDonder_pairing (field : (hessianFeatureCore period hPeriod metric).domain)
    (sector : Sector) (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real ((hessianFeatureCore period hPeriod metric field (0, sector)).val row)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (diffeomorphismTensorReadout period hPeriod (metric .plus) sector field.val)
      (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) (metric sector) reference row test) := by
  rcases field with ⟨field, hField⟩
  obtain ⟨smooth, rfl⟩ := hField
  rw [hessianFeatureCore_smooth, hessianFeaturesSmooth_deDonder, diffeomorphismTensorReadout_smooth]
  exact deDonderL2_smooth_pairing period hPeriod (metric sector) reference (smooth.metricPerturbation sector) row test

theorem hessianFeatureCore_fp_pairing (field : (hessianFeatureCore period hPeriod metric).domain)
    (sector : Sector) (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (actualFPCovectorRecovery period hPeriod reference (hessianFeatureCore period hPeriod metric field (1, sector)) row)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (regularGhostL2Recovery period hPeriod reference (metric .plus)
      (diffeomorphismTripletReadout period hPeriod (metric .plus) 0 field.val))
      (fpRowAdjointTest period hPeriod reference (metric sector) row test) := by
  rcases field with ⟨field, hField⟩
  obtain ⟨smooth, rfl⟩ := hField
  rw [hessianFeatureCore_smooth, hessianFeaturesSmooth_fp, actualFPCovectorRecovery_smooth,
    diffeomorphismTripletReadout_smooth, regularGhostL2Recovery_actual]
  exact fpSmoothRow_pairing period hPeriod reference (metric sector) smooth.nonminimal.ghost.field row test

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
