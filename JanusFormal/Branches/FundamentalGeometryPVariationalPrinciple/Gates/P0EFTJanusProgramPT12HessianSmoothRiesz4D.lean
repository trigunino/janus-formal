import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D
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

/-! Concrete original-L² BRST Hessian representatives for every actual smooth state. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianSmoothRiesz4D
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

def hessianSectorSmoothRiesz (sector : Sector) (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  ContinuousLinearMap.adjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (F := GlobalDiffeomorphismVectorL2 period hPeriod)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2)
      (hessianFeaturesSmooth period hPeriod metric field (0, sector)).val +
  deDonderTestRiesz period hPeriod reference metric sector
    (globalNormalizedVectorCoordinate period hPeriod (metric sector) field.nonminimal.nakanishiLautrup.field) -
  ContinuousLinearMap.adjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (F := GlobalDiffeomorphismVectorL2 period hPeriod)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1)
      (hessianFeaturesSmooth period hPeriod metric field (1, sector)).val -
  fpTestRiesz period hPeriod reference metric sector
    (globalNormalizedVectorCoordinate period hPeriod (metric sector) field.nonminimal.antighost.field) +
  auxiliarySectorL2Riesz period hPeriod reference metric sector (diffeomorphismL2Smooth period hPeriod (metric .plus) field)

theorem hessianSectorSmoothRiesz_pairing (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
    (test : (hessianFeatureMinimal period hPeriod metric).domain) :
    inner Real (hessianSectorSmoothRiesz period hPeriod reference metric sector field) test.val =
      hessianSectorForm period hPeriod reference metric sector
        (hessianFeatureSmoothDomain period hPeriod metric field) test := by
  have hB : smoothTestVector period hPeriod
      (globalNormalizedVectorCoordinate period hPeriod (metric sector) field.nonminimal.nakanishiLautrup.field) =
      sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
        (diffeomorphismL2Smooth period hPeriod (metric .plus) field) :=
    (sectorTripletL2_smooth period hPeriod reference (metric sector) (metric .plus) 2 field).symm
  have hC : smoothTestVector period hPeriod
      (globalNormalizedVectorCoordinate period hPeriod (metric sector) field.nonminimal.antighost.field) =
      sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
        (diffeomorphismL2Smooth period hPeriod (metric .plus) field) :=
    (sectorTripletL2_smooth period hPeriod reference (metric sector) (metric .plus) 1 field).symm
  simp only [hessianSectorSmoothRiesz, inner_add_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    deDonderTestRiesz_pairing, fpTestRiesz_pairing, auxiliarySectorL2Riesz_pairing, hB, hC,
    hessianSectorForm, hessianFeatureMinimal_smooth]
  change _ = inner Real (hessianFeaturesSmooth period hPeriod metric field (0, sector)).val
      (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 test.val) +
    inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field))
      (hessianFeatureMinimal period hPeriod metric test (0, sector)).val -
    (1 / 2 : Real) * inner Real (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field))
      (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 test.val) -
    (1 / 2 : Real) * inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field))
      (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 test.val) -
    inner Real (hessianFeaturesSmooth period hPeriod metric field (1, sector)).val
      (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 test.val) -
    inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1
      (diffeomorphismL2Smooth period hPeriod (metric .plus) field))
      (hessianFeatureMinimal period hPeriod metric test (1, sector)).val
  ring

def hessianSmoothRiesz (couplings : GlobalCandidateAActionCouplings)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) : DiffeomorphismL2 period hPeriod (metric .plus) :=
  candidateAPlusEinsteinKineticWeight couplings • hessianSectorSmoothRiesz period hPeriod reference metric .plus field +
    candidateAMinusEinsteinKineticWeight couplings • hessianSectorSmoothRiesz period hPeriod reference metric .minus field

theorem hessianSmoothRiesz_pairing (couplings : GlobalCandidateAActionCouplings)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
    (test : (hessianFeatureMinimal period hPeriod metric).domain) :
    inner Real (hessianSmoothRiesz period hPeriod reference metric couplings field) test.val =
      hessianL2Form period hPeriod reference metric couplings (hessianFeatureSmoothDomain period hPeriod metric field) test := by
  simp only [hessianSmoothRiesz, inner_add_left, hessianL2Form]
  apply congrArg₂ (· + ·)
  · exact (real_inner_smul_left (hessianSectorSmoothRiesz period hPeriod reference metric .plus field)
      test.val (candidateAPlusEinsteinKineticWeight couplings)).trans
        (congrArg (fun value => candidateAPlusEinsteinKineticWeight couplings * value)
          (hessianSectorSmoothRiesz_pairing period hPeriod reference metric .plus field test))
  · exact (real_inner_smul_left (hessianSectorSmoothRiesz period hPeriod reference metric .minus field)
      test.val (candidateAMinusEinsteinKineticWeight couplings)).trans
        (congrArg (fun value => candidateAMinusEinsteinKineticWeight couplings * value)
          (hessianSectorSmoothRiesz_pairing period hPeriod reference metric .minus field test))

theorem hessianSmoothRiesz_actual_pairing (couplings : GlobalCandidateAActionCouplings)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (hessianSmoothRiesz period hPeriod reference metric couplings first)
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings metric first second :=
  (hessianSmoothRiesz_pairing period hPeriod reference metric couplings first
    (hessianFeatureSmoothDomain period hPeriod metric second)).trans
      (hessianL2Form_smooth_eq_actual period hPeriod reference metric couplings first second)

end
end JanusFormal.P0EFTJanusProgramPT12HessianSmoothRiesz4D
