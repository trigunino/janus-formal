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

/-! Concrete L² representatives of de Donder and FP pairings against arbitrary smooth coordinate tests. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D
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

abbrev OriginalCovectorTest := Fin (finiteSmoothTangentFrame period hPeriod).count → SmoothScalarField period hPeriod

def deDonderTestRiesz (sector : Sector) (test : OriginalCovectorTest period hPeriod) :
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  ContinuousLinearMap.adjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (F := GlobalGeneralMetricTensorFrameL2 period hPeriod)
    (diffeomorphismTensorReadout period hPeriod (metric .plus) sector)
    (∑ row, deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) (metric sector) reference row (test row))

theorem deDonderTestRiesz_pairing (sector : Sector) (test : OriginalCovectorTest period hPeriod)
    (field : (hessianFeatureMinimal period hPeriod metric).domain) :
    inner Real (deDonderTestRiesz period hPeriod reference metric sector test) field.val =
      inner Real (smoothTestVector period hPeriod test) (hessianFeatureMinimal period hPeriod metric field (0, sector)).val := by
  rw [deDonderTestRiesz, ContinuousLinearMap.adjoint_inner_left, sum_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro row _
  have h := hessianFeature_closedGraph_deDonder period hPeriod metric reference
    (field.val, hessianFeatureMinimal period hPeriod metric field)
    (by rw [← hessianFeatureMinimal_graph period hPeriod metric reference]; exact (hessianFeatureMinimal period hPeriod metric).mem_graph field)
    sector row (test row)
  exact (real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _))

def fpOriginalTransposeTest (test : OriginalCovectorTest period hPeriod) : Fin 4 → SmoothScalarField period hPeriod :=
  smoothMatrixTransposeTest period hPeriod
    (frameCovectorChangeMatrix period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
      (finiteSmoothTangentFrame period hPeriod) reference.metric) test

theorem covectorRecovery_test_pairing (field : ActualFPCovectorL2 period hPeriod)
    (test : OriginalCovectorTest period hPeriod) :
    inner Real field.val (smoothTestVector period hPeriod test) =
      inner Real (actualFPCovectorRecovery period hPeriod reference field)
        (smoothTestVector period hPeriod (fpOriginalTransposeTest period hPeriod reference test)) := by
  have hInverse := frameCovectorL2Transport_inverse period hPeriod
    (finiteSmoothTangentFrame period hPeriod) (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric field
  change frameCovectorL2Transport period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    (finiteSmoothTangentFrame period hPeriod) reference.metric (actualFPCovectorRecovery period hPeriod reference field) = field.val at hInverse
  rw [← hInverse]
  exact canonicalSmoothMatrixL2_test_pairing period hPeriod _ _ test

def ghostRegularReadout : DiffeomorphismL2 period hPeriod (metric .plus) →L[Real] CartanGhostL2 period hPeriod :=
  (regularGhostL2Recovery period hPeriod reference (metric .plus)).comp
    (diffeomorphismTripletReadout period hPeriod (metric .plus) 0)

def fpTestRiesz (sector : Sector) (test : OriginalCovectorTest period hPeriod) :
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  ContinuousLinearMap.adjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (F := CartanGhostL2 period hPeriod) (ghostRegularReadout period hPeriod reference metric)
    (∑ row : Fin 4, fpRowAdjointTest period hPeriod reference (metric sector) row
      (fpOriginalTransposeTest period hPeriod reference test row))

theorem fpTestRiesz_pairing (sector : Sector) (test : OriginalCovectorTest period hPeriod)
    (field : (hessianFeatureMinimal period hPeriod metric).domain) :
    inner Real (fpTestRiesz period hPeriod reference metric sector test) field.val =
      inner Real (smoothTestVector period hPeriod test) (hessianFeatureMinimal period hPeriod metric field (1, sector)).val := by
  have hRows : inner Real (fpTestRiesz period hPeriod reference metric sector test) field.val =
      inner Real (smoothTestVector period hPeriod (fpOriginalTransposeTest period hPeriod reference test))
        (actualFPCovectorRecovery period hPeriod reference (hessianFeatureMinimal period hPeriod metric field (1, sector))) := by
    rw [fpTestRiesz, ContinuousLinearMap.adjoint_inner_left, sum_inner, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro row _
    have h := hessianFeature_closedGraph_fp period hPeriod metric reference
      (field.val, hessianFeatureMinimal period hPeriod metric field)
      (by rw [← hessianFeatureMinimal_graph period hPeriod metric reference]; exact (hessianFeatureMinimal period hPeriod metric).mem_graph field)
      sector row (fpOriginalTransposeTest period hPeriod reference test row)
    exact (real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _))
  exact hRows.trans ((real_inner_comm _ _).trans
    ((covectorRecovery_test_pairing period hPeriod reference
      (hessianFeatureMinimal period hPeriod metric field (1, sector)) test).symm.trans (real_inner_comm _ _)))

end
end JanusFormal.P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D
