import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeEinsteinHessianL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StoredVolumeEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedInducedMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Both native gravity Hessians as one actual BRST L2 covector for each fixed first field. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedEinsteinHessianL24D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12InducedMaxwellMetricL24D

variable (normalization : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12FullMaxwellMetricL24D
open P0EFTJanusProgramPT12PairedInducedMaxwellL24D

open P0EFTJanusProgramPT12StoredVolumeEinsteinHilbertL24D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D

local instance : MeasureTheory.IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

variable (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
  (couplings : Sector → EinsteinHilbertCouplings)

open P0EFTJanusProgramPT12NativeEinsteinHessianL24D
open P0EFTJanusProgramPT12NativeEinsteinHilbertHessian4D

variable (first : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)

def pairedEinsteinHessianCovector : DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  ∑ sector, (innerSL Real (nativeEinsteinHessianL2 period hPeriod
    (metric sector) (couplings sector) (first.metricPerturbation sector))).comp
      (diffeomorphismTensorReadout period hPeriod normalization sector)

theorem pairedEinsteinHessianCovector_smooth
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    pairedEinsteinHessianCovector period hPeriod normalization metric couplings first
      (diffeomorphismL2Smooth period hPeriod normalization test) =
    ∑ sector, nativeEinsteinHilbertHessian period hPeriod (metric sector) (couplings sector)
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector) (first.metricPerturbation sector))
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector) (test.metricPerturbation sector)) := by
  simp only [pairedEinsteinHessianCovector, sum_apply, ContinuousLinearMap.comp_apply,
    diffeomorphismTensorReadout_smooth, innerSL_apply_apply, nativeEinsteinHessianL2_pairing]

theorem pairedEinsteinHessian_bound
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, nativeEinsteinHilbertHessian period hPeriod (metric sector) (couplings sector)
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector) (first.metricPerturbation sector))
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector) (test.metricPerturbation sector))‖ ≤
    ‖pairedEinsteinHessianCovector period hPeriod normalization metric couplings first‖ *
      ‖diffeomorphismL2Smooth period hPeriod normalization test‖ := by
  rw [← pairedEinsteinHessianCovector_smooth period hPeriod normalization metric couplings first test]
  exact ContinuousLinearMap.le_opNorm _ _

theorem pairedEinsteinHessian_metric_bound
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, nativeEinsteinHilbertHessian period hPeriod (metric sector) (couplings sector)
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector) (first.metricPerturbation sector))
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector) (test.metricPerturbation sector))‖ ≤
    ‖pairedEinsteinHessianCovector period hPeriod normalization metric couplings first‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization test‖ := by
  change _ ≤ _ * ‖(diffeomorphismMetricSmooth period hPeriod normalization test).val‖
  rw [diffeomorphismMetricSmooth_original]
  simpa only [diffeomorphismMetricTransfer_metric] using
    pairedEinsteinHessian_bound period hPeriod normalization metric couplings first
      (diffeomorphismMetricTransfer period hPeriod normalization test)

end
end JanusFormal.P0EFTJanusProgramPT12PairedEinsteinHessianL24D
