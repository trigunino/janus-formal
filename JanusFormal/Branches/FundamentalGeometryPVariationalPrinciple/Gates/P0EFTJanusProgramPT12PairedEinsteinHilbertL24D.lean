import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StoredVolumeEinsteinHilbertL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedInducedMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Both native gravity variations as one covector on the actual BRST L2 space. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
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

def pairedEinsteinHilbertCovector : DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  ∑ sector, (innerSL Real (storedVolumeEinsteinHilbertL2 period hPeriod
    (metric sector) (couplings sector))).comp
      (diffeomorphismTensorReadout period hPeriod normalization sector)

theorem pairedEinsteinHilbertCovector_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    pairedEinsteinHilbertCovector period hPeriod normalization metric couplings
      (diffeomorphismL2Smooth period hPeriod normalization field) =
    ∑ sector, regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
      period hPeriod (metric sector) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (couplings sector) (regularGeneralMetricC2SmoothDirection period hPeriod
        (metric sector) (field.metricPerturbation sector)) := by
  simp only [pairedEinsteinHilbertCovector, sum_apply, ContinuousLinearMap.comp_apply,
    diffeomorphismTensorReadout_smooth, innerSL_apply_apply,
    storedVolumeEinsteinHilbertDerivative_eq_inner]

theorem pairedEinsteinHilbertDerivative_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
      period hPeriod (metric sector) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (couplings sector) (regularGeneralMetricC2SmoothDirection period hPeriod
        (metric sector) (field.metricPerturbation sector))‖ ≤
    ‖pairedEinsteinHilbertCovector period hPeriod normalization metric couplings‖ *
      ‖diffeomorphismL2Smooth period hPeriod normalization field‖ := by
  rw [← pairedEinsteinHilbertCovector_smooth period hPeriod normalization metric couplings field]
  exact ContinuousLinearMap.le_opNorm _ _

/-- Only the physical metric norm enters; all nonmetric BRST components drop out. -/
theorem pairedEinsteinHilbertDerivative_metric_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
      period hPeriod (metric sector) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (couplings sector) (regularGeneralMetricC2SmoothDirection period hPeriod
        (metric sector) (field.metricPerturbation sector))‖ ≤
    ‖pairedEinsteinHilbertCovector period hPeriod normalization metric couplings‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization field‖ := by
  change _ ≤ _ * ‖(diffeomorphismMetricSmooth period hPeriod normalization field).val‖
  rw [diffeomorphismMetricSmooth_original]
  simpa only [diffeomorphismMetricTransfer_metric] using
    pairedEinsteinHilbertDerivative_bound period hPeriod normalization metric couplings
      (diffeomorphismMetricTransfer period hPeriod normalization field)

end
end JanusFormal.P0EFTJanusProgramPT12PairedEinsteinHilbertL24D
