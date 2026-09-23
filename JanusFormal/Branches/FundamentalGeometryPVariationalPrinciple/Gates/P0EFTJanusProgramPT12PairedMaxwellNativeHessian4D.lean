import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedMaxwellMixedL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellMixedMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFullMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedInducedMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Weighted native mixed Maxwell Hessian on the actual diffeomorphism L2 space. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedMaxwellNativeHessian4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
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

variable (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
  (potential : Sector → SmoothAbelianGaugePotential period hPeriod) (weights : Sector → Real)

open P0EFTJanusProgramPT12MaxwellMixedMetricL24D
open P0EFTJanusProgramPT12PairedFullMaxwellL24D

variable (direction : Sector → SmoothAbelianGaugePotential period hPeriod)

open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPT12PairedMaxwellMixedL24D

/-- Exact equality to the physical weighted native Hessian entries. -/
theorem pairedNativeMaxwellHessian_metric_gauge
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (∑ sector, weights sector * nativeMobileMaxwellHessian period hPeriod
      (metric sector) (potential sector)
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector)
        (field.metricPerturbation sector), 0)
      (0, maxwellSmoothGaugeC2 period hPeriod (metric sector) (direction sector))) =
    pairedMaxwellMixedCovector period hPeriod normalization metric potential weights direction
      (diffeomorphismL2Smooth period hPeriod normalization field) := by
  simp only [nativeMobileMaxwellHessian_metric_gauge, pairedMaxwellMixedCovector,
    sum_apply, smul_apply, ContinuousLinearMap.comp_apply, diffeomorphismTensorReadout_smooth,
    innerSL_apply_apply, smul_eq_mul]

theorem pairedNativeMaxwellHessian_gauge_metric
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (∑ sector, weights sector * nativeMobileMaxwellHessian period hPeriod
      (metric sector) (potential sector)
      (0, maxwellSmoothGaugeC2 period hPeriod (metric sector) (direction sector))
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector)
        (field.metricPerturbation sector), 0)) =
    pairedMaxwellMixedCovector period hPeriod normalization metric potential weights direction
      (diffeomorphismL2Smooth period hPeriod normalization field) := by
  simp only [nativeMobileMaxwellHessian_gauge_metric, pairedMaxwellMixedCovector,
    sum_apply, smul_apply, ContinuousLinearMap.comp_apply, diffeomorphismTensorReadout_smooth,
    innerSL_apply_apply, smul_eq_mul]

theorem pairedNativeMaxwellHessian_metric_gauge_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, weights sector * nativeMobileMaxwellHessian period hPeriod
      (metric sector) (potential sector)
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector)
        (field.metricPerturbation sector), 0)
      (0, maxwellSmoothGaugeC2 period hPeriod (metric sector) (direction sector))‖ ≤
    ‖pairedMaxwellMixedCovector period hPeriod normalization metric potential weights direction‖ *
      ‖diffeomorphismL2Smooth period hPeriod normalization field‖ := by
  rw [pairedNativeMaxwellHessian_metric_gauge]
  exact ContinuousLinearMap.le_opNorm _ _

open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

/-- The bound already holds in the metric-only norm used by the H11 adjoint criterion. -/
theorem pairedNativeMaxwellHessian_metric_only_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, weights sector * nativeMobileMaxwellHessian period hPeriod
      (metric sector) (potential sector)
      (regularGeneralMetricC2SmoothDirection period hPeriod (metric sector)
        (field.metricPerturbation sector), 0)
      (0, maxwellSmoothGaugeC2 period hPeriod (metric sector) (direction sector))‖ ≤
    ‖pairedMaxwellMixedCovector period hPeriod normalization metric potential weights direction‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization field‖ := by
  change _ ≤ _ * ‖(diffeomorphismMetricSmooth period hPeriod normalization field).val‖
  rw [diffeomorphismMetricSmooth_original]
  simpa only [diffeomorphismMetricTransfer_metric] using
    pairedNativeMaxwellHessian_metric_gauge_bound period hPeriod normalization metric potential weights direction
      (diffeomorphismMetricTransfer period hPeriod normalization field)
end
end JanusFormal.P0EFTJanusProgramPT12PairedMaxwellNativeHessian4D
