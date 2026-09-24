import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12TensorSecondJetL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedInducedMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Actual BRST metric L2 bounds for paired second-jet expressions. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedTensorSecondJetL24D
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

open P0EFTJanusProgramPT12TensorSecondJetL24D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D

variable (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
  (value : Sector → Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
  (first : Sector → Fin 4 → Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
  (second : Sector → Fin 4 → Fin 4 → Fin 4 → Fin 4 → SmoothScalarField period hPeriod)

def pairedTensorSecondJetCovector : DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  ∑ sector, (tensorSecondJetCovector period hPeriod
    (metric sector) (value sector) (first sector) (second sector)).comp
      (diffeomorphismTensorReadout period hPeriod normalization sector)

theorem pairedTensorSecondJetCovector_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    pairedTensorSecondJetCovector period hPeriod normalization metric value first second
      (diffeomorphismL2Smooth period hPeriod normalization field) =
    ∑ sector, tensorSecondJetFunctional period hPeriod
      (metric sector) (value sector) (first sector) (second sector) (field.metricPerturbation sector) := by
  simp only [pairedTensorSecondJetCovector, sum_apply, ContinuousLinearMap.comp_apply,
    diffeomorphismTensorReadout_smooth, tensorSecondJetCovector_smooth]

theorem pairedTensorSecondJetFunctional_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, tensorSecondJetFunctional period hPeriod
      (metric sector) (value sector) (first sector) (second sector) (field.metricPerturbation sector)‖ ≤
    ‖pairedTensorSecondJetCovector period hPeriod normalization metric value first second‖ *
      ‖diffeomorphismL2Smooth period hPeriod normalization field‖ := by
  rw [← pairedTensorSecondJetCovector_smooth period hPeriod normalization metric value first second field]
  exact ContinuousLinearMap.le_opNorm _ _

theorem pairedTensorSecondJetFunctional_metric_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, tensorSecondJetFunctional period hPeriod
      (metric sector) (value sector) (first sector) (second sector) (field.metricPerturbation sector)‖ ≤
    ‖pairedTensorSecondJetCovector period hPeriod normalization metric value first second‖ *
      ‖diffeomorphismMetricSmooth period hPeriod normalization field‖ := by
  change _ ≤ _ * ‖(diffeomorphismMetricSmooth period hPeriod normalization field).val‖
  rw [diffeomorphismMetricSmooth_original]
  simpa only [diffeomorphismMetricTransfer_metric] using
    pairedTensorSecondJetFunctional_bound period hPeriod normalization metric value first second
      (diffeomorphismMetricTransfer period hPeriod normalization field)

end
end JanusFormal.P0EFTJanusProgramPT12PairedTensorSecondJetL24D
