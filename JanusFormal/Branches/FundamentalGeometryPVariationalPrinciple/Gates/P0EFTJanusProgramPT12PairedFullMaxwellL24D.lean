import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedInducedMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Weighted complete Maxwell metric covector on the actual paired diffeomorphism L2 space. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedFullMaxwellL24D
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

variable (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
  (potential : Sector → SmoothAbelianGaugePotential period hPeriod) (weights : Sector → Real)

/-- Both complete Maxwell metric variations with the given physical weights. -/
def pairedFullMaxwellMetricCovector : DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  ∑ sector, weights sector •
    (fullMaxwellMetricCovector period hPeriod (metric sector) (potential sector)).comp
      (diffeomorphismTensorReadout period hPeriod normalization sector)

theorem pairedFullMaxwellMetricCovector_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    pairedFullMaxwellMetricCovector period hPeriod normalization metric potential weights
      (diffeomorphismL2Smooth period hPeriod normalization field) =
      ∑ sector, weights sector * fullMaxwellMetricVariation period hPeriod
        (metric sector) (potential sector) (field.metricPerturbation sector) := by
  simp only [pairedFullMaxwellMetricCovector, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    diffeomorphismTensorReadout_smooth, fullMaxwellMetricCovector_smooth, smul_eq_mul]

/-- The paired native Maxwell derivative is bounded in the actual diffeomorphism L2 norm. -/
theorem pairedFullMaxwellMetricVariation_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖∑ sector, weights sector * fullMaxwellMetricVariation period hPeriod
      (metric sector) (potential sector) (field.metricPerturbation sector)‖ ≤
      ‖pairedFullMaxwellMetricCovector period hPeriod normalization metric potential weights‖ *
        ‖diffeomorphismL2Smooth period hPeriod normalization field‖ := by
  rw [← pairedFullMaxwellMetricCovector_smooth period hPeriod normalization metric potential weights field]
  exact ContinuousLinearMap.le_opNorm _ _

end
end JanusFormal.P0EFTJanusProgramPT12PairedFullMaxwellL24D
