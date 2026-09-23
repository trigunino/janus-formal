import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellMixedMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFullMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedInducedMaxwellL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Weighted mixed potential-metric Maxwell derivative on the actual diffeomorphism L2 space. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedMaxwellMixedL24D
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

/-- The physical weighted mixed derivative is a continuous covector in the metric test. -/
def pairedMaxwellMixedCovector : DiffeomorphismL2 period hPeriod normalization →L[Real] Real :=
  ∑ sector, weights sector •
    (innerSL Real (maxwellMixedMetricRiesz period hPeriod (metric sector)
      (potential sector) (direction sector))).comp
      (diffeomorphismTensorReadout period hPeriod normalization sector)

theorem pairedMaxwellMetricVariation_hasDerivAt_potential
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    HasDerivAt (fun t : Real => ∑ sector, weights sector *
      fullMaxwellMetricVariation period hPeriod (metric sector)
        (potential sector + t • direction sector) (field.metricPerturbation sector))
      (pairedMaxwellMixedCovector period hPeriod normalization metric potential weights direction
        (diffeomorphismL2Smooth period hPeriod normalization field)) 0 := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun sector _ =>
    (fullMaxwellMetricVariation_hasDerivAt_potential period hPeriod (metric sector)
      (potential sector) (direction sector) (field.metricPerturbation sector)).const_mul (weights sector))
  simpa only [Finset.sum_fn, pairedMaxwellMixedCovector, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, diffeomorphismTensorReadout_smooth, innerSL_apply_apply,
    smul_eq_mul] using h

theorem pairedMaxwellMixedVariation_bound
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖deriv (fun t : Real => ∑ sector, weights sector *
      fullMaxwellMetricVariation period hPeriod (metric sector)
        (potential sector + t • direction sector) (field.metricPerturbation sector)) 0‖ ≤
      ‖pairedMaxwellMixedCovector period hPeriod normalization metric potential weights direction‖ *
        ‖diffeomorphismL2Smooth period hPeriod normalization field‖ := by
  rw [(pairedMaxwellMetricVariation_hasDerivAt_potential period hPeriod normalization metric
    potential weights direction field).deriv]
  exact ContinuousLinearMap.le_opNorm _ _

end
end JanusFormal.P0EFTJanusProgramPT12PairedMaxwellMixedL24D
