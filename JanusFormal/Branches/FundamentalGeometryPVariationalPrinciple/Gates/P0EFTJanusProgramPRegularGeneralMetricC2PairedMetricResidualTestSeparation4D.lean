import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D

/-! # Separation of the two strong metric residuals by physical tests -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev MetricPair :=
  SmoothGeneralMetricTensorPair period hPeriod

/-- Convert the physical sector-indexed metric test into the canonical pair. -/
def globalMinimalPhysicalMetricTestPair
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    MetricPair period hPeriod :=
  (test .plus, test .minus)

/-- Convert a canonical tensor pair into the physical sector-indexed test. -/
def globalMinimalPhysicalMetricTestOfPair
    (pair : MetricPair period hPeriod) :
    GlobalMinimalPhysicalMetricTest period hPeriod
  | .plus => pair.1
  | .minus => pair.2

@[simp]
theorem globalMinimalPhysicalMetricTestPair_ofPair
    (pair : MetricPair period hPeriod) :
    globalMinimalPhysicalMetricTestPair period hPeriod
        (globalMinimalPhysicalMetricTestOfPair period hPeriod pair) = pair :=
  rfl

@[simp]
theorem globalMinimalPhysicalMetricTestOfPair_pair
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    globalMinimalPhysicalMetricTestOfPair period hPeriod
        (globalMinimalPhysicalMetricTestPair period hPeriod test) = test := by
  funext sector
  cases sector <;> rfl

/-- Canonical integrated pairing of a smooth two-sector metric residual with
an authentic physical metric test. -/
def regularGeneralMetricC2PairedMetricResidualPairing
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (residual : MetricPair period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) : Real :=
  canonicalGeneralMetricTensorPairPairing period hPeriod metrics residual
    (globalMinimalPhysicalMetricTestPair period hPeriod test)

/-- The authentic physical metric tests separate every smooth tensor-pair
residual. -/
theorem regularGeneralMetricC2PairedMetricResidualPairing_separates
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (residual : MetricPair period hPeriod) :
    (∀ test : GlobalMinimalPhysicalMetricTest period hPeriod,
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics
        residual test = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    apply canonicalGeneralMetricTensorPairPairing_separates period hPeriod
      metrics residual
    intro test
    exact hPairing
      (globalMinimalPhysicalMetricTestOfPair period hPeriod test)
  · rintro rfl test
    unfold regularGeneralMetricC2PairedMetricResidualPairing
    exact canonicalGeneralMetricTensorPairPairing_zero_left period hPeriod
      metrics _

/-- Separated form stated as the two pointwise tensor equations. -/
theorem regularGeneralMetricC2PairedMetricResidualPairing_zero_iff_components
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (residual : MetricPair period hPeriod) :
    (∀ test : GlobalMinimalPhysicalMetricTest period hPeriod,
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics
        residual test = 0) ↔
      residual.1 = 0 ∧ residual.2 = 0 := by
  rw [regularGeneralMetricC2PairedMetricResidualPairing_separates period
    hPeriod metrics residual]
  constructor
  · intro hResidual
    rw [hResidual]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hPlus, hMinus⟩
    exact Prod.ext hPlus hMinus

/-- Gate marker: smooth tests in both physical metric sectors are genuinely
separating, with no nonzero coupling or positivity assumption left as data. -/
theorem regular_general_metric_c2_paired_metric_residual_test_separation_gate
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (residual : MetricPair period hPeriod) :
    (∀ test : GlobalMinimalPhysicalMetricTest period hPeriod,
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics
        residual test = 0) ↔
      residual.1 = 0 ∧ residual.2 = 0 :=
  regularGeneralMetricC2PairedMetricResidualPairing_zero_iff_components period
    hPeriod metrics residual

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
end JanusFormal
