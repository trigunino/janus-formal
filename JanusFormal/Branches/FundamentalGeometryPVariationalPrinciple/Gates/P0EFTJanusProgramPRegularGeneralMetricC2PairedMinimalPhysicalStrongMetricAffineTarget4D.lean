import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

/-! # Exact affine metric line in the concrete strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D

set_option autoImplicit false
set_option maxHeartbeats 300000

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance globalMinimalPhysicalTangentAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_fullMetricPerturbation
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration test).1.completeVariation.fullMetricPerturbation =
        test :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_independent
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration test).1.completeVariation.independent = 0 :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricLine_fullMetricPerturbation
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) (t : Real) :
    (point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration test).1.completeVariation.fullMetricPerturbation =
      point.1.completeVariation.fullMetricPerturbation + t • test := by
  change point.1.completeVariation.fullMetricPerturbation + t • test = _
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricLine_independent
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) (t : Real) :
    (point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration test).1.completeVariation.independent =
      point.1.completeVariation.independent := by
  change point.1.completeVariation.independent + t • 0 = _
  simp

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricLine_spinC
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) (t : Real) :
    (point + t •
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration test).1.2 = point.1.2 := by
  change point.1.2 + t • 0 = _
  simp

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricTarget_plusTensor
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) (t : Real)
    (hLine : point + t •
        regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
          hPeriod configuration test ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
      configuration plusBase minusBase
        (point + t •
          regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
            period hPeriod configuration test) hLine).geometry.plusMetric.tensor =
      plusBase.metric.tensor +
        (point.1.completeVariation.fullMetricPerturbation .plus +
          t • test .plus) := by
  rw [regularGeneralMetricC2PairedMinimalPhysicalTarget_geometry,
    regularGeneralMetricC2PairedLorentzChartGeometry_plusTensor,
    congrFun
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricLine_fullMetricPerturbation
        period hPeriod configuration point test t) .plus]
  rfl

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricTarget_minusTensor
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) (t : Real)
    (hLine : point + t •
        regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
          hPeriod configuration test ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
      configuration plusBase minusBase
        (point + t •
          regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
            period hPeriod configuration test) hLine).geometry.minusMetric.tensor =
      minusBase.metric.tensor +
        (point.1.completeVariation.fullMetricPerturbation .minus +
          t • test .minus) := by
  rw [regularGeneralMetricC2PairedMinimalPhysicalTarget_geometry,
    regularGeneralMetricC2PairedLorentzChartGeometry_minusTensor,
    congrFun
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricLine_fullMetricPerturbation
        period hPeriod configuration point test t) .minus]
  rfl

/-- Gate marker: pure metric tests generate the exact two-sector affine metric
line and leave every nonmetric strong coordinate fixed. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_metric_affine_target_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration test).1.completeVariation.fullMetricPerturbation =
        test ∧
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration test).1.completeVariation.independent = 0 :=
  ⟨regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_fullMetricPerturbation
      period hPeriod configuration test,
    regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_independent
      period hPeriod configuration test⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D
end JanusFormal
