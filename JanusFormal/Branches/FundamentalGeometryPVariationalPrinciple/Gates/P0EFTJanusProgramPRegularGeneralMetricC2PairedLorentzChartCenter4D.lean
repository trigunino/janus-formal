import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D

/-!
# Zero centre of the paired regular Lorentz chart

The two single-metric chart conditions contain zero automatically.  The
paired chart has one additional condition: the base minus metric must lie in
the relative chart based at the base plus metric.  Once this honest base-pair
compatibility is supplied, the zero perturbation is admissible and reconstructs
the two base metric tensors exactly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Compatibility required from the two base metrics for zero to be a centre
of the nested paired chart. -/
def RegularGeneralMetricC2PairedLorentzChartBaseCompatible
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) : Prop :=
  let hPlus :=
    regularGeneralMetricSmoothC2Variation_zero_mem_lorentzChartDomain
      period hPeriod plusBase
  regularGeneralMetricSmoothC2Variation period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
        0 hPlus)
      (minusBase.metric.tensor - plusBase.metric.tensor) ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
        0 hPlus)

/-- A compatible pair of base metrics makes the zero two-sector variation
admissible in the nested chart. -/
theorem regularGeneralMetricC2PairedLorentzChart_zero_admissible
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCompatible : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase 0 0 := by
  let hPlus :=
    regularGeneralMetricSmoothC2Variation_zero_mem_lorentzChartDomain
      period hPeriod plusBase
  let hMinus :=
    regularGeneralMetricSmoothC2Variation_zero_mem_lorentzChartDomain
      period hPeriod minusBase
  refine {
    plus_mem := hPlus
    minus_mem := hMinus
    relative_mem := ?_ }
  simpa [RegularGeneralMetricC2PairedLorentzChartBaseCompatible,
    hPlus, regularGeneralMetricC2PairedRelativeTensor] using hCompatible

/-- The same zero-centre result in the exact global metric-pair model used by
the minimal physical tangent. -/
theorem globalMetricPerturbationPairLorentzChart_zero_admissible
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCompatible : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
      plusBase minusBase 0 := by
  change RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
    plusBase minusBase 0 0
  exact regularGeneralMetricC2PairedLorentzChart_zero_admissible
    period hPeriod plusBase minusBase hCompatible

@[simp]
theorem globalMetricPerturbationPairLorentzChartGeometry_zero_plusTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCompatible : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    (globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
      minusBase 0
        (globalMetricPerturbationPairLorentzChart_zero_admissible period hPeriod
          plusBase minusBase hCompatible)).plusMetric.tensor =
      plusBase.metric.tensor := by
  rw [globalMetricPerturbationPairLorentzChartGeometry_plusTensor]
  simp

@[simp]
theorem globalMetricPerturbationPairLorentzChartGeometry_zero_minusTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCompatible : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    (globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
      minusBase 0
        (globalMetricPerturbationPairLorentzChart_zero_admissible period hPeriod
          plusBase minusBase hCompatible)).minusMetric.tensor =
      minusBase.metric.tensor := by
  rw [globalMetricPerturbationPairLorentzChartGeometry_minusTensor]
  simp

/-- Gate marker: compatible base metrics supply an admissible zero centre with
the exact two base metric tensors. -/
theorem regular_general_metric_c2_paired_lorentz_chart_center_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCompatible : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    ∃ hZero : GlobalMetricPerturbationPairLorentzChartAdmissible
        period hPeriod plusBase minusBase 0,
      (globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
          minusBase 0 hZero).plusMetric.tensor = plusBase.metric.tensor ∧
        (globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
          minusBase 0 hZero).minusMetric.tensor = minusBase.metric.tensor := by
  let hZero := globalMetricPerturbationPairLorentzChart_zero_admissible
    period hPeriod plusBase minusBase hCompatible
  exact ⟨hZero,
    globalMetricPerturbationPairLorentzChartGeometry_zero_plusTensor
      period hPeriod plusBase minusBase hCompatible,
    globalMetricPerturbationPairLorentzChartGeometry_zero_minusTensor
      period hPeriod plusBase minusBase hCompatible⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
end JanusFormal
