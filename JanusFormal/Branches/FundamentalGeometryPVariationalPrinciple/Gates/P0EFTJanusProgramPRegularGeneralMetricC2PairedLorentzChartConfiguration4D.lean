import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D

/-!
# Intrinsic-gauge configuration on the paired regular metric chart

The paired geometry is installed in a global configuration while the two
gauge coefficient fields are defined by evaluating supplied intrinsic
potentials in the corresponding varied regular frames.  All unrelated
non-metric fields are inherited from a supplied configuration.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Install the paired Candidate-A geometry and the exact regular-frame
coefficient readings of two intrinsic gauge potentials. -/
def regularGeneralMetricC2PairedLorentzChartConfiguration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalFieldConfiguration period hPeriod where
  geometry := regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  coefficientFields :=
    { metrics :=
        ((regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible).plusMetric,
          (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible).minusMetric)
      matter := configuration.coefficientFields.matter
      gauge :=
        (gaugePotentialFrameCoefficients period hPeriod
            (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
              minusBase plusMetricVariation minusMetricVariation
              hAdmissible).metric (potential .plus),
          gaugePotentialFrameCoefficients period hPeriod
            (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
              minusBase plusMetricVariation minusMetricVariation
              hAdmissible).metric (potential .minus))
      ghosts := configuration.coefficientFields.ghosts
      auxiliaries := configuration.coefficientFields.auxiliaries
      llAuxMetric := configuration.coefficientFields.llAuxMetric
      llMeasure := configuration.coefficientFields.llMeasure
      llField := configuration.coefficientFields.llField }
  metrics_eq := rfl
  legacyMatter_eq_zero := configuration.legacyMatter_eq_zero
  spinCMatter := configuration.spinCMatter
  d10Completion := configuration.d10Completion

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartConfiguration_geometry
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
      configuration plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential).geometry =
        regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
          plusBase minusBase plusMetricVariation minusMetricVariation
          hAdmissible :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartConfiguration_metrics
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
      configuration plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential).coefficientFields.metrics =
        ((regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible).plusMetric,
          (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible).minusMetric) :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartConfiguration_plusGauge
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
      configuration plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential).coefficientFields.gauge.1 =
        gaugePotentialFrameCoefficients period hPeriod
          (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric (potential .plus) :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartConfiguration_minusGauge
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
      configuration plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential).coefficientFields.gauge.2 =
        gaugePotentialFrameCoefficients period hPeriod
          (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric (potential .minus) :=
  rfl

/-- Exact `plusGauge_eq` field required by `GlobalCandidateAActionData` for
the paired intrinsic Maxwell line. -/
theorem regularGeneralMetricC2PairedLorentzChartConfiguration_plusGauge_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod)
    (point : MappingTorus (reflectedSphereData period hPeriod))
    (index : Fin 4) (component : Fin 2) :
    (regularGeneralMetricC2PairedPlusMaxwell period hPeriod plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible (potential .plus)
        (variation .plus)).potential.toFun component point
          ((regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric.frame index point) =
      (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
        configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential).coefficientFields.gauge.1
          point (index, component) := by
  exact regularGeneralMetricC2PairedPlusMaxwell_gaugeCoefficient period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
      (potential .plus) (variation .plus) point index component

/-- Exact `minusGauge_eq` field required by `GlobalCandidateAActionData` for
the paired intrinsic Maxwell line. -/
theorem regularGeneralMetricC2PairedLorentzChartConfiguration_minusGauge_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod)
    (point : MappingTorus (reflectedSphereData period hPeriod))
    (index : Fin 4) (component : Fin 2) :
    (regularGeneralMetricC2PairedMinusMaxwell period hPeriod plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible (potential .minus)
        (variation .minus)).potential.toFun component point
          ((regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric.frame index point) =
      (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
        configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential).coefficientFields.gauge.2
          point (index, component) := by
  exact regularGeneralMetricC2PairedMinusMaxwell_gaugeCoefficient period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
      (potential .minus) (variation .minus) point index component

/-- Gate marker: one global configuration now carries the paired geometry and
the exact intrinsic-gauge coefficient fields read by both Maxwell lines. -/
theorem regular_general_metric_c2_paired_lorentz_chart_configuration_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    ∃ result : GlobalFieldConfiguration period hPeriod,
      result.geometry =
          regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible ∧
        result.coefficientFields.gauge.1 =
          gaugePotentialFrameCoefficients period hPeriod
            (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
              minusBase plusMetricVariation minusMetricVariation
              hAdmissible).metric (potential .plus) ∧
        result.coefficientFields.gauge.2 =
          gaugePotentialFrameCoefficients period hPeriod
            (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
              minusBase plusMetricVariation minusMetricVariation
              hAdmissible).metric (potential .minus) := by
  exact ⟨regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
      configuration plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential, rfl, rfl, rfl⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D
end JanusFormal
