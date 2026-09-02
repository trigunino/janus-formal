import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D

/-!
# Einstein--Hilbert data for the paired regular metric chart

The two regular metrics produced by the paired Candidate-A chart are promoted
with the existing global scalar-curvature constructor.  Their metric fields
are identified exactly with the two sectors of the paired geometry.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Einstein--Hilbert package of the independently varied plus metric. -/
def regularGeneralMetricC2PairedPlusGravity
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    RegularEinsteinHilbertMetric period hPeriod :=
  JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
    period hPeriod
      (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
        plusVariation minusVariation hAdmissible)

/-- Einstein--Hilbert package of the independently varied minus metric. -/
def regularGeneralMetricC2PairedMinusGravity
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    RegularEinsteinHilbertMetric period hPeriod :=
  JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
    period hPeriod
      (regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
        plusVariation minusVariation hAdmissible)

@[simp]
theorem regularGeneralMetricC2PairedPlusGravity_metric
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible).metric =
        regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
          minusBase plusVariation minusVariation hAdmissible :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinusGravity_metric
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible).metric =
        regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase
          minusBase plusVariation minusVariation hAdmissible :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedPlusGravity_metric_eq_geometry
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible).metric.metric =
        (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
          plusBase minusBase plusVariation minusVariation
          hAdmissible).plusMetric := by
  exact (regularGeneralMetricC2PairedLorentzChartGeometry_plusMetric
    period hPeriod plusBase minusBase plusVariation minusVariation
    hAdmissible).symm

@[simp]
theorem regularGeneralMetricC2PairedMinusGravity_metric_eq_geometry
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible).metric.metric =
        (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
          plusBase minusBase plusVariation minusVariation
          hAdmissible).minusMetric := by
  exact (regularGeneralMetricC2PairedLorentzChartGeometry_minusMetric
    period hPeriod plusBase minusBase plusVariation minusVariation
    hAdmissible).symm

/-- The first four geometric fields required by
`GlobalCandidateAActionData` are supplied by the paired chart. -/
theorem regular_general_metric_c2_paired_lorentz_chart_gravity_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    ∃ plusGravity minusGravity : RegularEinsteinHilbertMetric period hPeriod,
      plusGravity.metric.metric =
          (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusVariation minusVariation
            hAdmissible).plusMetric ∧
        minusGravity.metric.metric =
          (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
            plusBase minusBase plusVariation minusVariation
            hAdmissible).minusMetric := by
  exact ⟨regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
      minusBase plusVariation minusVariation hAdmissible,
    regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible,
    regularGeneralMetricC2PairedPlusGravity_metric_eq_geometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible,
    regularGeneralMetricC2PairedMinusGravity_metric_eq_geometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible⟩

/-- Direct typed wrapper for the two-sector metric tangent used by T03. -/
theorem global_metric_perturbation_pair_lorentz_chart_gravity_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase perturbation) :
    ∃ plusGravity minusGravity : RegularEinsteinHilbertMetric period hPeriod,
      plusGravity.metric.metric =
          (globalMetricPerturbationPairLorentzChartGeometry period hPeriod
            plusBase minusBase perturbation hAdmissible).plusMetric ∧
        minusGravity.metric.metric =
          (globalMetricPerturbationPairLorentzChartGeometry period hPeriod
            plusBase minusBase perturbation hAdmissible).minusMetric := by
  exact regular_general_metric_c2_paired_lorentz_chart_gravity_gate
    period hPeriod plusBase minusBase (perturbation .plus)
      (perturbation .minus) hAdmissible

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
end JanusFormal
