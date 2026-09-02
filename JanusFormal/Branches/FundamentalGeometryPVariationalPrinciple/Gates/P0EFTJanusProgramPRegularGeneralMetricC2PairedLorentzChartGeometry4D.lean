import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedD8GeneralLorentzMetricFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

/-!
# Two independent regular metric perturbations in the Candidate-A chart

Two independent Lorentz-chart variations are first promoted to regular
metrics.  The second-stage relative variation is measured from the varied
plus metric; when it is admissible, the existing root chart produces one
genuine `GlobalCandidateAGeometry` whose two metrics are exactly the two
independently varied metrics.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusFixedD8GeneralLorentzMetricFunctor4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Relative tensor from the varied plus metric to the independently varied
minus metric. -/
def regularGeneralMetricC2PairedRelativeTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  (minusBase.metric.tensor + minusVariation) -
    (plusBase.metric.tensor + plusVariation)

/-- Honest nested admissibility data for two independent metric variations.
The final field is the Candidate-A root-chart condition between the two
already varied metrics; it is not inferred from separate Lorentzness. -/
structure RegularGeneralMetricC2PairedLorentzChartAdmissible
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod) : Prop where
  plus_mem : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
      plusVariation ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase
  minus_mem : regularGeneralMetricSmoothC2Variation period hPeriod minusBase
      minusVariation ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase
  relative_mem :
    regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase plusVariation plus_mem)
        (regularGeneralMetricC2PairedRelativeTensor period hPeriod
          plusBase minusBase plusVariation minusVariation) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase plusVariation plus_mem)

/-- Regular plus metric selected by the first independent chart. -/
def regularGeneralMetricC2PairedPlusMetric
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    RegularGeneralLorentzMetric period hPeriod :=
  regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
    plusVariation hAdmissible.plus_mem

/-- Regular minus metric selected independently in the second base chart. -/
def regularGeneralMetricC2PairedMinusMetric
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    RegularGeneralLorentzMetric period hPeriod :=
  regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
    minusVariation hAdmissible.minus_mem

/-- Candidate-A geometry obtained from the varied plus metric and the exact
relative tensor leading to the independently varied minus metric. -/
def regularGeneralMetricC2PairedLorentzChartGeometry
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    GlobalCandidateAGeometry period hPeriod :=
  regularGeneralMetricC2LorentzChartGeometry period hPeriod
    (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible)
    (regularGeneralMetricC2PairedRelativeTensor period hPeriod
      plusBase minusBase plusVariation minusVariation)
    hAdmissible.relative_mem

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartGeometry_plusMetric
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible).plusMetric =
        (regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase
          minusBase plusVariation minusVariation hAdmissible).metric :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartGeometry_minusMetric
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible).minusMetric =
        (regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase
          minusBase plusVariation minusVariation hAdmissible).metric := by
  apply smoothGeneralLorentzMetric_ext
  unfold regularGeneralMetricC2PairedLorentzChartGeometry
  rw [regularGeneralMetricC2LorentzChartGeometry_minusMetric]
  unfold regularGeneralMetricC2PairedPlusMetric
  unfold regularGeneralMetricC2PairedMinusMetric
  rw [regularGeneralMetricC2LorentzChartMetric_tensor,
    regularGeneralMetricC2LorentzChartRegularMetric_metric,
    regularGeneralMetricC2LorentzChartMetric_tensor,
    regularGeneralMetricC2LorentzChartRegularMetric_metric,
    regularGeneralMetricC2LorentzChartMetric_tensor]
  unfold regularGeneralMetricC2PairedRelativeTensor
  abel

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartGeometry_plusTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible
        ).plusMetric.tensor = plusBase.metric.tensor + plusVariation := by
  rw [regularGeneralMetricC2PairedLorentzChartGeometry_plusMetric]
  exact regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod
    plusBase plusVariation hAdmissible.plus_mem

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartGeometry_minusTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    (regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible
        ).minusMetric.tensor = minusBase.metric.tensor + minusVariation := by
  rw [regularGeneralMetricC2PairedLorentzChartGeometry_minusMetric]
  exact regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod
    minusBase minusVariation hAdmissible.minus_mem

/-- Gate marker: the Candidate-A root geometry now accepts two independent
regular C² metric variations and returns exactly their two affine metrics. -/
theorem regular_general_metric_c2_paired_lorentz_chart_geometry_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusVariation minusVariation) :
    ∃ geometry : GlobalCandidateAGeometry period hPeriod,
      geometry.plusMetric.tensor = plusBase.metric.tensor + plusVariation ∧
        geometry.minusMetric.tensor =
          minusBase.metric.tensor + minusVariation := by
  exact ⟨regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible,
    regularGeneralMetricC2PairedLorentzChartGeometry_plusTensor period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible,
    regularGeneralMetricC2PairedLorentzChartGeometry_minusTensor period hPeriod
      plusBase minusBase plusVariation minusVariation hAdmissible⟩

/-- The same honest admissibility predicate on the exact two-sector metric
direction used by the global T03 tangent. -/
abbrev GlobalMetricPerturbationPairLorentzChartAdmissible
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod) : Prop :=
  RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
    plusBase minusBase (perturbation .plus) (perturbation .minus)

/-- Direct Candidate-A geometry chart on the already installed global metric
perturbation pair. -/
def globalMetricPerturbationPairLorentzChartGeometry
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase perturbation) :
    GlobalCandidateAGeometry period hPeriod :=
  regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
    plusBase minusBase (perturbation .plus) (perturbation .minus) hAdmissible

@[simp]
theorem globalMetricPerturbationPairLorentzChartGeometry_plusTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase perturbation) :
    (globalMetricPerturbationPairLorentzChartGeometry period hPeriod
      plusBase minusBase perturbation hAdmissible).plusMetric.tensor =
        plusBase.metric.tensor + perturbation .plus :=
  regularGeneralMetricC2PairedLorentzChartGeometry_plusTensor period hPeriod
    plusBase minusBase (perturbation .plus) (perturbation .minus) hAdmissible

@[simp]
theorem globalMetricPerturbationPairLorentzChartGeometry_minusTensor
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase perturbation) :
    (globalMetricPerturbationPairLorentzChartGeometry period hPeriod
      plusBase minusBase perturbation hAdmissible).minusMetric.tensor =
        minusBase.metric.tensor + perturbation .minus :=
  regularGeneralMetricC2PairedLorentzChartGeometry_minusTensor period hPeriod
    plusBase minusBase (perturbation .plus) (perturbation .minus) hAdmissible

/-- Typed bridge from the exact global metric tangent slot to the paired
Candidate-A geometry chart. -/
theorem global_metric_perturbation_pair_lorentz_chart_geometry_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (perturbation : GlobalMetricPerturbationPair period hPeriod)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase perturbation) :
    ∃ geometry : GlobalCandidateAGeometry period hPeriod,
      geometry.plusMetric.tensor =
          plusBase.metric.tensor + perturbation .plus ∧
        geometry.minusMetric.tensor =
          minusBase.metric.tensor + perturbation .minus := by
  exact ⟨globalMetricPerturbationPairLorentzChartGeometry period hPeriod
      plusBase minusBase perturbation hAdmissible,
    globalMetricPerturbationPairLorentzChartGeometry_plusTensor period hPeriod
      plusBase minusBase perturbation hAdmissible,
    globalMetricPerturbationPairLorentzChartGeometry_minusTensor period hPeriod
      plusBase minusBase perturbation hAdmissible⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
end JanusFormal
