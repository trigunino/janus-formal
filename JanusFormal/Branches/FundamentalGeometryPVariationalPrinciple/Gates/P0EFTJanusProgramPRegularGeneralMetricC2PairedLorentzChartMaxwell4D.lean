import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

/-!
# Maxwell data for the paired regular metric chart

The frame-free global Maxwell pairing supplies every scalar field required by
a regular intrinsic Maxwell line.  Specializing this constructor to the two
paired gravity metrics gives gauge coefficients by evaluation in their own
regular frames, with no inverse-coframe assumption.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Canonical regular Maxwell line determined by an intrinsic potential and
an intrinsic variation on any regular metric. -/
def regularIntrinsicMaxwellLineOfPotentials
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    RegularIntrinsicMaxwellLine period hPeriod metric where
  potential := potential
  variation := variation
  basePairing :=
    globalSmoothMaxwellPairing period hPeriod metric.metric
      potential potential
  mixedPairing :=
    globalSmoothMaxwellPairing period hPeriod metric.metric
        variation potential +
      globalSmoothMaxwellPairing period hPeriod metric.metric
        potential variation
  variationPairing :=
    globalSmoothMaxwellPairing period hPeriod metric.metric
      variation variation
  basePairing_eq patch coordinate := by
    exact globalMaxwellPairing_eq_local period hPeriod metric.metric
      potential potential patch coordinate
  mixedPairing_eq patch coordinate := by
    change
      globalMaxwellPairing period hPeriod metric.metric variation potential
          (patch.coordinateMap coordinate) +
        globalMaxwellPairing period hPeriod metric.metric potential variation
          (patch.coordinateMap coordinate) = _
    rw [globalMaxwellPairing_eq_local, globalMaxwellPairing_eq_local]
  variationPairing_eq patch coordinate := by
    exact globalMaxwellPairing_eq_local period hPeriod metric.metric
      variation variation patch coordinate

@[simp]
theorem regularIntrinsicMaxwellLineOfPotentials_potential
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
      potential variation).potential = potential :=
  rfl

@[simp]
theorem regularIntrinsicMaxwellLineOfPotentials_variation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
      potential variation).variation = variation :=
  rfl

/-- Plus-sector Maxwell line on the independently varied plus metric. -/
def regularGeneralMetricC2PairedPlusMaxwell
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    RegularIntrinsicMaxwellLine period hPeriod
      (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase minusBase
        plusMetricVariation minusMetricVariation hAdmissible).metric :=
  regularIntrinsicMaxwellLineOfPotentials period hPeriod _ potential variation

/-- Minus-sector Maxwell line on the independently varied minus metric. -/
def regularGeneralMetricC2PairedMinusMaxwell
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    RegularIntrinsicMaxwellLine period hPeriod
      (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase minusBase
        plusMetricVariation minusMetricVariation hAdmissible).metric :=
  regularIntrinsicMaxwellLineOfPotentials period hPeriod _ potential variation

@[simp]
theorem regularGeneralMetricC2PairedPlusMaxwell_gaugeCoefficient
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : MappingTorus (reflectedSphereData period hPeriod))
    (index : Fin 4) (component : Fin 2) :
    (regularGeneralMetricC2PairedPlusMaxwell period hPeriod plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible potential variation
        ).potential.toFun component point
          ((regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric.frame index point) =
      gaugePotentialFrameCoefficients period hPeriod
        (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
          minusBase plusMetricVariation minusMetricVariation
          hAdmissible).metric potential point (index, component) := by
  exact (gaugePotentialFrameCoefficients_apply period hPeriod _ potential
    point index component).symm

@[simp]
theorem regularGeneralMetricC2PairedMinusMaxwell_gaugeCoefficient
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : MappingTorus (reflectedSphereData period hPeriod))
    (index : Fin 4) (component : Fin 2) :
    (regularGeneralMetricC2PairedMinusMaxwell period hPeriod plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible potential variation
        ).potential.toFun component point
          ((regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric.frame index point) =
      gaugePotentialFrameCoefficients period hPeriod
        (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
          minusBase plusMetricVariation minusMetricVariation
          hAdmissible).metric potential point (index, component) := by
  exact (gaugePotentialFrameCoefficients_apply period hPeriod _ potential
    point index component).symm

/-- Gate marker: both paired gravity sectors carry genuine intrinsic Maxwell
lines, and their coefficient fields are exactly their regular-frame readings. -/
theorem regular_general_metric_c2_paired_lorentz_chart_maxwell_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    ∃ plusMaxwell : RegularIntrinsicMaxwellLine period hPeriod
          (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric,
      ∃ minusMaxwell : RegularIntrinsicMaxwellLine period hPeriod
          (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric,
        plusMaxwell.potential = potential .plus ∧
          minusMaxwell.potential = potential .minus := by
  exact ⟨regularGeneralMetricC2PairedPlusMaxwell period hPeriod plusBase
      minusBase plusMetricVariation minusMetricVariation hAdmissible
      (potential .plus) (variation .plus),
    regularGeneralMetricC2PairedMinusMaxwell period hPeriod plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible
      (potential .minus) (variation .minus), rfl, rfl⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
end JanusFormal
