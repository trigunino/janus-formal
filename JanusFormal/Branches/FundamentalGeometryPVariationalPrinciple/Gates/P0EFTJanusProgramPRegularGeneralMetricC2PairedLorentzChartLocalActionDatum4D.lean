import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartActionData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLocalVariationalChart4D

/-!
# Local Candidate-A datum on the paired regular metric chart

The paired configuration and its complete action package are bundled into the
dependent local datum expected by the variational-chart API.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartLocalActionDatum4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartActionData4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The complete paired configuration/action package as the dependent datum
used by local Candidate-A families. -/
def regularGeneralMetricC2PairedLorentzChartLocalActionDatum
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace :=
  ⟨regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
      configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential,
    regularGeneralMetricC2PairedLorentzChartActionData period hPeriod
      configuration couplings data plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential variation⟩

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartLocalActionDatum_configuration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartLocalActionDatum period hPeriod
      configuration couplings data plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential variation).1 =
      regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
        configuration plusBase minusBase plusMetricVariation
          minusMetricVariation hAdmissible potential :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartLocalActionDatum_data
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartLocalActionDatum period hPeriod
      configuration couplings data plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential variation).2 =
      regularGeneralMetricC2PairedLorentzChartActionData period hPeriod
        configuration couplings data plusBase minusBase plusMetricVariation
          minusMetricVariation hAdmissible potential variation :=
  rfl

/-- Gate marker: every admissible paired point now has the exact dependent
datum required by the local variational family interface. -/
theorem regular_general_metric_c2_paired_lorentz_chart_local_action_datum_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    Nonempty (GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace) :=
  ⟨regularGeneralMetricC2PairedLorentzChartLocalActionDatum period hPeriod
    configuration couplings data plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential variation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartLocalActionDatum4D
end JanusFormal
