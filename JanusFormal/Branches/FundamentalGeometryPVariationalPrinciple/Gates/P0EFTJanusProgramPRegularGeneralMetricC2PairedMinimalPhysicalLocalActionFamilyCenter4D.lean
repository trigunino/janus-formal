import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamily4D

/-!
# Exact centre of the paired minimal-physical local action family

Metric compatibility makes the zero direction admissible.  Exact agreement
of the selected paired root geometry with the configuration geometry then
turns the pointwise family into a genuinely centred local action family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamily4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Exact compatibility between the canonical paired chart centre and the
geometry already stored in the base configuration. -/
def RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) : Prop :=
  globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
      minusBase 0
        (globalMetricPerturbationPairLorentzChart_zero_admissible period hPeriod
          plusBase minusBase hBase) =
    configuration.geometry

/-- The datum selected by the paired family at zero has exactly the original
configuration as its first projection. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn_datumAt_zero_configuration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (domain : Set (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration))
    (hAdmissible : ∀ direction, direction ∈ domain →
      GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation)
    (hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ domain)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration plusBase minusBase hBase) :
    ((regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
      period hPeriod configuration couplings data plusBase minusBase domain
        hAdmissible).datumAt 0 hZero).1 = configuration := by
  rw [
    regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn_datumAt_configuration]
  unfold regularGeneralMetricC2PairedMinimalPhysicalTarget
  change globalMinimalPhysicalConfigurationAt period hPeriod configuration
      (globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
        minusBase 0 _) 0 = configuration
  rw [hCenter]
  exact globalMinimalPhysicalConfigurationAt_zero period hPeriod configuration

/-- Gate marker: base compatibility and exact root selection close the centre
identity required by the minimal-physical variational chart. -/
theorem regular_general_metric_c2_paired_minimal_physical_local_action_family_center_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (domain : Set (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration))
    (hAdmissible : ∀ direction, direction ∈ domain →
      GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation)
    (hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ domain)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration plusBase minusBase hBase) :
    ((regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
      period hPeriod configuration couplings data plusBase minusBase domain
        hAdmissible).datumAt 0 hZero).1 = configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn_datumAt_zero_configuration
    period hPeriod configuration couplings data plusBase minusBase hBase domain
      hAdmissible hZero hCenter

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
end JanusFormal
