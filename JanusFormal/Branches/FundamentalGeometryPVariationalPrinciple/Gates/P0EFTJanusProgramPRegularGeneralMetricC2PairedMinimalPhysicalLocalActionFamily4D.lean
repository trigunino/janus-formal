import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D

/-!
# Paired local action family on an admissible minimal-physical domain

The pointwise datum is packaged over any supplied set on which paired chart
admissibility is known.  This is the exact `datumAt` layer; openness, the
center identity and blockwise `C²` regularity belong to the later variational
chart contract.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamily4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Exact local action family on any domain carrying pointwise paired-chart
admissibility. -/
def regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (domain : Set (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration))
    (hAdmissible : ∀ direction, direction ∈ domain →
      GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation) :
    GlobalCandidateALocalActionFamily period hPeriod
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
      couplings NonNullFace NullFace where
  domain := domain
  datumAt := fun direction hDirection =>
    regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum period hPeriod
      configuration couplings data plusBase minusBase direction
        (hAdmissible direction hDirection)

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn_domain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (domain : Set (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration))
    (hAdmissible : ∀ direction, direction ∈ domain →
      GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation) :
    (regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
      period hPeriod configuration couplings data plusBase minusBase domain
        hAdmissible).domain = domain :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn_datumAt_configuration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (domain : Set (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration))
    (hAdmissible : ∀ direction, direction ∈ domain →
      GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) (hDirection : direction ∈ domain) :
    ((regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
      period hPeriod configuration couplings data plusBase minusBase domain
        hAdmissible).datumAt direction hDirection).1 =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase direction
          (hAdmissible direction hDirection) :=
  rfl

/-- Gate marker: the pointwise minimal-physical construction now supplies the
actual `datumAt` family over every certified admissible domain. -/
theorem regular_general_metric_c2_paired_minimal_physical_local_action_family_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (domain : Set (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration))
    (hAdmissible : ∀ direction, direction ∈ domain →
      GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation) :
    Nonempty (GlobalCandidateALocalActionFamily period hPeriod
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
      couplings NonNullFace NullFace) :=
  ⟨regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn
    period hPeriod configuration couplings data plusBase minusBase domain
      hAdmissible⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamily4D
end JanusFormal
