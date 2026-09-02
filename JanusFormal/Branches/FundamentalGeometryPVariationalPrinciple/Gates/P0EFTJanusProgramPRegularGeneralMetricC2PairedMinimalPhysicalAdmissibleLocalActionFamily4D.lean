import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain4D

/-!
# Canonical admissible paired minimal-physical local action family

The domain is no longer supplied externally: it is exactly the locus where the
paired chart is admissible.  Base compatibility puts zero in this locus, and
exact centre compatibility identifies its zero datum with the original
configuration.  The locus lies inside the open separate-Lorentz domain; its
remaining openness question is precisely the relative-root condition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Exact paired-chart admissibility locus on the minimal physical tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  {direction |
    GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod plusBase
      minusBase direction.1.completeVariation.fullMetricPerturbation}

/-- Base compatibility puts the zero direction in the exact paired locus. -/
theorem zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    (0 : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase := by
  change GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
    plusBase minusBase 0
  exact globalMetricPerturbationPairLorentzChart_zero_admissible period hPeriod
    plusBase minusBase hBase

/-- Exact paired admissibility implies both separate fixed-base Lorentz
conditions.  Thus only the relative-root field distinguishes the exact locus
from the open domain of Gate 363. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_subset_separateLorentzDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase ⊆
      regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
        period hPeriod configuration plusBase minusBase := by
  intro direction hDirection
  exact ⟨hDirection.plus_mem, hDirection.minus_mem⟩

/-- Local action family on the exact paired admissibility locus. -/
def regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    GlobalCandidateALocalActionFamily period hPeriod
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
      couplings NonNullFace NullFace :=
  regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn period hPeriod
    configuration couplings data plusBase minusBase
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
      (fun _ hDirection => hDirection)

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily_domain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase).domain =
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase :=
  rfl

/-- Under exact centre compatibility, the canonical family's zero datum has
the original configuration as first projection. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily_datumAt_zero_configuration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration plusBase minusBase hBase) :
    let hZero :=
      zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration plusBase minusBase hBase
    ((regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase).datumAt
        0 hZero).1 = configuration := by
  exact
    regularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyOn_datumAt_zero_configuration
      period hPeriod configuration couplings data plusBase minusBase hBase
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
      (fun _ hDirection => hDirection)
      (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration plusBase minusBase hBase)
      hCenter

/-- Gate marker: the canonical exact admissibility locus now carries a local
action family containing zero and centred on the original configuration. -/
theorem regular_general_metric_c2_paired_minimal_physical_admissible_local_action_family_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration plusBase minusBase hBase) :
    let family :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
        period hPeriod configuration couplings data plusBase minusBase
    ∃ hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration) ∈ family.domain,
      (family.datumAt 0 hZero).1 = configuration := by
  let hZero :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  exact ⟨hZero,
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily_datumAt_zero_configuration
      period hPeriod configuration couplings data plusBase minusBase hBase
        hCenter⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
end JanusFormal
