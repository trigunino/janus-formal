import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D

/-!
# Actual combined throat matter/LL chartwise jets

At one throat point, this gate combines the genuine primitive SpinC and LL
second-order jets extracted from the same global gauge-fixed configuration.

This does not add a background or metric jet, construct the complete throat
carrier, or assert chart/trivialization overlap laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatPacketChartwiseSecondOrderJetExtraction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D
open P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- The actual primitive SpinC and LL jets of one gauge-fixed configuration,
in one throat chart and one primitive SpinC trivialization. -/
def actualThroatPacketSecondOrderJetsAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    FixedTrivializationThroatSecondOrderJets where
  spinCMatter :=
    globalGaugeFixedSpinCMatterSecondOrderJetsAt period hPeriod configuration
      index base hBase
  llAuxMetric :=
    (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration base).llAuxMetric
  llMeasure :=
    (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration base).llMeasure
  llField :=
    (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration base).llField

@[simp]
theorem actualThroatPacketSecondOrderJetsAt_spinCMatter_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (sector : Sector) :
    ((actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
        base hBase).spinCMatter sector).value =
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
        (configuration.physical.spinCMatter sector) index base := by
  exact globalGaugeFixedSpinCMatterSecondOrderJetsAt_value period hPeriod
    configuration index base hBase sector

@[simp]
theorem actualThroatPacketSecondOrderJetsAt_llAuxMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
        base hBase).llAuxMetric.value =
      configuration.physical.coefficientFields.llAuxMetric base := by
  exact
    globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt_llAuxMetric_value
      period hPeriod configuration base

@[simp]
theorem actualThroatPacketSecondOrderJetsAt_llMeasure_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
        base hBase).llMeasure.value =
      configuration.physical.coefficientFields.llMeasure base := by
  exact
    globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt_llMeasure_value
      period hPeriod configuration base

@[simp]
theorem actualThroatPacketSecondOrderJetsAt_llField_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
        base hBase).llField.value =
      configuration.physical.coefficientFields.llField base := by
  exact
    globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt_llField_value
      period hPeriod configuration base

end
end P0EFTJanusProgramPActualThroatPacketChartwiseSecondOrderJetExtraction4D
end JanusFormal
