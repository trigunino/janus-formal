import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatPacketChartwiseSecondOrderJetExtraction4D

/-!
# Conditional assembly of the actual throat physical second-order jet

The induced metrics, primitive SpinC matter and LL fields below are the
genuine chartwise jets of one gauge-fixed global configuration, all extracted
in the extended throat chart centered at the same point.

The entire `StructuredBackgroundSecondJet EuclideanR3` is external data.  It
is not extracted, canonical, or proved compatible with the selected point,
chart, metric, immersion, normal convention, or throat-coordinate frame.
This gate proves no chart or SpinC-trivialization overlap law, no descent to a
global jet bundle, and no closure of T02.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConditionalActualThroatPhysicalSecondOrderJetAssembly4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatPacketChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Assemble every actual throat slot at one chart center, conditionally on a
fully external structured background. -/
def globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    ThroatPhysicalSecondOrderJet period hPeriod configuration where
  point := base
  background := background
  inducedMetric := fun sector =>
    globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
      sector base
  spinCMatter :=
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
      base hBase).spinCMatter
  llAuxMetric :=
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
      base hBase).llAuxMetric
  llMeasure :=
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
      base hBase).llMeasure
  llField :=
    (actualThroatPacketSecondOrderJetsAt period hPeriod configuration index
      base hBase).llField

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    (globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).point = base :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_background
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    (globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).background =
        background :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_inducedMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3)
    (sector : Sector) (first second : ThroatCoverCoordinates) :
    ((globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).inducedMetric
        sector).value first second =
      (globalGaugeFixedInducedMetricBySector
        period hPeriod configuration sector).tensor base
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base).symm base first)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base).symm base second) :=
  globalGaugeFixedThroatMetricSecondOrderJetAt_value_apply period hPeriod
    configuration sector base first second

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_spinCMatter_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3)
    (sector : Sector) :
    ((globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).spinCMatter
        sector).value =
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
        (configuration.physical.spinCMatter sector) index base :=
  actualThroatPacketSecondOrderJetsAt_spinCMatter_value period hPeriod
    configuration index base hBase sector

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_llAuxMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    (globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).llAuxMetric.value =
      configuration.physical.coefficientFields.llAuxMetric base :=
  actualThroatPacketSecondOrderJetsAt_llAuxMetric_value period hPeriod
    configuration index base hBase

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_llMeasure_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    (globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).llMeasure.value =
      configuration.physical.coefficientFields.llMeasure base :=
  actualThroatPacketSecondOrderJetsAt_llMeasure_value period hPeriod
    configuration index base hBase

@[simp]
theorem globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_llField_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    (globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background).llField.value =
      configuration.physical.coefficientFields.llField base :=
  actualThroatPacketSecondOrderJetsAt_llField_value period hPeriod
    configuration index base hBase

/-- Sum-carrier wrapper for the same conditional throat assembly. -/
def globalCandidateAConditionalActualThroatPhysicalSecondOrderJetCarrierAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (background : StructuredBackgroundSecondJet EuclideanR3) :
    ProgramPPhysicalSecondOrderJetCarrier period hPeriod configuration :=
  ProgramPPhysicalSecondOrderJetCarrier.throat
    (globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration index base hBase background)

end
end P0EFTJanusProgramPConditionalActualThroatPhysicalSecondOrderJetAssembly4D
end JanusFormal
