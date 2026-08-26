import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatStructuredBackgroundCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConditionalActualThroatPhysicalSecondOrderJetAssembly4D

/-!
# Refined conditional assembly of the actual throat physical second-order jet

This gate reuses the existing actual throat assembly with the refined
structured background.  The induced metrics, SpinC matter, LL packet,
pointwise Koszul quadratic of the symmetrized transported metric one-jet, and
pulled-back Candidate-A `U(1)^2` connection jets are all built at the same
genuine throat point.

The construction remains conditional on sectorwise
`HasNoTangentialRadical`, compatible `GlobalCandidateAActionData`, a SpinC
chart containing the point, and external normal completion data.  Only the
sectorwise normal quadratic, its symmetry proof, and physical normal
coordinate remain externally supplied.  No immersion provenance, normal
normalization or orientation, compatibility with the induced metric or
throat inclusion, equality with the raw metric derivative, identification
with a Levi--Civita connection, overlap law, global descent, or closure of
T02 is proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRefinedConditionalActualThroatPhysicalSecondOrderJetAssembly4D

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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatPacketChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D
open P0EFTJanusProgramPActualThroatStructuredBackgroundCompletion4D
open P0EFTJanusProgramPConditionalActualThroatPhysicalSecondOrderJetAssembly4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Assemble all actual throat slots at one point while supplying only the
normal part of the structured background externally. -/
def globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    ThroatPhysicalSecondOrderJet period hPeriod configuration :=
  globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt
    period hPeriod configuration index base hBase
      (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion)

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).point = base :=
  rfl

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_background
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).background =
      globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion :=
  rfl

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_background_tangentialQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).background.tangentialQuadratic sector =
      globalCandidateAActualThroatTangentialConnectionQuadraticAt
        period hPeriod configuration base hTransverse sector :=
  rfl

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_background_gaugeConnection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) (component : Fin 2) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).background.gaugeConnection sector component =
      globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector component base :=
  rfl

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_background_normalQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).background.normalQuadratic sector =
      completion.normalQuadratic sector :=
  rfl

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_background_physicalNormal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).background.physicalNormal sector =
      completion.physicalNormal sector :=
  rfl

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_inducedMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) (first second : ThroatCoverCoordinates) :
    ((globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).inducedMetric sector).value first second =
      (globalGaugeFixedInducedMetricBySector
        period hPeriod configuration sector).tensor base
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base).symm base first)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base).symm base second) :=
  globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_inducedMetric_value
    period hPeriod configuration index base hBase
      (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion)
      sector first second

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_spinCMatter_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    ((globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).spinCMatter sector).value =
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
        (configuration.physical.spinCMatter sector) index base :=
  globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_spinCMatter_value
    period hPeriod configuration index base hBase
      (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion) sector

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_llAuxMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).llAuxMetric.value =
      configuration.physical.coefficientFields.llAuxMetric base :=
  globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_llAuxMetric_value
    period hPeriod configuration index base hBase
      (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion)

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_llMeasure_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).llMeasure.value =
      configuration.physical.coefficientFields.llMeasure base :=
  globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_llMeasure_value
    period hPeriod configuration index base hBase
      (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion)

@[simp]
theorem globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt_llField_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion).llField.value =
      configuration.physical.coefficientFields.llField base :=
  globalCandidateAConditionalActualThroatPhysicalSecondOrderJetAt_llField_value
    period hPeriod configuration index base hBase
      (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
        period hPeriod configuration data base hTransverse completion)

/-- Sum-carrier wrapper for the refined conditional throat assembly. -/
def globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetCarrierAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    ProgramPPhysicalSecondOrderJetCarrier period hPeriod configuration :=
  ProgramPPhysicalSecondOrderJetCarrier.throat
    (globalCandidateARefinedConditionalActualThroatPhysicalSecondOrderJetAt
      period hPeriod configuration data index base hBase hTransverse
        completion)

end
end P0EFTJanusProgramPRefinedConditionalActualThroatPhysicalSecondOrderJetAssembly4D
end JanusFormal
