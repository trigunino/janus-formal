import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D

/-!
# Conditional completion of the actual bulk structured background

The actual bulk-background core already contains the sectorwise tangential
connection and paired Abelian connection jets.  Completing it to the carrier
interface additionally requires a sectorwise normal quadratic form and a
physical normal coordinate.

Those normal fields are explicit external geometric data here.  This gate
does not extract them from a global configuration, prove that they arise from
an immersion, or select a canonical completion.  In particular, compatibility
with the selected point and chart, either sector metric, an immersion and its
normal trivialization/orientation, or the bulk--throat trace is not proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualBulkStructuredBackgroundCompletion4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Exactly the external normal data missing from the actual bulk-background
core.  No provenance or uniqueness is encoded by this structure. -/
structure ExternalBulkStructuredBackgroundCompletionData where
  normalQuadratic :
    Sector → ContinuousSecondFundamentalForm
      (Tangent := EuclideanR4) (Normal := Real)
  physicalNormal : Sector → Real
  normalQuadratic_symmetric : ∀ sector first second,
    normalQuadratic sector first second =
      normalQuadratic sector second first

/-- Conditionally complete the realized bulk-background core using supplied
external normal geometry. -/
def completeActualBulkStructuredBackgroundSecondJetCore
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualBulkStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalBulkStructuredBackgroundCompletionData) :
    StructuredBackgroundSecondJet EuclideanR4 where
  tangentialQuadratic := core.tangentialQuadratic
  normalQuadratic := completion.normalQuadratic
  gaugeConnection := core.gaugeConnection
  physicalNormal := completion.physicalNormal
  tangentialQuadratic_symmetric := core.tangentialQuadratic_symmetric
  normalQuadratic_symmetric := completion.normalQuadratic_symmetric

@[simp]
theorem completeActualBulkStructuredBackgroundSecondJetCore_tangentialQuadratic
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualBulkStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (completeActualBulkStructuredBackgroundSecondJetCore period hPeriod core
      completion).tangentialQuadratic sector =
      core.tangentialQuadratic sector :=
  rfl

@[simp]
theorem completeActualBulkStructuredBackgroundSecondJetCore_gaugeConnection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualBulkStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) (component : Fin 2) :
    (completeActualBulkStructuredBackgroundSecondJetCore period hPeriod core
      completion).gaugeConnection sector component =
      core.gaugeConnection sector component :=
  rfl

@[simp]
theorem completeActualBulkStructuredBackgroundSecondJetCore_normalQuadratic
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualBulkStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (completeActualBulkStructuredBackgroundSecondJetCore period hPeriod core
      completion).normalQuadratic sector =
      completion.normalQuadratic sector :=
  rfl

@[simp]
theorem completeActualBulkStructuredBackgroundSecondJetCore_physicalNormal
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualBulkStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (completeActualBulkStructuredBackgroundSecondJetCore period hPeriod core
      completion).physicalNormal sector =
      completion.physicalNormal sector :=
  rfl

/-- Conditional background obtained by combining the genuinely extracted
Candidate-A core with explicitly supplied external normal geometry. -/
def globalCandidateAConditionalBulkStructuredBackgroundSecondJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (completion : ExternalBulkStructuredBackgroundCompletionData) :
    StructuredBackgroundSecondJet EuclideanR4 :=
  completeActualBulkStructuredBackgroundSecondJetCore period hPeriod
    (globalCandidateAActualBulkStructuredBackgroundSecondJetCore period hPeriod
      configuration data patch coordinate) completion

@[simp]
theorem globalCandidateAConditionalBulkStructuredBackgroundSecondJet_gaugeConnection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (completion : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) (component : Fin 2) :
    (globalCandidateAConditionalBulkStructuredBackgroundSecondJet period hPeriod
      configuration data patch coordinate completion).gaugeConnection
        sector component =
      globalCandidateABulkGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component patch coordinate :=
  rfl

@[simp]
theorem globalCandidateAConditionalBulkStructuredBackgroundSecondJet_normalQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (completion : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalBulkStructuredBackgroundSecondJet period hPeriod
      configuration data patch coordinate completion).normalQuadratic sector =
      completion.normalQuadratic sector :=
  rfl

end
end P0EFTJanusProgramPActualBulkStructuredBackgroundCompletion4D
end JanusFormal
