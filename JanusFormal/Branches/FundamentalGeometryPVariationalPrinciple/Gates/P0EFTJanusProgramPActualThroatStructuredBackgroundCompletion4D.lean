import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatStructuredBackgroundSecondJetCore4D

/-!
# Conditional completion of the actual throat structured background

The actual-input throat-background core already contains the pointwise
Koszul quadratic formed from the symmetrized transported metric one-jet and
the pulled-back Candidate-A `U(1)^2` connection jets.  Completing it to
`StructuredBackgroundSecondJet EuclideanR3` requires only a sectorwise normal
quadratic, its symmetry proof, and a physical normal coordinate.

Those normal fields are explicit external data here.  This gate does not
extract them from an immersion, prove metric orthogonality or unit length,
choose an orientation, or prove compatibility with the selected point,
induced metrics, tangential connection, gauge fields, or throat inclusion.
It proves no overlap law, global descent, canonical completion, or closure of
T02, and does not identify the tangential quadratic with a Levi--Civita
connection for the raw metric derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatStructuredBackgroundCompletion4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D
open P0EFTJanusProgramPActualThroatStructuredBackgroundSecondJetCore4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Exactly the external normal data missing from the actual throat core.
No geometric provenance, compatibility, normalization, or uniqueness is
encoded by this structure. -/
structure ExternalThroatStructuredBackgroundCompletionData where
  normalQuadratic :
    Sector → ContinuousSecondFundamentalForm
      (Tangent := EuclideanR3) (Normal := Real)
  physicalNormal : Sector → Real
  normalQuadratic_symmetric : ∀ sector first second,
    normalQuadratic sector first second =
      normalQuadratic sector second first

/-- Conditionally complete a realized throat-background core using supplied
external normal geometry. -/
def completeActualThroatStructuredBackgroundSecondJetCore
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    StructuredBackgroundSecondJet EuclideanR3 where
  tangentialQuadratic := core.tangentialQuadratic
  normalQuadratic := completion.normalQuadratic
  gaugeConnection := core.gaugeConnection
  physicalNormal := completion.physicalNormal
  tangentialQuadratic_symmetric := core.tangentialQuadratic_symmetric
  normalQuadratic_symmetric := completion.normalQuadratic_symmetric

@[simp]
theorem completeActualThroatStructuredBackgroundSecondJetCore_tangentialQuadratic
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (completeActualThroatStructuredBackgroundSecondJetCore
      period hPeriod core completion).tangentialQuadratic sector =
      core.tangentialQuadratic sector :=
  rfl

@[simp]
theorem completeActualThroatStructuredBackgroundSecondJetCore_gaugeConnection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) (component : Fin 2) :
    (completeActualThroatStructuredBackgroundSecondJetCore
      period hPeriod core completion).gaugeConnection sector component =
      core.gaugeConnection sector component :=
  rfl

@[simp]
theorem completeActualThroatStructuredBackgroundSecondJetCore_normalQuadratic
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (completeActualThroatStructuredBackgroundSecondJetCore
      period hPeriod core completion).normalQuadratic sector =
      completion.normalQuadratic sector :=
  rfl

@[simp]
theorem completeActualThroatStructuredBackgroundSecondJetCore_physicalNormal
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (core : ActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration)
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (completeActualThroatStructuredBackgroundSecondJetCore
      period hPeriod core completion).physicalNormal sector =
      completion.physicalNormal sector :=
  rfl

/-- Conditional structured background whose tangential and Abelian slots are
actual Candidate-A data at `base`, while only its normal slots are supplied
externally. -/
def globalCandidateAConditionalThroatStructuredBackgroundSecondJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData) :
    StructuredBackgroundSecondJet EuclideanR3 :=
  completeActualThroatStructuredBackgroundSecondJetCore period hPeriod
    (globalCandidateAActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration data base hTransverse) completion

@[simp]
theorem globalCandidateAConditionalThroatStructuredBackgroundSecondJet_tangentialQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
      period hPeriod configuration data base hTransverse completion).tangentialQuadratic
        sector =
      globalCandidateAActualThroatTangentialConnectionQuadraticAt
        period hPeriod configuration base hTransverse sector :=
  rfl

@[simp]
theorem globalCandidateAConditionalThroatStructuredBackgroundSecondJet_gaugeConnection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) (component : Fin 2) :
    (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
      period hPeriod configuration data base hTransverse completion).gaugeConnection
        sector component =
      globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector component base :=
  rfl

@[simp]
theorem globalCandidateAConditionalThroatStructuredBackgroundSecondJet_normalQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
      period hPeriod configuration data base hTransverse completion).normalQuadratic
        sector = completion.normalQuadratic sector :=
  rfl

@[simp]
theorem globalCandidateAConditionalThroatStructuredBackgroundSecondJet_physicalNormal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (completion : ExternalThroatStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalThroatStructuredBackgroundSecondJet
      period hPeriod configuration data base hTransverse completion).physicalNormal
        sector = completion.physicalNormal sector :=
  rfl

end
end P0EFTJanusProgramPActualThroatStructuredBackgroundCompletion4D
end JanusFormal
