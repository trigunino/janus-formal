import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D

/-!
# Actual pointwise throat structured-background core

At one genuine throat point, this gate combines the canonical pointwise
Koszul quadratic formed from the symmetrized transported actual metric
one-jet with the actual pulled-back Candidate-A `U(1)^2` connection jets.
Both fields use the same point and the same gauge-fixed configuration; the
gauge jets additionally use compatible `GlobalCandidateAActionData`.

The tangential quadratic remains conditional on sectorwise
`HasNoTangentialRadical`.  The core deliberately omits `normalQuadratic` and
`physicalNormal`.  It proves no immersion or normal compatibility, no chart
or frame overlap law, no smooth dependence on the point, no global descent,
no equality of the symmetrized derivative with the raw metric derivative, no
identification with a Levi--Civita connection, and no closure of T02.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatStructuredBackgroundSecondJetCore4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- The realized pointwise part of `StructuredBackgroundSecondJet
EuclideanR3`.  Its only missing fields are precisely `normalQuadratic` and
`physicalNormal`, together with symmetry of the former. -/
structure ActualThroatStructuredBackgroundSecondJetCore
    (_configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) where
  point : ProgramPThroatJetBase period hPeriod
  tangentialQuadratic :
    Sector → ContinuousTangentialQuadratic EuclideanR3
  gaugeConnection :
    Sector → Fin 2 →
      FramedSecondOrderJet EuclideanR3 (FramedCovector EuclideanR3)
  tangentialQuadratic_symmetric : ∀ sector first second,
    tangentialQuadratic sector first second =
      tangentialQuadratic sector second first

/-- Combine the actual tangential and Abelian throat data at one common
point.  No independent tangential or gauge field is supplied. -/
def globalCandidateAActualThroatStructuredBackgroundSecondJetCore
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector)) :
    ActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration where
  point := base
  tangentialQuadratic :=
    globalCandidateAActualThroatTangentialConnectionQuadraticAt
      period hPeriod configuration base hTransverse
  gaugeConnection :=
    (globalCandidateAActualThroatGaugeSecondJetCore
      period hPeriod configuration data base).gaugeConnection
  tangentialQuadratic_symmetric := fun sector first second =>
    globalCandidateAActualThroatTangentialConnectionQuadraticAt_symmetric
      period hPeriod configuration base hTransverse sector first second

@[simp]
theorem globalCandidateAActualThroatStructuredBackgroundSecondJetCore_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector)) :
    (globalCandidateAActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration data base hTransverse).point = base :=
  rfl

@[simp]
theorem globalCandidateAActualThroatStructuredBackgroundSecondJetCore_tangentialQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) :
    (globalCandidateAActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration data base hTransverse).tangentialQuadratic
        sector =
      globalCandidateAActualThroatTangentialConnectionQuadraticAt
        period hPeriod configuration base hTransverse sector :=
  rfl

@[simp]
theorem globalCandidateAActualThroatStructuredBackgroundSecondJetCore_gaugeConnection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (base : ProgramPThroatJetBase period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) (component : Fin 2) :
    (globalCandidateAActualThroatStructuredBackgroundSecondJetCore
      period hPeriod configuration data base hTransverse).gaugeConnection
        sector component =
      globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector component base :=
  rfl

end
end P0EFTJanusProgramPActualThroatStructuredBackgroundSecondJetCore4D
end JanusFormal
