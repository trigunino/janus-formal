import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualBulkStructuredBackgroundCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualBulkAbelianNonminimalChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualBulkDiffeomorphismNonminimalChartwiseSecondOrderJetExtraction4D

/-!
# Conditional assembly of the actual bulk physical second-order jet

All metric, Abelian-nonminimal and diffeomorphism-nonminimal slots below are
the genuine chartwise jets of one gauge-fixed global configuration.  The
background uses the genuine Candidate-A tangential and Abelian core, but its
normal quadratic form and physical normal remain explicitly supplied by
`ExternalBulkStructuredBackgroundCompletionData`.

Consequently this is a conditional assembly, not an extraction of the normal
geometry, a canonical choice, an overlap/descent theorem, an atlas-wide jet,
or a closure of T02.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConditionalActualBulkPhysicalSecondOrderJetAssembly4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualBulkStructuredBackgroundCompletion4D
open P0EFTJanusProgramPActualBulkAbelianNonminimalChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualBulkDiffeomorphismNonminimalChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Assemble the actual chartwise bulk slots, conditionally on external normal
geometry completing the structured background. -/
def globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData) :
    BulkPhysicalSecondOrderJet period hPeriod configuration where
  point := globalGaugeFixedBulkMetricJetPoint period hPeriod patch coordinate
  background :=
    globalCandidateAConditionalBulkStructuredBackgroundSecondJet period hPeriod
      configuration data patch coordinate normalData
  metric := fun sector =>
    globalGaugeFixedBulkMetricSecondOrderJetAt period hPeriod configuration
      sector patch coordinate
  abelianGhost :=
    (globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt period hPeriod
      configuration patch coordinate).abelianGhost
  abelianAntighost :=
    (globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt period hPeriod
      configuration patch coordinate).abelianAntighost
  abelianNakanishiLautrup :=
    (globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt period hPeriod
      configuration patch coordinate).abelianNakanishiLautrup
  diffeomorphismGhost :=
    (globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
      period hPeriod configuration patch coordinate).diffeomorphismGhost
  diffeomorphismAntighost :=
    (globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
      period hPeriod configuration patch coordinate).diffeomorphismAntighost
  diffeomorphismNakanishiLautrup :=
    (globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
      period hPeriod configuration patch coordinate).diffeomorphismNakanishiLautrup

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).point =
      patch.coordinateMap (coverToHolonomicEquiv coordinate) :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_background_normalQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).background.normalQuadratic
        sector = normalData.normalQuadratic sector :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_metric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    ((globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).metric sector).value
        first second =
      Matrix.toBilin'
        (localMetricMatrix period hPeriod
          (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
          patch (coverToHolonomicEquiv coordinate))
        (coverToHolonomicEquiv first) (coverToHolonomicEquiv second) :=
  globalGaugeFixedBulkMetricSecondOrderJetAt_value_apply period hPeriod
    configuration sector patch coordinate first second

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_abelianGhost
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).abelianGhost sector =
      globalGaugeFixedBulkAbelianGhostSecondOrderJetAt period hPeriod
        configuration sector patch coordinate :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_abelianAntighost
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).abelianAntighost sector =
      globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt period hPeriod
        configuration sector patch coordinate :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_abelianNakanishiLautrup
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData)
    (sector : Sector) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).abelianNakanishiLautrup
        sector =
      globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt period hPeriod
        configuration sector patch coordinate :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_diffeomorphismGhost
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).diffeomorphismGhost =
      globalGaugeFixedBulkDiffeomorphismGhostSecondOrderJetAt period hPeriod
        configuration patch coordinate :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_diffeomorphismAntighost
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).diffeomorphismAntighost =
      globalGaugeFixedBulkDiffeomorphismAntighostSecondOrderJetAt period hPeriod
        configuration patch coordinate :=
  rfl

@[simp]
theorem globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt_diffeomorphismNakanishiLautrup
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates)
    (normalData : ExternalBulkStructuredBackgroundCompletionData) :
    (globalCandidateAConditionalActualBulkPhysicalSecondOrderJetAt period hPeriod
      configuration data patch coordinate normalData).diffeomorphismNakanishiLautrup =
      globalGaugeFixedBulkDiffeomorphismNakanishiLautrupSecondOrderJetAt
        period hPeriod configuration patch coordinate :=
  rfl

end
end P0EFTJanusProgramPConditionalActualBulkPhysicalSecondOrderJetAssembly4D
end JanusFormal
