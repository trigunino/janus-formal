import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRefinedActualThroatOrientedGaussPhysicalSecondOrderJetAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetLowOrderOrbit4D

/-!
# Actual oriented Gauss throat low-order deck orbit

This gate projects the witness-free actual throat jet to its exact `(II, F)`
data.  Reversing the orientation lift is realized by the residual normal-frame
reflection: the Gauss second fundamental form changes sign while the Abelian
curvature, based at the same physical throat point, is unchanged.

The reduction deliberately forgets `physicalNormal`; no deck transition of
the full fixed-frame physical jet is claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualOrientedGaussThroatLowOrderDeckOrbit4D

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusConcreteAbelianConnectionJet
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusEuclideanStructuredJetActionGroupoidRealization
open P0EFTJanusStructuredJetActionGroupoid
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetLowOrderOrbit4D
open P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D
open P0EFTJanusProgramPRefinedActualThroatOrientedGaussPhysicalSecondOrderJetAssembly4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Exact low-order `(II, F)` projection of the actual oriented throat jet. -/
def globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    LowOrderReducedData EuclideanR3 Real :=
  P0EFTJanusProgramPPhysicalSecondOrderJetLowOrderOrbit4D.ThroatPhysicalSecondOrderJet.toLowOrderReducedData
    (globalCandidateARefinedActualOrientedGaussThroatPhysicalSecondOrderJet
      period hPeriod configuration data boundary hTransverse) sector column

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_secondFundamental
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
      period hPeriod configuration data boundary hTransverse sector column).secondFundamental =
      fun first second =>
        actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
          boundary sector first second :=
  rfl

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_gaugeCurvature_apply
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) (first second : EuclideanR3) :
    (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
      period hPeriod configuration data boundary hTransverse sector column).gaugeCurvature
        first second =
      (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
          period hPeriod data sector column
            (orientationDoubleToThroat period hPeriod boundary)).firstDerivative
          first second -
        (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
          period hPeriod data sector column
            (orientationDoubleToThroat period hPeriod boundary)).firstDerivative
          second first :=
  rfl

theorem globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_secondFundamental_deck
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
      period hPeriod configuration data
        (orientationDeck period hPeriod boundary) hTransverse sector column).secondFundamental =
      fun first second =>
        -(globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
          period hPeriod configuration data boundary hTransverse sector column).secondFundamental
            first second := by
  funext first second
  change
    actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        (orientationDeck period hPeriod boundary) sector first second =
      -actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector first second
  have hDeck := congrArg
    (fun form => form first second)
    (actualThroatSectorGaussNormalQuadraticAt_deck period hPeriod
      configuration hTransverse boundary sector)
  simpa only [neg_apply] using hDeck

@[simp] theorem globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_gaugeCurvature_deck
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
      period hPeriod configuration data
        (orientationDeck period hPeriod boundary) hTransverse sector column).gaugeCurvature =
      (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
        period hPeriod configuration data boundary hTransverse sector column).gaugeCurvature := by
  funext first second
  change
    (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector column
          (orientationDoubleToThroat period hPeriod
            (orientationDeck period hPeriod boundary))).firstDerivative
          first second -
      (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector column
          (orientationDoubleToThroat period hPeriod
            (orientationDeck period hPeriod boundary))).firstDerivative
          second first =
    (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector column
          (orientationDoubleToThroat period hPeriod boundary)).firstDerivative
          first second -
      (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector column
          (orientationDoubleToThroat period hPeriod boundary)).firstDerivative
          second first
  rw [orientationDoubleToThroat_deck]

/-- The residual frame corresponding to reversal of the oriented normal line. -/
def actualOrientedGaussThroatDeckSpinCFrame :
    LowOrderSpinCFrame EuclideanR3 Real :=
  ((1, LinearIsometryEquiv.neg Real), 1)

@[simp] theorem actualOrientedGaussThroatDeckSpinCFrame_normal_apply
    (normal : Real) :
    (actualOrientedGaussThroatDeckSpinCFrame).1.2 normal = -normal :=
  rfl

/-- The actual reduced jet is equivariant for the deck reversal and the
residual normal-frame reflection. -/
theorem globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_deck_equivariant
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    actualOrientedGaussThroatDeckSpinCFrame •
        globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
          period hPeriod configuration data boundary hTransverse sector column =
      globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
        period hPeriod configuration data
          (orientationDeck period hPeriod boundary) hTransverse sector column := by
  change actOnReducedData
      (actualOrientedGaussThroatDeckSpinCFrame).1
      (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
        period hPeriod configuration data boundary hTransverse sector column) = _
  apply LowOrderReducedData.ext
  · funext first second
    change
      -actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
          boundary sector first second =
        actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
          (orientationDeck period hPeriod boundary) sector first second
    have hDeck := congrArg
      (fun form => form first second)
      (actualThroatSectorGaussNormalQuadraticAt_deck period hPeriod
        configuration hTransverse boundary sector)
    simpa only [neg_apply] using hDeck.symm
  · funext first second
    change
      (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
          period hPeriod data sector column
            (orientationDoubleToThroat period hPeriod boundary)).firstDerivative
            first second -
        (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
          period hPeriod data sector column
            (orientationDoubleToThroat period hPeriod boundary)).firstDerivative
            second first =
      (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
          period hPeriod data sector column
            (orientationDoubleToThroat period hPeriod
              (orientationDeck period hPeriod boundary))).firstDerivative
            first second -
        (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
          period hPeriod data sector column
            (orientationDoubleToThroat period hPeriod
              (orientationDeck period hPeriod boundary))).firstDerivative
            second first
    rw [orientationDoubleToThroat_deck]

/-- Every installed residual-frame/SpinC invariant evaluator gives the same
value on the two oriented lifts of the actual throat data. -/
theorem ProjectedLowOrderInvariantEvaluator.actualOrientedGaussThroat_deck_invariant
    {Target : Type*}
    (evaluator : ProjectedLowOrderInvariantEvaluator EuclideanR3 Target)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    reducedObservable evaluator.toFun
        (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
          period hPeriod configuration data
            (orientationDeck period hPeriod boundary) hTransverse sector column) =
      reducedObservable evaluator.toFun
        (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
          period hPeriod configuration data boundary hTransverse sector column) := by
  rw [← globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_deck_equivariant
    period hPeriod configuration data boundary hTransverse sector column]
  exact evaluator.reduced_eq_under_residualSpinC
    actualOrientedGaussThroatDeckSpinCFrame
    (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
      period hPeriod configuration data boundary hTransverse sector column)

/-- Canonical action-groupoid arrow from one oriented lift to its deck mate. -/
def globalCandidateARefinedActualOrientedGaussThroatLowOrderDeckArrow
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (column : Fin 2) :
    ActionArrow (Symmetry := LowOrderSpinCFrame EuclideanR3 Real)
      (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
        period hPeriod configuration data boundary hTransverse sector column)
      (globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData
        period hPeriod configuration data
          (orientationDeck period hPeriod boundary) hTransverse sector column) where
  element := actualOrientedGaussThroatDeckSpinCFrame
  maps_source :=
    globalCandidateARefinedActualOrientedGaussThroatLowOrderReducedData_deck_equivariant
      period hPeriod configuration data boundary hTransverse sector column

end
end P0EFTJanusProgramPActualOrientedGaussThroatLowOrderDeckOrbit4D
end JanusFormal
