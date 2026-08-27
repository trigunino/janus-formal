import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D

/-!
# Arbitrary SpinC trivialization and base-chart overlap for second jets

The same-chart SpinC trivialization law composes with the fixed-trivialization
base-chart chain rule to give the exact value, first-order, and second-order
laws between arbitrary valid trivialization--chart pairs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Arbitrary trivialization--chart germ -/

/-- Changing SpinC trivialization in the source chart and then changing base
chart gives the target local representative as an exact germ. -/
theorem
    d9PrimitiveSpinCSectionTrivializationChartRepresentative_arbitraryTrivializationBaseChartTransition_eventuallyEq
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (sourceIndex targetIndex : D9PrimitiveSpinCIndex period hPeriod)
    (sourceChart targetChart current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod sourceIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod targetIndex)
    (hSourceChart : current ∈
      (extChartAt throatCoverModelWithCorners sourceChart).source)
    (hTargetChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source) :
    (fun coordinate =>
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          sourceIndex targetIndex sourceChart coordinate
        (d9PrimitiveSpinCSectionTrivializationChartRepresentative period
          hPeriod choice state sourceIndex sourceChart coordinate)) =ᶠ[nhds
            (extChartAt throatCoverModelWithCorners sourceChart current)]
      (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
          choice state targetIndex targetChart) ∘
        throatGaugeBaseChartTransition period hPeriod
          sourceChart targetChart := by
  exact
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative_transition_eventuallyEq
      period hPeriod choice state sourceIndex targetIndex sourceChart current
        hCurrent hSourceChart).trans
    (P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionTrivializationChartRepresentative_baseChartTransition_eventuallyEq
      period hPeriod choice state targetIndex sourceChart targetChart current
        hSourceChart hTargetChart)

/-! ## Exact arbitrary trivialization--chart jet laws -/

/-- The target value is the exact SpinC fiber transport of the source value. -/
theorem d9PrimitiveSpinCSectionSecondOrderJet_arbitraryTrivializationBaseChart_value
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (sourceIndex targetIndex : D9PrimitiveSpinCIndex period hPeriod)
    (sourceChart targetChart current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod sourceIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod targetIndex)
    (hSourceChart : current ∈
      (extChartAt throatCoverModelWithCorners sourceChart).source)
    (hTargetChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
      hPeriod choice state targetIndex targetChart current hCurrent.2
        hTargetChart).value =
      d9PrimitiveSpinCCoordChange period hPeriod choice sourceIndex targetIndex
        current
        (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state sourceIndex sourceChart current hCurrent.1
            hSourceChart).value := by
  have hBase :=
    P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value_transition
      period hPeriod choice state targetIndex sourceChart targetChart current
        hCurrent.2 hSourceChart hTargetChart
  exact hBase.symm.trans
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value_transition
      period hPeriod choice state sourceIndex targetIndex sourceChart current
        hCurrent hSourceChart)

/-- Arbitrary trivialization--chart first-order law: the target derivative
pulled back by the base-chart Jacobian equals the varying-transition Leibniz
expression. -/
theorem d9PrimitiveSpinCSectionSecondOrderJet_arbitraryTrivializationBaseChart_firstDerivative_transition
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (sourceIndex targetIndex : D9PrimitiveSpinCIndex period hPeriod)
    (sourceChart targetChart current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod sourceIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod targetIndex)
    (hSourceChart : current ∈
      (extChartAt throatCoverModelWithCorners sourceChart).source)
    (hTargetChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
      hPeriod choice state targetIndex targetChart current hCurrent.2
        hTargetChart).firstDerivative.comp
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              sourceChart targetChart)
            (extChartAt throatCoverModelWithCorners sourceChart current)) =
      (d9PrimitiveSpinCCoordChange period hPeriod choice sourceIndex targetIndex
          current).comp
        (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state sourceIndex sourceChart current hCurrent.1
            hSourceChart).firstDerivative +
      (fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          sourceIndex targetIndex sourceChart)
        (extChartAt throatCoverModelWithCorners sourceChart current)).flip
          (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
            hPeriod choice state sourceIndex sourceChart current hCurrent.1
              hSourceChart).value := by
  have hBase :=
    P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative_transition
      period hPeriod choice state targetIndex sourceChart targetChart current
        hCurrent.2 hSourceChart hTargetChart
  exact hBase.symm.trans
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative_transition
      period hPeriod choice state sourceIndex targetIndex sourceChart current
        hCurrent hSourceChart)

/-- Arbitrary trivialization--chart second-order law. The base-chart Hessian
terms equal the full four-term SpinC transition expression. -/
theorem d9PrimitiveSpinCSectionSecondOrderJet_arbitraryTrivializationBaseChart_secondDerivative_transition_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (sourceIndex targetIndex : D9PrimitiveSpinCIndex period hPeriod)
    (sourceChart targetChart current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod sourceIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod targetIndex)
    (hSourceChart : current ∈
      (extChartAt throatCoverModelWithCorners sourceChart).source)
    (hTargetChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    (first second : ThroatCoverCoordinates) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
      hPeriod choice state targetIndex targetChart current hCurrent.2
        hTargetChart).secondDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              sourceChart targetChart)
            (extChartAt throatCoverModelWithCorners sourceChart current) first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              sourceChart targetChart)
            (extChartAt throatCoverModelWithCorners sourceChart current) second) +
      (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
        hPeriod choice state targetIndex targetChart current hCurrent.2
          hTargetChart).firstDerivative
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  sourceChart targetChart))
              (extChartAt throatCoverModelWithCorners sourceChart current)
                first second) =
      d9PrimitiveSpinCCoordChange period hPeriod choice sourceIndex targetIndex
        current
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state sourceIndex sourceChart current hCurrent.1
            hSourceChart).secondDerivative first second) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            sourceIndex targetIndex sourceChart)
          (extChartAt throatCoverModelWithCorners sourceChart current) first
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state sourceIndex sourceChart current hCurrent.1
            hSourceChart).firstDerivative second) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            sourceIndex targetIndex sourceChart)
          (extChartAt throatCoverModelWithCorners sourceChart current) second
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state sourceIndex sourceChart current hCurrent.1
            hSourceChart).firstDerivative first) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                sourceIndex targetIndex sourceChart) coordinate second)
          (extChartAt throatCoverModelWithCorners sourceChart current) first
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state sourceIndex sourceChart current hCurrent.1
            hSourceChart).value) := by
  have hBase :=
    P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative_transition_apply
      period hPeriod choice state targetIndex sourceChart targetChart current
        hCurrent.2 hSourceChart hTargetChart first second
  exact hBase.symm.trans
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative_transition_apply
      period hPeriod choice state sourceIndex targetIndex sourceChart current
        hCurrent hSourceChart first second)

end
end P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderJetOverlap4D
end JanusFormal
