import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D

/-!
# Actual throat constant-fiber third-jet base change

The reverse base-chart transition used by the existing constant-fiber
second-jet core extends pointwise with the genuine third derivative of the
smooth throat atlas.  Its transport truncates exactly to the existing
second-order transport.

No third-order cocycle, physical third-jet atlas, or current descent is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The actual reverse base-chart coefficients through order three at one
point of a two-chart overlap. -/
def actualThroatConstantFiberThirdOrderJetBaseChangeAt
    (first second current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod first)
    (hSecond : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod second) :
    FramedThirdOrderJetConstantFiberBaseChange ThroatCoverCoordinates where
  toFramedSecondOrderJetConstantFiberBaseChange :=
    actualThroatConstantFiberSecondOrderJetBaseChangeAt
      period hPeriod first second current hFirst hSecond
  baseThird :=
    fderiv Real
      (fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod second first)))
      (extChartAt throatCoverModelWithCorners second current)
  baseThird_swap_first_second firstDirection secondDirection thirdDirection :=
    throatGaugeBaseChartTransitionThirdDerivativeAt_swap_first_second
      period hPeriod second first current hSecond hFirst
        firstDirection secondDirection thirdDirection
  baseThird_swap_second_third firstDirection secondDirection thirdDirection :=
    throatGaugeBaseChartTransitionThirdDerivativeAt_swap_second_third
      period hPeriod second first current hSecond hFirst
        firstDirection secondDirection thirdDirection

@[simp]
theorem actualThroatConstantFiberThirdOrderJetBaseChangeAt_baseThird_apply
    (first second current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod first)
    (hSecond : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod second)
    (firstDirection secondDirection thirdDirection :
      ThroatCoverCoordinates) :
    (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        first second current hFirst hSecond).baseThird
          firstDirection secondDirection thirdDirection =
      throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
        second first current firstDirection secondDirection thirdDirection :=
  rfl

/-- Forgetting the transported third derivative recovers exactly the
existing constant-fiber second-order transport. -/
@[simp]
theorem actualThroatConstantFiberThirdOrderJetBaseChangeAt_transport_truncate
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first second current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod first)
    (hSecond : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod second)
    (jet : FramedThirdOrderJet ThroatCoverCoordinates Fiber) :
    ((actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      first second current hFirst hSecond).transport jet).toFramedSecondOrderJet =
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        first second current hFirst hSecond).transport
          jet.toFramedSecondOrderJet :=
  rfl

/-- A genuine self-transition acts as the identity on constant-fiber third
jets. -/
@[simp]
theorem actualThroatConstantFiberThirdOrderJetBaseChangeAt_self_transport
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (index current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod index)
    (jet : FramedThirdOrderJet ThroatCoverCoordinates Fiber) :
    (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      index index current hCurrent hCurrent).transport jet = jet := by
  have hChart : current ∈
      (extChartAt throatCoverModelWithCorners index).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      hCurrent
  have hBaseFirst :
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseFirst =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    change
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseFirst =
          ContinuousLinearMap.id Real ThroatCoverCoordinates
    simpa only [actualThroatConstantFiberSecondOrderJetBaseChangeAt] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod index current hChart
  have hBaseSecond :
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseSecond = 0 := by
    change
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseSecond = 0
    simpa only [actualThroatConstantFiberSecondOrderJetBaseChangeAt] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod index current hChart
  have hBaseThird :
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseThird = 0 := by
    apply ContinuousLinearMap.ext
    intro firstDirection
    apply ContinuousLinearMap.ext
    intro secondDirection
    apply ContinuousLinearMap.ext
    intro thirdDirection
    rw [actualThroatConstantFiberThirdOrderJetBaseChangeAt_baseThird_apply]
    simpa using
      throatGaugeBaseChartTransitionThirdDerivativeAt_self period hPeriod
        index current hChart firstDirection secondDirection thirdDirection
  apply FramedThirdOrderJet.ext_components
  · apply FramedSecondOrderJet.ext_components
    · simp only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_toFramedSecondOrderJet,
        FramedSecondOrderJetConstantFiberBaseChange.transport_value]
    · apply ContinuousLinearMap.ext
      intro direction
      simp only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_firstDerivative_apply]
      rw [hBaseFirst]
      rfl
    · apply ContinuousLinearMap.ext
      intro firstDirection
      apply ContinuousLinearMap.ext
      intro secondDirection
      simp only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_secondDerivative_apply]
      rw [hBaseFirst, hBaseSecond]
      simp
  · apply ContinuousLinearMap.ext
    intro firstDirection
    apply ContinuousLinearMap.ext
    intro secondDirection
    apply ContinuousLinearMap.ext
    intro thirdDirection
    simp only [
      FramedThirdOrderJetConstantFiberBaseChange.transport_thirdDerivative_apply]
    rw [hBaseFirst, hBaseSecond, hBaseThird]
    simp

end
end P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
end JanusFormal
