import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

/-!
# Jacobian equivalences for actual throat base-chart transitions

At a point lying in two extended charts, the Jacobian of the forward chart
transition is a real-linear equivalence.  Its inverse is exactly the Jacobian
of the reverse transition at the corresponding chart coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

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

/-- The Jacobian of a valid throat base-chart transition, packaged with the
Jacobian of the reverse transition as its exact inverse. -/
def throatGaugeBaseChartTransitionJacobianEquivAt
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates := by
  let forward : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
    fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        firstCenter secondCenter)
      (extChartAt throatCoverModelWithCorners firstCenter current)
  let reverse : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
    fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        secondCenter firstCenter)
      (extChartAt throatCoverModelWithCorners secondCenter current)
  have hReverseForward :
      reverse.comp forward =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [forward, reverse,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_inverse
        period hPeriod firstCenter secondCenter current hFirst hSecond
  have hForwardReverse :
      forward.comp reverse =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [forward, reverse,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_inverse
        period hPeriod secondCenter firstCenter current hSecond hFirst
  exact
    { toFun := forward
      invFun := reverse
      left_inv := fun coordinate => by
        have hApply := congrArg
          (fun map : ThroatCoverCoordinates →L[Real]
              ThroatCoverCoordinates => map coordinate)
          hReverseForward
        simpa using hApply
      right_inv := fun coordinate => by
        have hApply := congrArg
          (fun map : ThroatCoverCoordinates →L[Real]
              ThroatCoverCoordinates => map coordinate)
          hForwardReverse
        simpa using hApply
      map_add' := forward.map_add
      map_smul' := forward.map_smul }

@[simp]
theorem throatGaugeBaseChartTransitionJacobianEquivAt_apply
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : ThroatCoverCoordinates) :
    throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter secondCenter current hFirst hSecond direction =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)
        direction :=
  rfl

@[simp]
theorem throatGaugeBaseChartTransitionJacobianEquivAt_symm_apply
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : ThroatCoverCoordinates) :
    (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter secondCenter current hFirst hSecond).symm direction =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          secondCenter firstCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        direction :=
  rfl

@[simp]
theorem throatGaugeBaseChartTransitionJacobianEquivAt_coe
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ⇑(throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter secondCenter current hFirst hSecond) =
      ⇑(fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)) :=
  rfl

@[simp]
theorem throatGaugeBaseChartTransitionJacobianEquivAt_symm_coe
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ⇑(throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter secondCenter current hFirst hSecond).symm =
      ⇑(fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          secondCenter firstCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)) :=
  rfl

@[simp]
theorem throatGaugeBaseChartTransitionJacobianEquivAt_toLinearMap
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
      firstCenter secondCenter current hFirst hSecond).toLinearMap =
      (fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)).toLinearMap :=
  rfl

@[simp]
theorem throatGaugeBaseChartTransitionJacobianEquivAt_symm_toLinearMap
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
      firstCenter secondCenter current hFirst hSecond).symm.toLinearMap =
      (fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          secondCenter firstCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)).toLinearMap :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
end JanusFormal
