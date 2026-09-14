import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D

/-!
# Actual throat base-chart Jacobian density cocycle

The absolute determinant of the genuine throat base-chart Jacobian is a
strictly positive density cocycle.  Reversing the transition supplies its
reciprocal factor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualThroatBaseChartJacobianDensityCocycle4D

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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D

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

/-- Absolute Jacobian factor of a genuine throat base-chart transition. -/
def programPT06ActualThroatBaseChartJacobianDensityAt
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) : Real :=
  |((LinearEquiv.det
    (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
      firstCenter secondCenter current hFirst hSecond) : Realˣ) : Real)|

/-- Every valid base-chart Jacobian density is strictly positive. -/
theorem programPT06ActualThroatBaseChartJacobianDensityAt_pos
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    0 < programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
      firstCenter secondCenter current hFirst hSecond := by
  unfold programPT06ActualThroatBaseChartJacobianDensityAt
  exact abs_pos.mpr (Units.ne_zero _)

theorem programPT06ActualThroatBaseChartJacobianEquivAt_trans
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (hThird : current ∈
      (extChartAt throatCoverModelWithCorners thirdCenter).source) :
    throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter thirdCenter current hFirst hThird =
      (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter secondCenter current hFirst hSecond).trans
        (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          secondCenter thirdCenter current hSecond hThird) := by
  apply LinearEquiv.ext
  intro direction
  have hCocycle :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
      period hPeriod firstCenter secondCenter thirdCenter current
        hFirst hSecond hThird
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates => derivative direction) hCocycle
  simpa only [
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    ContinuousLinearMap.comp_apply,
    LinearEquiv.trans_apply,
    throatGaugeBaseChartTransitionJacobianEquivAt_apply] using hApplied

/-- The Jacobian equivalence of a self-transition is the identity. -/
@[simp]
theorem programPT06ActualThroatBaseChartJacobianEquivAt_self
    (center current : EffectiveThroat period hPeriod)
    (hCenter : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        center center current hCenter hCenter =
      LinearEquiv.refl Real ThroatCoverCoordinates := by
  apply LinearEquiv.ext
  intro direction
  have hSelf := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates => derivative direction)
    (throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
      period hPeriod center current hCenter)
  simpa only [
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionJacobianEquivAt_apply,
    ContinuousLinearMap.id_apply,
    LinearEquiv.refl_apply] using hSelf

/-- A base chart has unit Jacobian density relative to itself. -/
@[simp]
theorem programPT06ActualThroatBaseChartJacobianDensityAt_self
    (center current : EffectiveThroat period hPeriod)
    (hCenter : current ∈
      (extChartAt throatCoverModelWithCorners center).source) :
    programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
      center center current hCenter hCenter = 1 := by
  simp [programPT06ActualThroatBaseChartJacobianDensityAt]

/-- Absolute Jacobian densities multiply on triple chart overlaps. -/
theorem programPT06ActualThroatBaseChartJacobianDensityAt_comp
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (hThird : current ∈
      (extChartAt throatCoverModelWithCorners thirdCenter).source) :
    programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
        firstCenter thirdCenter current hFirst hThird =
      programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
          firstCenter secondCenter current hFirst hSecond *
        programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
          secondCenter thirdCenter current hSecond hThird := by
  unfold programPT06ActualThroatBaseChartJacobianDensityAt
  rw [programPT06ActualThroatBaseChartJacobianEquivAt_trans period hPeriod
    firstCenter secondCenter thirdCenter current hFirst hSecond hThird,
    LinearEquiv.det_trans]
  simp only [Units.val_mul, abs_mul, mul_comm]

/-- Forward and reverse Jacobian density factors are reciprocal. -/
theorem programPT06ActualThroatBaseChartJacobianDensityAt_reverse_mul
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
        firstCenter secondCenter current hFirst hSecond *
      programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
        secondCenter firstCenter current hSecond hFirst = 1 := by
  rw [← programPT06ActualThroatBaseChartJacobianDensityAt_comp period hPeriod
    firstCenter secondCenter firstCenter current hFirst hSecond hFirst]
  exact programPT06ActualThroatBaseChartJacobianDensityAt_self
    period hPeriod firstCenter current hFirst

end
end P0EFTJanusProgramPT06ActualThroatBaseChartJacobianDensityCocycle4D
end JanusFormal
