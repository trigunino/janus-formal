import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Third derivative of the actual throat base-chart transition

The genuine extended-chart transition is smooth on every valid overlap.  This
gate exposes its third Frechet derivative in the three-dimensional throat
model and proves the two adjacent symmetries of that trilinear coefficient.

This is only the geometric base-transition coefficient.  It does not construct
a third-order physical jet carrier, the fiber-transition third derivatives, a
third-jet cocycle, or current descent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

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

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApply := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApply

/-- Third Frechet derivative of the genuine throat base-chart transition at
one point of an overlap.  The first argument differentiates the Hessian-valued
map; the last two are its Hessian directions. -/
def throatGaugeBaseChartTransitionThirdDerivativeAt
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (first second third : ThroatCoverCoordinates) :
    ThroatCoverCoordinates :=
  fderiv Real
      (fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)))
      (extChartAt throatCoverModelWithCorners firstCenter current)
      first second third

/-- The first two directions of the actual throat transition third derivative
commute. -/
theorem throatGaugeBaseChartTransitionThirdDerivativeAt_swap_first_second
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second third : ThroatCoverCoordinates) :
    throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
        firstCenter secondCenter current first second third =
      throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
        firstCenter secondCenter current second first third := by
  have hFirstDerivative :
      ContDiffAt Real 2
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter))
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).fderiv_right
        (m := 2) (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hSymmetric :=
    (hFirstDerivative.isSymmSndFDerivAt (by norm_num)).eq first second
  exact congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates => derivative third) hSymmetric

/-- The last two directions of the actual throat transition third derivative
commute. -/
theorem throatGaugeBaseChartTransitionThirdDerivativeAt_swap_second_third
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second third : ThroatCoverCoordinates) :
    throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
        firstCenter secondCenter current first second third =
      throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
        firstCenter secondCenter current first third second := by
  let transition := throatGaugeBaseChartTransition period hPeriod
    firstCenter secondCenter
  let coordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hTransitionC3 : ContDiffAt Real 3 transition coordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hHessian :
      DifferentiableAt Real
        (fderiv Real (fderiv Real transition)) coordinate :=
    ((hTransitionC3.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let hessianAtSecond : ThroatCoverCoordinates →
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
    fun nearby => fderiv Real (fderiv Real transition) nearby second
  let hessianAtThird : ThroatCoverCoordinates →
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
    fun nearby => fderiv Real (fderiv Real transition) nearby third
  have hHessianAtSecond :
      DifferentiableAt Real hessianAtSecond coordinate := by
    have hApplied := hHessian.clm_apply
      (differentiableAt_const (c := second))
    simpa only [hessianAtSecond] using hApplied
  have hHessianAtThird :
      DifferentiableAt Real hessianAtThird coordinate := by
    have hApplied := hHessian.clm_apply
      (differentiableAt_const (c := third))
    simpa only [hessianAtThird] using hApplied
  have hNearbySymmetry :
      Filter.EventuallyEq (𝓝 coordinate)
        (fun nearby => hessianAtSecond nearby third)
        (fun nearby => hessianAtThird nearby second) := by
    filter_upwards [hTransitionC3.eventually (by norm_num)]
      with nearby hNearby
    exact (hNearby.isSymmSndFDerivAt (𝕜 := Real) (by norm_num)).eq
      second third
  have hDerivativeEquality := hNearbySymmetry.fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates => derivative first) hDerivativeEquality
  have hSecondThird :
      fderiv Real (fun nearby => hessianAtSecond nearby third)
          coordinate first =
        fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first second third := by
    calc
      fderiv Real (fun nearby => hessianAtSecond nearby third)
          coordinate first =
        fderiv Real hessianAtSecond coordinate first third :=
          fderiv_continuousLinearMap_apply_const hessianAtSecond
            coordinate first third hHessianAtSecond
      _ = fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first second third := by
        rw [fderiv_continuousLinearMap_apply_const
          (fderiv Real (fderiv Real transition)) coordinate first second
            hHessian]
  have hThirdSecond :
      fderiv Real (fun nearby => hessianAtThird nearby second)
          coordinate first =
        fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first third second := by
    calc
      fderiv Real (fun nearby => hessianAtThird nearby second)
          coordinate first =
        fderiv Real hessianAtThird coordinate first second :=
          fderiv_continuousLinearMap_apply_const hessianAtThird
            coordinate first second hHessianAtThird
      _ = fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first third second := by
        rw [fderiv_continuousLinearMap_apply_const
          (fderiv Real (fderiv Real transition)) coordinate first third
            hHessian]
  rw [hSecondThird, hThirdSecond] at hApplied
  simpa only [throatGaugeBaseChartTransitionThirdDerivativeAt,
    transition, coordinate] using hApplied

end
end P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D
end JanusFormal
