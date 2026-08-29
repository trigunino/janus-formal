import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D

/-!
# Compatibility of the concrete semidirect throat-gauge jet transport

The explicit inverse-base/forward-frame semidirect formula produces, from
every arbitrary source jet, the unique direct-compatible representative at
the prescribed target frame and chart anchors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

private abbrev CovectorEnd :=
  FramedCovector ThroatCoverCoordinates →L[Real]
    FramedCovector ThroatCoverCoordinates

local instance covectorEndNormedAddCommGroup :
    NormedAddCommGroup CovectorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorEndNormedSpace : NormedSpace Real CovectorEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorEnd

local instance covectorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point direction : X) (value : Y)
    (hField : DifferentiableAt Real field point) :
    fderiv Real (fun current ↦ field current value) point direction =
      fderiv Real field point direction value := by
  have hDerivative :=
    fderiv_clm_apply hField (differentiableAt_const (c := value))
  have hApplied := congrArg
    (fun derivative : X →L[Real] Z ↦ derivative direction) hDerivative
  simpa using hApplied

private theorem semidirectFirst_inverse
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (Ainv : X →L[Real] X)
    (D Dinv : V →L[Real] V)
    (E Einv : X → V →L[Real] V)
    (p₀ q₀ : V) (p₁ q₁ : X →L[Real] V)
    (hD : Dinv.comp D = ContinuousLinearMap.id Real V)
    (hE : ∀ direction, Dinv.comp (E direction) +
      (Einv direction).comp D = 0)
    (hq₀ : q₀ = D p₀)
    (hq₁ : ∀ direction,
      q₁ direction = D (p₁ (Ainv direction)) + E direction p₀)
    (direction : X) :
    p₁ (Ainv direction) = Dinv (q₁ direction) + Einv direction q₀ := by
  have hDApply (value : V) : Dinv (D value) = value := by
    have hApplied := congrArg (fun map : V →L[Real] V ↦ map value) hD
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hEApply (value : V) :
      Dinv (E direction value) + Einv direction (D value) = 0 := by
    have hApplied := congrArg
      (fun map : V →L[Real] V ↦ map value) (hE direction)
    simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply]
      using hApplied
  rw [hq₁ direction, hq₀, map_add, hDApply]
  calc
    p₁ (Ainv direction) = p₁ (Ainv direction) + 0 := by simp
    _ = p₁ (Ainv direction) +
        (Dinv (E direction p₀) + Einv direction (D p₀)) := by
          rw [hEApply]
    _ = p₁ (Ainv direction) + Dinv (E direction p₀) +
        Einv direction (D p₀) := by abel

private theorem semidirectSecond_inverse
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (Ainv : X →L[Real] X) (Binv : X → X → X)
    (D Dinv : V →L[Real] V)
    (E Einv : X → V →L[Real] V)
    (F Finv : X → X → V →L[Real] V)
    (p₀ q₀ : V) (p₁ q₁ : X →L[Real] V)
    (p₂ q₂ : X →L[Real] X →L[Real] V)
    (hD : Dinv.comp D = ContinuousLinearMap.id Real V)
    (hE : ∀ direction, Dinv.comp (E direction) +
      (Einv direction).comp D = 0)
    (hF : ∀ first second value,
      Dinv (F first second value) +
      Einv first (E second value) + Einv second (E first value) +
      Finv first second (D value) = 0)
    (hq₀ : q₀ = D p₀)
    (hq₁ : ∀ direction,
      q₁ direction = D (p₁ (Ainv direction)) + E direction p₀)
    (hq₂ : ∀ first second,
      q₂ first second =
        D (p₂ (Ainv first) (Ainv second)) +
        D (p₁ (Binv first second)) +
        E first (p₁ (Ainv second)) +
        E second (p₁ (Ainv first)) + F first second p₀)
    (first second : X) :
    p₂ (Ainv first) (Ainv second) + p₁ (Binv first second) =
      Dinv (q₂ first second) + Einv first (q₁ second) +
        Einv second (q₁ first) + Finv first second q₀ := by
  have hDApply (value : V) : Dinv (D value) = value := by
    have hApplied := congrArg (fun map : V →L[Real] V ↦ map value) hD
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hEApply (direction : X) (value : V) :
      Dinv (E direction value) + Einv direction (D value) = 0 := by
    have hApplied := congrArg
      (fun map : V →L[Real] V ↦ map value) (hE direction)
    simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply]
      using hApplied
  symm
  calc
    Dinv (q₂ first second) + Einv first (q₁ second) +
          Einv second (q₁ first) + Finv first second q₀ =
        p₂ (Ainv first) (Ainv second) + p₁ (Binv first second) +
        (Dinv (E first (p₁ (Ainv second))) +
          Einv first (D (p₁ (Ainv second)))) +
        (Dinv (E second (p₁ (Ainv first))) +
          Einv second (D (p₁ (Ainv first)))) +
        (Dinv (F first second p₀) + Einv first (E second p₀) +
          Einv second (E first p₀) + Finv first second (D p₀)) := by
            rw [hq₂ first second, hq₁ second, hq₁ first, hq₀]
            simp only [map_add, hDApply]
            abel
    _ = p₂ (Ainv first) (Ainv second) + p₁ (Binv first second) := by
      rw [hEApply first, hEApply second, hF first second]
      simp

/-! ## Exact compatibility of the concrete transport -/

/-- The concrete semidirect transport sends every arbitrary source jet to a
direct-compatible representative at the requested target anchors. -/
theorem throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    DirectTransitionCompatible period hPeriod source
      (throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
        source target) := by
  let transported :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
      source target
  let Ainv := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let Binv (first second : ThroatCoverCoordinates) := fderiv Real
    (fderiv Real (throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
      first second
  let D : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current
  let Dinv : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      target.frameAnchor source.frameAnchor current
  let E (direction : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      source.frameAnchor target.frameAnchor target.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current) direction
  let Einv (direction : ThroatCoverCoordinates) := fderiv Real
    (throatGaugeCovectorTransitionCenteredChart period hPeriod
      target.frameAnchor source.frameAnchor target.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current) direction
  let F (first second : ThroatCoverCoordinates) :=
    throatGaugeCovectorTargetTransitionSecondDerivativeAt period hPeriod
      source target first second
  let Finv (first second : ThroatCoverCoordinates) := fderiv Real
    (fun coordinate => fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        target.frameAnchor source.frameAnchor target.chartAnchor)
      coordinate second)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current) first
  have hD : Dinv.comp D = ContinuousLinearMap.id Real
      (FramedCovector ThroatCoverCoordinates) := by
    apply ContinuousLinearMap.ext
    intro covector
    have hCocycle := congrArg
      (fun transition : FramedCovector ThroatCoverCoordinates ≃L[Real]
          FramedCovector ThroatCoverCoordinates ↦ transition covector)
      (throatGaugeCovectorTrivializationTransitionAt_cocycle period hPeriod
        source.frameAnchor target.frameAnchor source.frameAnchor current
          ⟨source.frame_mem, target.frame_mem, source.frame_mem⟩)
    have hSelf :
        throatGaugeCovectorTrivializationTransitionAt period hPeriod
            source.frameAnchor source.frameAnchor current covector = covector := by
      simpa only [throatGaugeCovectorTransitionCenteredChart,
        (extChartAt throatCoverModelWithCorners source.chartAnchor).left_inv
          source.chart_mem, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearMap.id_apply] using congrArg
        (fun transition : FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates ↦ transition covector)
        (throatGaugeCovectorTransitionCenteredChart_self period hPeriod
          source.frameAnchor source.chartAnchor current source.frame_mem
            source.chart_mem)
    simpa only [D, Dinv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, hSelf] using hCocycle
  have hBaseSelfFirst :
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hE : ∀ direction, Dinv.comp (E direction) +
      (Einv direction).comp D = 0 := by
    intro direction
    have hInverse :=
      throatGaugeFrameBaseChartTransition_firstDerivative_inverse period hPeriod
        source.frameAnchor target.frameAnchor target.chartAnchor
          target.chartAnchor current ⟨source.frame_mem, target.frame_mem⟩
            target.chart_mem target.chart_mem direction
    rw [hBaseSelfFirst] at hInverse
    simpa only [D, Dinv, E, Einv,
      throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
        target.chart_mem,
      ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe] using hInverse
  have hForwardDerivative : DifferentiableAt Real
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor))
      (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
    have hSmooth : ((1 : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω) := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact
      ((throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
        period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
          current ⟨source.frame_mem, target.frame_mem⟩ target.chart_mem).fderiv_right
            (m := 1) hSmooth).differentiableAt (by norm_num)
  have hFBridge (first second : ThroatCoverCoordinates) :
      fderiv Real
          (fun coordinate => fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              source.frameAnchor target.frameAnchor target.chartAnchor)
            coordinate second)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first = F first second := by
    simpa only [F, throatGaugeCovectorTargetTransitionSecondDerivativeAt] using
      fderiv_clm_apply_const_apply
        (fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          first second hForwardDerivative
  have hBaseDerivative : DifferentiableAt Real
      (fderiv Real (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor target.chartAnchor))
      (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
    ((throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      target.chartAnchor target.chartAnchor current target.chart_mem
        target.chart_mem).fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)
  have hBaseSelfSecondApplied (first second : ThroatCoverCoordinates) :
      fderiv Real
          (fun coordinate => fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor target.chartAnchor) coordinate second)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first = 0 := by
    rw [fderiv_clm_apply_const_apply
      (fderiv Real (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor target.chartAnchor))
      (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second hBaseDerivative]
    have hSelf :=
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod target.chartAnchor current target.chart_mem
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative,
      zero_apply] using congrArg
        (fun derivative : ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates ↦
          derivative first second) hSelf
  have hF : ∀ first second value,
      Dinv (F first second value) +
      Einv first (E second value) + Einv second (E first value) +
      Finv first second (D value) = 0 := by
    intro first second value
    have hInverse :=
      throatGaugeFrameBaseChartTransition_secondDerivative_inverse_apply
        period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
          target.chartAnchor current ⟨source.frame_mem, target.frame_mem⟩
            target.chart_mem target.chart_mem first second value
    rw [hBaseSelfFirst] at hInverse
    simp only [ContinuousLinearMap.id_apply] at hInverse
    rw [hFBridge first second, hBaseSelfSecondApplied first second] at hInverse
    simpa only [D, Dinv, E, Einv, Finv,
      throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
        target.chart_mem,
      ContinuousLinearEquiv.coe_coe, map_zero, zero_apply, add_zero] using hInverse
  have hTransportValue : transported.jet.value = D source.jet.value := by
    rfl
  have hTransportFirst : ∀ direction,
      transported.jet.firstDerivative direction =
        D (source.jet.firstDerivative (Ainv direction)) +
          E direction source.jet.value := by
    intro direction
    rfl
  have hTransportSecond : ∀ first second,
      transported.jet.secondDerivative first second =
        D (source.jet.secondDerivative (Ainv first) (Ainv second)) +
        D (source.jet.firstDerivative (Binv first second)) +
        E first (source.jet.firstDerivative (Ainv second)) +
        E second (source.jet.firstDerivative (Ainv first)) +
        F first second source.jet.value := by
    intro first second
    rfl
  have hReverse : DirectTransitionCompatible period hPeriod transported source := by
    constructor
    · have hApplied := congrArg
        (fun map : FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates ↦ map source.jet.value) hD
      rw [hTransportValue]
      simpa only [transported,
        throatGaugeSecondOrderJetSemidirectTargetPresentationAt, D, Dinv,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe]
        using hApplied.symm
    · apply ContinuousLinearMap.ext
      intro direction
      exact semidirectFirst_inverse Ainv D Dinv E Einv
        source.jet.value transported.jet.value source.jet.firstDerivative
          transported.jet.firstDerivative hD hE hTransportValue
            hTransportFirst direction
    · intro first second
      exact semidirectSecond_inverse Ainv Binv D Dinv E Einv F Finv
        source.jet.value transported.jet.value source.jet.firstDerivative
          transported.jet.firstDerivative source.jet.secondDerivative
            transported.jet.secondDerivative hD hE hF hTransportValue
              hTransportFirst hTransportSecond first second
  exact directTransitionCompatible_symm period hPeriod hReverse

/-- There is an explicit transported representative at any prescribed valid
target frame/chart pair, and it is directly compatible with the source. -/
theorem exists_directCompatible_semidirectRepresentativeAt_targetAnchors
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    ∃ representative : GaugePresentationAt period hPeriod current,
      representative.frameAnchor = target.frameAnchor ∧
      representative.chartAnchor = target.chartAnchor ∧
      representative.jet =
        throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
          source target source.jet ∧
      DirectTransitionCompatible period hPeriod source representative := by
  refine ⟨throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
    source target, rfl, rfl, rfl, ?_⟩
  exact
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
      period hPeriod source target

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportCompatibility4D
end JanusFormal
