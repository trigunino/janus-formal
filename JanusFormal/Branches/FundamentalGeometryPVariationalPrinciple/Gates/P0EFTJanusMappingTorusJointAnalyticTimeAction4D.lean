import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteTimeFlow4D

/-!
# Joint analyticity of the complete D8 time action

The existing time-flow gate proves analyticity of every fixed-time slice.
This gate proves the stronger action-map statement: time and spacetime point
vary jointly analytically on `ℝ × D8`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusJointAnalyticTimeAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusReflectionFixedThroat

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The action map with time and quotient point as a single input. -/
def effectiveJointTimeFlow
    (input : Real × EffectiveQuotient period hPeriod) :
    EffectiveQuotient period hPeriod :=
  effectiveTimeFlow period hPeriod input.1 input.2

/-- Time translation is jointly analytic already on the product cover. -/
theorem effectiveCoverJointTimeTranslation_contMDiff :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ω
      (fun input : Real × EffectiveCover period hPeriod =>
        coverTimeTranslation (sphereData period hPeriod) input.1 input.2) := by
  let productEquiv := coverHomeomorphProd (sphereData period hPeriod)
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
    productEquiv
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ω
    productEquiv
  have hFiber : ContMDiff coverModelWithCorners (𝓡 3) ω
      (fun point : EffectiveCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hTo
  have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ω
      (fun point : EffectiveCover period hPeriod => point.time) :=
    contMDiff_snd.comp hTo
  have hFiberInput :
      ContMDiff (𝓘(Real, Real).prod coverModelWithCorners) (𝓡 3) ω
        (fun input : Real × EffectiveCover period hPeriod => input.2.fiber) :=
    hFiber.comp contMDiff_snd
  have hTimeInput :
      ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
        𝓘(Real, Real) ω
        (fun input : Real × EffectiveCover period hPeriod =>
          input.2.time + input.1) :=
    (hTime.comp contMDiff_snd).add contMDiff_fst
  exact hInv.comp (hFiberInput.prodMk hTimeInput)

/-- The complete real action is jointly analytic, not merely analytic at each
fixed time. -/
theorem effectiveJointTimeFlow_contMDiff :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ω
      (effectiveJointTimeFlow period hPeriod) := by
  have hProjection := mappingTorus_projection_isLocalDiffeomorph
    coverModelWithCorners ω (sphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)
  have hLift : ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ω
      (fun input : Real × EffectiveCover period hPeriod =>
        mappingTorusMk (sphereData period hPeriod)
          (coverTimeTranslation (sphereData period hPeriod)
            input.1 input.2)) :=
    hProjection.contMDiff.comp
      (effectiveCoverJointTimeTranslation_contMDiff period hPeriod)
  rintro ⟨shift, quotientPoint⟩
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  have hLocal := hProjection anchor
  have hInput : ContMDiffAt
      (𝓘(Real, Real).prod coverModelWithCorners)
      (𝓘(Real, Real).prod coverModelWithCorners) ω
      (fun input : Real × EffectiveQuotient period hPeriod =>
        (input.1, hLocal.localInverse input.2))
      (shift, mappingTorusMk (sphereData period hPeriod) anchor) :=
    contMDiffAt_fst.prodMk
      (hLocal.localInverse_contMDiffAt.comp
        (shift, mappingTorusMk (sphereData period hPeriod) anchor)
        contMDiffAt_snd)
  have hLocalLift : ContMDiffAt
      (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ω
      ((fun input : Real × EffectiveCover period hPeriod =>
          mappingTorusMk (sphereData period hPeriod)
            (coverTimeTranslation (sphereData period hPeriod)
              input.1 input.2)) ∘
        (fun input : Real × EffectiveQuotient period hPeriod =>
          (input.1, hLocal.localInverse input.2)))
      (shift, mappingTorusMk (sphereData period hPeriod) anchor) :=
    hLift.contMDiffAt.comp _ hInput
  apply hLocalLift.congr_of_eventuallyEq
  have hSnd : Filter.Tendsto
      (fun input : Real × EffectiveQuotient period hPeriod => input.2)
      (𝓝 (shift, mappingTorusMk (sphereData period hPeriod) anchor))
      (𝓝 (mappingTorusMk (sphereData period hPeriod) anchor)) :=
    continuousAt_snd
  have hRight := hLocal.localInverse_eventuallyEq_right.comp_tendsto hSnd
  filter_upwards [hRight] with input hInputRight
  change effectiveTimeFlow period hPeriod input.1 input.2 =
    mappingTorusMk (sphereData period hPeriod)
      (coverTimeTranslation (sphereData period hPeriod)
        input.1 (hLocal.localInverse input.2))
  rw [← effectiveTimeFlow_mk]
  exact congrArg (effectiveTimeFlow period hPeriod input.1) hInputRight.symm

/-- Packaged real action with joint analyticity. -/
structure JointAnalyticRealAction where
  action : CompleteAnalyticRealAction period hPeriod
  joint_analytic :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ω
      (fun input : Real × EffectiveQuotient period hPeriod =>
        action.flow input.1 input.2)

def effectiveJointAnalyticRealAction :
    JointAnalyticRealAction period hPeriod where
  action := effectiveCompleteAnalyticRealAction period hPeriod
  joint_analytic := effectiveJointTimeFlow_contMDiff period hPeriod

theorem joint_analytic_time_action4D_closed :
    Nonempty (JointAnalyticRealAction period hPeriod) :=
  ⟨effectiveJointAnalyticRealAction period hPeriod⟩

end

end P0EFTJanusMappingTorusJointAnalyticTimeAction4D
end JanusFormal
