import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Full top-form determinant law on the three-dimensional throat space. -/
theorem programPT06ThroatSignedTopForm_comp
    (form : ThroatCoverCoordinates [⋀^Fin 3]→L[Real] Real)
    (linear : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) :
    form.compContinuousLinearMap linear =
      LinearMap.det linear.toLinearMap • form := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [(form.compContinuousLinearMap linear).toAlternatingMap
    |>.eq_smul_basis_det programPT06ThroatSpatialBasis]
  rw [(LinearMap.det linear.toLinearMap • form).toAlternatingMap
    |>.eq_smul_basis_det programPT06ThroatSpatialBasis]
  have hEvaluation :
      (form.compContinuousLinearMap linear).toAlternatingMap
          programPT06ThroatSpatialBasis =
        LinearMap.det linear.toLinearMap *
          form programPT06ThroatSpatialBasis := by
    change (form.compContinuousLinearMap linear) programPT06ThroatSpatialBasis = _
    exact programPT06ThroatSignedTopForm_comp_apply_basis form linear
  rw [hEvaluation]
  rfl

private theorem programPT06ThroatLinear_rightInverse_of_leftInverse
    (forward reverse :
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates)
    (hLeft : reverse.comp forward =
      ContinuousLinearMap.id Real ThroatCoverCoordinates) :
    forward.comp reverse =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
  have hLeftPointwise : Function.LeftInverse reverse forward := by
    intro vector
    have hApplied := congrArg (fun operator => operator vector) hLeft
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hForwardSurjective : Function.Surjective forward :=
    LinearMap.surjective_of_injective hLeftPointwise.injective
  have hRightPointwise : Function.RightInverse reverse forward :=
    hLeftPointwise.rightInverse_of_surjective hForwardSurjective
  apply ContinuousLinearMap.ext
  intro vector
  exact hRightPointwise vector

/-- Pulling back the flux of a vector through inverse linear maps equals the
flux of its signed vector-density pullback. -/
theorem programPT06ThroatSignedFlux_comp
    (forward reverse :
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates)
    (vector : ThroatCoverCoordinates)
    (hLeft : reverse.comp forward =
      ContinuousLinearMap.id Real ThroatCoverCoordinates) :
    (programPT06ThroatSignedVolume.curryLeft vector).compContinuousLinearMap
        forward =
      programPT06ThroatSignedVolume.curryLeft
        (LinearMap.det forward.toLinearMap • reverse vector) := by
  have hRight :=
    programPT06ThroatLinear_rightInverse_of_leftInverse forward reverse hLeft
  have hRightApply : forward (reverse vector) = vector := by
    have hApplied := congrArg (fun operator => operator vector) hRight
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  calc
    _ = (programPT06ThroatSignedVolume.curryLeft
        (forward (reverse vector))).compContinuousLinearMap forward := by
      rw [hRightApply]
    _ = (programPT06ThroatSignedVolume.compContinuousLinearMap forward).curryLeft
        (reverse vector) := by
      symm
      exact ContinuousAlternatingMap.curryLeft_compContinuousLinearMap
        programPT06ThroatSignedVolume forward (reverse vector)
    _ = (LinearMap.det forward.toLinearMap •
        programPT06ThroatSignedVolume).curryLeft (reverse vector) := by
      rw [programPT06ThroatSignedTopForm_comp]
    _ = _ := by
      simp

/-- Signed vector-density pullback built from the forward Jacobian and the
reverse Jacobian at the corresponding target point. -/
def programPT06ThroatSignedVectorPullback
    (forward reverse field :
      ThroatCoverCoordinates → ThroatCoverCoordinates) :
    ThroatCoverCoordinates → ThroatCoverCoordinates :=
  fun coordinate =>
    LinearMap.det (fderiv Real forward coordinate).toLinearMap •
      fderiv Real reverse (forward coordinate) (field (forward coordinate))

/-- At a point where the two Jacobians are inverse, vector pullback and
differential-form pullback give the same flux two-form. -/
theorem programPT06ThroatSignedVectorPullback_fluxForm_eq_at
    {forward reverse field :
      ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hInverse :
      (fderiv Real reverse (forward coordinate)).comp
          (fderiv Real forward coordinate) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates) :
    programPT06ThroatSignedFluxForm
        (programPT06ThroatSignedVectorPullback forward reverse field) coordinate =
      programPT06ThroatSignedFluxPullback forward field coordinate := by
  unfold programPT06ThroatSignedFluxForm
    programPT06ThroatSignedVectorPullback
    programPT06ThroatSignedFluxPullback
  exact (programPT06ThroatSignedFlux_comp
    (fderiv Real forward coordinate)
    (fderiv Real reverse (forward coordinate))
    (field (forward coordinate)) hInverse).symm

/-- A local inverse-Jacobian law gives equality of vector and form pullbacks
throughout the same germ. -/
theorem programPT06ThroatSignedVectorPullback_fluxForm_eventuallyEq
    {forward reverse field :
      ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hInverse : ∀ᶠ nearby in nhds coordinate,
      (fderiv Real reverse (forward nearby)).comp
          (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates) :
    programPT06ThroatSignedFluxForm
        (programPT06ThroatSignedVectorPullback forward reverse field) =ᶠ[nhds coordinate]
      programPT06ThroatSignedFluxPullback forward field :=
  hInverse.mono fun _ hNearby =>
    programPT06ThroatSignedVectorPullback_fluxForm_eq_at hNearby

/-- Local signed Piola identity for the coordinate divergence. -/
theorem programPT06ThroatSignedVectorPullback_divergence_eq_det_mul
    {forward reverse field :
      ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hInverse : ∀ᶠ nearby in nhds coordinate,
      (fderiv Real reverse (forward nearby)).comp
          (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates)
    (hVectorPullback : DifferentiableAt Real
      (programPT06ThroatSignedVectorPullback forward reverse field) coordinate)
    (hField : DifferentiableAt Real field (forward coordinate))
    (hForward : ContDiffAt Real 2 forward coordinate) :
    programPT06ThroatCoordinateDivergence
        (programPT06ThroatSignedVectorPullback forward reverse field) coordinate =
      LinearMap.det (fderiv Real forward coordinate).toLinearMap *
        programPT06ThroatCoordinateDivergence field (forward coordinate) := by
  have hForms := programPT06ThroatSignedVectorPullback_fluxForm_eventuallyEq
    (field := field) hInverse
  calc
    _ = extDeriv (programPT06ThroatSignedFluxForm
          (programPT06ThroatSignedVectorPullback forward reverse field)) coordinate
        programPT06ThroatSpatialBasis :=
      (programPT06ThroatSignedFluxForm_extDeriv_apply_basis hVectorPullback).symm
    _ = extDeriv (programPT06ThroatSignedFluxPullback forward field) coordinate
        programPT06ThroatSpatialBasis := by
      rw [hForms.extDeriv_eq]
    _ = _ := programPT06ThroatSignedFluxPullback_extDeriv_eq_det_mul_divergence
      hField hForward

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (Base period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (Base period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The forward and reverse transition Jacobians are inverse throughout a
neighborhood of every genuine overlap point. -/
theorem programPT06ActualThroatTransitionJacobian_inverse_eventually
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ∀ᶠ nearby in nhds
        (extChartAt throatCoverModelWithCorners firstCenter current),
      (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter nearby)).comp
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          nearby) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
  let forward :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let reverse :=
    throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter
  let coordinate := extChartAt throatCoverModelWithCorners firstCenter current
  have hForward : ContDiffAt Real 2 forward coordinate :=
    throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      firstCenter secondCenter current hFirst hSecond
  have hReverse : ContDiffAt Real 2 reverse (forward coordinate) := by
    dsimp only [forward, reverse, coordinate]
    rw [throatGaugeBaseChartTransition_apply_current period hPeriod
      firstCenter secondCenter current hFirst]
    exact throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      secondCenter firstCenter current hSecond hFirst
  have hReverseEventually : ∀ᶠ nearby in nhds coordinate,
      ContDiffAt Real 2 reverse (forward nearby) :=
    hForward.continuousAt.eventually (hReverse.eventually (by norm_num))
  have hCompositeDerivative :=
    (throatGaugeBaseChartTransition_inverse_comp_eventuallyEq period hPeriod
      firstCenter secondCenter current hFirst hSecond).fderiv (𝕜 := Real)
  filter_upwards [hForward.eventually (by norm_num), hReverseEventually,
    hCompositeDerivative] with nearby hForwardNearby hReverseNearby hDerivative
  have hComposition := fderiv_comp (𝕜 := Real) (x := nearby)
    (f := forward) (g := reverse)
    (hReverseNearby.differentiableAt (by norm_num))
    (hForwardNearby.differentiableAt (by norm_num))
  calc
    _ = fderiv Real (reverse ∘ forward) nearby := hComposition.symm
    _ = fderiv Real id nearby := hDerivative
    _ = _ := by simp

/-- Vector and form pullbacks agree as germs at a genuine overlap. -/
theorem programPT06ActualThroatSignedVectorPullback_fluxForm_eventuallyEq
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates) :
    programPT06ThroatSignedFluxForm
        (programPT06ThroatSignedVectorPullback
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
          field) =ᶠ[nhds (extChartAt throatCoverModelWithCorners firstCenter current)]
      programPT06ThroatSignedFluxPullback
        (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
        field :=
  programPT06ThroatSignedVectorPullback_fluxForm_eventuallyEq
    (field := field)
    (programPT06ActualThroatTransitionJacobian_inverse_eventually
      period hPeriod firstCenter secondCenter current hFirst hSecond)

/-- The signed vector pullback is differentiable at every genuine overlap
whenever the target vector field is differentiable there. -/
theorem programPT06ActualThroatSignedVectorPullback_differentiableAt
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (hField : DifferentiableAt Real field
      (extChartAt throatCoverModelWithCorners secondCenter current)) :
    DifferentiableAt Real
      (programPT06ThroatSignedVectorPullback
        (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
        (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
        field)
      (extChartAt throatCoverModelWithCorners firstCenter current) := by
  let forward :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let reverse :=
    throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter
  let coordinate := extChartAt throatCoverModelWithCorners firstCenter current
  have hForward : ContDiffAt Real ∞ forward coordinate :=
    throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond
  have hJacobian : ContDiffAt Real ∞ (fderiv Real forward) coordinate :=
    throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond
  have hDeterminant : DifferentiableAt Real
      (fun nearby => LinearMap.det (fderiv Real forward nearby).toLinearMap)
      coordinate :=
    (programPT06ThroatEndomorphismDeterminant_contDiff.contDiffAt.comp
      coordinate hJacobian).differentiableAt (by simp)
  have hFieldAtForward : DifferentiableAt Real field (forward coordinate) := by
    dsimp only [forward, coordinate]
    rw [throatGaugeBaseChartTransition_apply_current period hPeriod
      firstCenter secondCenter current hFirst]
    exact hField
  have hFieldAlongForward : DifferentiableAt Real
      (fun nearby => field (forward nearby)) coordinate :=
    hFieldAtForward.comp coordinate
      (hForward.differentiableAt (by simp))
  have hReverseJacobian : DifferentiableAt Real
      (fun nearby => fderiv Real reverse (forward nearby)) coordinate := by
    change DifferentiableAt Real
      (programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
        firstCenter secondCenter) coordinate
    exact
      (programPT06ActualThroatBaseInverseJacobianInCoordinates_contDiffAt
        period hPeriod firstCenter secondCenter current hFirst hSecond
        |>.differentiableAt (by simp))
  have hReverseApplied : DifferentiableAt Real
      (fun nearby =>
        fderiv Real reverse (forward nearby) (field (forward nearby))) coordinate :=
    hReverseJacobian.clm_apply hFieldAlongForward
  unfold programPT06ThroatSignedVectorPullback
  exact hDeterminant.smul hReverseApplied

/-- The signed vector pullback and the exterior-form pullback agree at every
genuine throat base-chart overlap point. -/
theorem programPT06ActualThroatSignedVectorPullback_fluxForm_eq_at
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates) :
    programPT06ThroatSignedFluxForm
        (programPT06ThroatSignedVectorPullback
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
          field)
        (extChartAt throatCoverModelWithCorners firstCenter current) =
      programPT06ThroatSignedFluxPullback
        (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
        field (extChartAt throatCoverModelWithCorners firstCenter current) := by
  apply programPT06ThroatSignedVectorPullback_fluxForm_eq_at
  rw [throatGaugeBaseChartTransition_apply_current period hPeriod
    firstCenter secondCenter current hFirst]
  simpa only [
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_inverse
      period hPeriod firstCenter secondCenter current hFirst hSecond

/-- Signed Piola transformation of coordinate divergence at a genuine
overlap point. -/
theorem programPT06ActualThroatSignedVectorPullback_divergence_eq_det_mul
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (hField : DifferentiableAt Real field
      (extChartAt throatCoverModelWithCorners secondCenter current)) :
    programPT06ThroatCoordinateDivergence
        (programPT06ThroatSignedVectorPullback
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
          field)
        (extChartAt throatCoverModelWithCorners firstCenter current) =
      LinearMap.det
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)).toLinearMap *
        programPT06ThroatCoordinateDivergence field
          (extChartAt throatCoverModelWithCorners secondCenter current) := by
  have hForwardValue := throatGaugeBaseChartTransition_apply_current period hPeriod
    firstCenter secondCenter current hFirst
  have hVectorPullback :=
    programPT06ActualThroatSignedVectorPullback_differentiableAt
      period hPeriod firstCenter secondCenter current hFirst hSecond field hField
  have hFieldAtForward : DifferentiableAt Real field
      (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
        (extChartAt throatCoverModelWithCorners firstCenter current)) := by
    rw [hForwardValue]
    exact hField
  rw [← hForwardValue] at ⊢
  apply programPT06ThroatSignedVectorPullback_divergence_eq_det_mul
  · exact programPT06ActualThroatTransitionJacobian_inverse_eventually
      period hPeriod firstCenter secondCenter current hFirst hSecond
  · exact hVectorPullback
  · exact hFieldAtForward
  · exact throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      firstCenter secondCenter current hFirst hSecond

end
end P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D
end JanusFormal
