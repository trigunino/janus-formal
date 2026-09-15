import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D

/-!
# Ambient signed vector-pullback Piola law

This gate lifts the existing three-dimensional throat Piola argument to the
four-dimensional ambient current carrier.  Exterior differentiation of the
pulled-back flux three-form gives the signed Jacobian times coordinate
divergence.  For Gate 1049's local collar transition, its chosen inverse has
inverse Jacobian throughout the same germ, so a differentiable ambient current
obeys the pointwise four-dimensional signed Piola law.

This is a coordinate-volume statement at one face point.  It does not identify
the physical metric volume, provide an atlas-wide transition family, or prove
an integrated Stokes law.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Module Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06WarpedNullAffineFluxFiberStokes4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D

/-- The ambient flux differential evaluated on the fixed basis is coordinate
divergence. -/
theorem programPT06AmbientFluxThreeForm_extDeriv_apply_basis
    {current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hCurrent : DifferentiableAt Real current coordinate) :
    extDeriv (programPT06AmbientFluxThreeForm current) coordinate
        programPT06AmbientCoordinateBasis =
      programPT06AmbientCoordinateDivergence current coordinate := by
  have hForm := congrArg
    (fun form : ProgramPT06AmbientCoordinate4 [⋀^Fin 4]→L[Real] Real =>
      form programPT06AmbientCoordinateBasis)
    (programPT06AmbientFluxThreeForm_extDeriv hCurrent)
  simpa only [ContinuousAlternatingMap.smul_apply,
    programPT06AmbientSignedVolume_apply_basis, smul_eq_mul, mul_one] using
    hForm

/-- Evaluation form of the determinant law for ambient top forms. -/
theorem programPT06AmbientSignedTopForm_comp_apply_basis
    (form : ProgramPT06AmbientCoordinate4 [⋀^Fin 4]→L[Real] Real)
    (linear : ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4) :
    (form.compContinuousLinearMap linear) programPT06AmbientCoordinateBasis =
      LinearMap.det linear.toLinearMap *
        form programPT06AmbientCoordinateBasis := by
  rw [programPT06AmbientSignedTopForm_comp]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- Exterior-form Piola naturality in the four-dimensional ambient carrier. -/
theorem programPT06AmbientThreeFormPullback_extDeriv_eq_det_mul_divergence
    {forward current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hCurrent : DifferentiableAt Real current (forward coordinate))
    (hForward : ContDiffAt Real 2 forward coordinate) :
    extDeriv
        (programPT06ThreeFormPullback forward
          (programPT06AmbientFluxThreeForm current)) coordinate
        programPT06AmbientCoordinateBasis =
      LinearMap.det (fderiv Real forward coordinate).toLinearMap *
        programPT06AmbientCoordinateDivergence current
          (forward coordinate) := by
  have hFlux : DifferentiableAt Real
      (programPT06AmbientFluxThreeForm current) (forward coordinate) :=
    programPT06AmbientSignedVolume.curryLeft.differentiableAt.comp
      (forward coordinate) hCurrent
  unfold programPT06ThreeFormPullback
  rw [extDeriv_pullback hFlux hForward (by simp)]
  rw [programPT06AmbientSignedTopForm_comp_apply_basis]
  rw [programPT06AmbientFluxThreeForm_extDeriv_apply_basis hCurrent]

/-- An inverse-Jacobian germ identifies the signed vector-density and
differential-form flux pullbacks throughout that germ. -/
theorem programPT06AmbientSignedVectorPullback_fluxThreeForm_eventuallyEq
    {forward reverse current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hInverse : ∀ᶠ nearby in 𝓝 coordinate,
      (fderiv Real reverse (forward nearby)).comp
          (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4) :
    programPT06AmbientFluxThreeForm
        (programPT06AmbientSignedVectorPullback forward reverse current) =ᶠ[
      𝓝 coordinate]
      programPT06ThreeFormPullback forward
        (programPT06AmbientFluxThreeForm current) :=
  hInverse.mono fun _ hNearby =>
    programPT06AmbientSignedVectorPullback_fluxThreeForm_eq_at hNearby

/-- Local four-dimensional signed Piola identity for coordinate divergence. -/
theorem programPT06AmbientSignedVectorPullback_divergence_eq_det_mul
    {forward reverse current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hInverse : ∀ᶠ nearby in 𝓝 coordinate,
      (fderiv Real reverse (forward nearby)).comp
          (fderiv Real forward nearby) =
        ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4)
    (hVectorPullback : DifferentiableAt Real
      (programPT06AmbientSignedVectorPullback forward reverse current)
      coordinate)
    (hCurrent : DifferentiableAt Real current (forward coordinate))
    (hForward : ContDiffAt Real 2 forward coordinate) :
    programPT06AmbientCoordinateDivergence
        (programPT06AmbientSignedVectorPullback forward reverse current)
        coordinate =
      LinearMap.det (fderiv Real forward coordinate).toLinearMap *
        programPT06AmbientCoordinateDivergence current
          (forward coordinate) := by
  have hForms :=
    programPT06AmbientSignedVectorPullback_fluxThreeForm_eventuallyEq
      (current := current) hInverse
  calc
    _ = extDeriv
        (programPT06AmbientFluxThreeForm
          (programPT06AmbientSignedVectorPullback forward reverse current))
        coordinate programPT06AmbientCoordinateBasis :=
      (programPT06AmbientFluxThreeForm_extDeriv_apply_basis
        hVectorPullback).symm
    _ = extDeriv
        (programPT06ThreeFormPullback forward
          (programPT06AmbientFluxThreeForm current)) coordinate
        programPT06AmbientCoordinateBasis := by
      rw [hForms.extDeriv_eq]
    _ = _ :=
      programPT06AmbientThreeFormPullback_extDeriv_eq_det_mul_divergence
        hCurrent hForward

private def programPT06AmbientEndomorphismMatrixEntryContinuousLinearMap
    (row column : Fin 4) :
    (ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4) →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun operator ↦
        LinearMap.toMatrix programPT06AmbientCoordinateBasis
          programPT06AmbientCoordinateBasis operator.toLinearMap row column
      map_add' := by
        intro first second
        simp
      map_smul' := by
        intro scalar operator
        simp }

private theorem programPT06AmbientEndomorphismMatrixEntry_contDiff
    (row column : Fin 4) :
    ContDiff Real ∞
      (fun operator : ProgramPT06AmbientCoordinate4 →L[Real]
          ProgramPT06AmbientCoordinate4 ↦
        LinearMap.toMatrix programPT06AmbientCoordinateBasis
          programPT06AmbientCoordinateBasis operator.toLinearMap row column) := by
  change ContDiff Real ∞
    (programPT06AmbientEndomorphismMatrixEntryContinuousLinearMap row column)
  exact
    (programPT06AmbientEndomorphismMatrixEntryContinuousLinearMap
      row column).contDiff

/-- Determinant is smooth on ambient four-dimensional endomorphisms. -/
theorem programPT06AmbientEndomorphismDeterminant_contDiff :
    ContDiff Real ∞
      (fun operator : ProgramPT06AmbientCoordinate4 →L[Real]
          ProgramPT06AmbientCoordinate4 ↦
        LinearMap.det operator.toLinearMap) := by
  rw [show
    (fun operator : ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4 ↦ LinearMap.det operator.toLinearMap) =
      fun operator ↦ Matrix.det
        (LinearMap.toMatrix programPT06AmbientCoordinateBasis
          programPT06AmbientCoordinateBasis operator.toLinearMap) by
    funext operator
    exact (LinearMap.det_toMatrix programPT06AmbientCoordinateBasis
      operator.toLinearMap).symm]
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact programPT06AmbientEndomorphismMatrixEntry_contDiff
    (permutation index) index

variable (period : Real) (hPeriod : period ≠ 0)

/-- The forward and chosen inverse Jacobians are inverse throughout the local
collar-transition germ. -/
theorem programPT06WarpedNullCollarTransitionJacobian_inverse_eventually
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ∀ᶠ nearby in 𝓝 (programPT06WarpedNullHyperplaneEmbedding source),
      (fderiv Real
          (programPT06WarpedNullCollarInverseTransition period hPeriod datum)
          (datum.transition nearby)).comp
        (fderiv Real datum.transition nearby) =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4 := by
  let forward := datum.transition
  let reverse :=
    programPT06WarpedNullCollarInverseTransition period hPeriod datum
  let coordinate := programPT06WarpedNullHyperplaneEmbedding source
  have hForward : ContDiffAt Real 2 forward coordinate :=
    (datum.transition_isLocalDiffeomorphAt.contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hReverse : ContDiffAt Real 2 reverse (forward coordinate) :=
    (datum.transition_isLocalDiffeomorphAt.localInverse_contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hReverseEventually : ∀ᶠ nearby in 𝓝 coordinate,
      ContDiffAt Real 2 reverse (forward nearby) :=
    hForward.continuousAt.eventually (hReverse.eventually (by norm_num))
  have hCompositeDerivative :=
    (programPT06WarpedNullCollarInverseTransition_eventuallyEq_left
      period hPeriod datum).fderiv (𝕜 := Real)
  filter_upwards [hForward.eventually (by norm_num), hReverseEventually,
    hCompositeDerivative] with nearby hForwardNearby hReverseNearby hDerivative
  have hComposition := fderiv_comp (𝕜 := Real) (x := nearby)
    (f := forward) (g := reverse)
    (hReverseNearby.differentiableAt (by norm_num))
    (hForwardNearby.differentiableAt (by norm_num))
  calc
    _ = fderiv Real (reverse ∘ forward) nearby := hComposition.symm
    _ = fderiv Real id nearby := hDerivative
    _ = _ := fderiv_id

/-- Gate 1049's signed pulled-back current is differentiable whenever the
target current is differentiable at the fixed face point. -/
theorem programPT06WarpedNullCollarTransitionSignedPullbackCurrent_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    DifferentiableAt Real
      (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
        period hPeriod datum current)
      (programPT06WarpedNullHyperplaneEmbedding source) := by
  let forward := datum.transition
  let reverse :=
    programPT06WarpedNullCollarInverseTransition period hPeriod datum
  let coordinate := programPT06WarpedNullHyperplaneEmbedding source
  have hForward : ContDiffAt Real 2 forward coordinate :=
    (datum.transition_isLocalDiffeomorphAt.contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hForwardJacobian : ContDiffAt Real 1
      (fderiv Real forward) coordinate :=
    hForward.fderiv_right (m := 1) (by norm_num)
  have hDeterminant : DifferentiableAt Real
      (fun nearby => LinearMap.det
        (fderiv Real forward nearby).toLinearMap) coordinate :=
    ((programPT06AmbientEndomorphismDeterminant_contDiff.contDiffAt.of_le
      (by norm_num)).comp coordinate hForwardJacobian).differentiableAt
      (by norm_num)
  have hCurrentAtForward : DifferentiableAt Real current
      (forward coordinate) := by
    dsimp only [forward, coordinate]
    rw [datum.transition_face period hPeriod]
    exact hCurrent
  have hCurrentAlongForward : DifferentiableAt Real
      (fun nearby => current (forward nearby)) coordinate :=
    hCurrentAtForward.comp coordinate
      (hForward.differentiableAt (by norm_num))
  have hReverse : ContDiffAt Real 2 reverse (forward coordinate) :=
    (datum.transition_isLocalDiffeomorphAt.localInverse_contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hReverseJacobian : DifferentiableAt Real
      (fderiv Real reverse) (forward coordinate) :=
    (hReverse.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hReverseJacobianAlongForward : DifferentiableAt Real
      (fun nearby => fderiv Real reverse (forward nearby)) coordinate :=
    hReverseJacobian.comp coordinate
      (hForward.differentiableAt (by norm_num))
  have hReverseApplied : DifferentiableAt Real
      (fun nearby =>
        fderiv Real reverse (forward nearby) (current (forward nearby)))
      coordinate :=
    hReverseJacobianAlongForward.clm_apply hCurrentAlongForward
  unfold programPT06WarpedNullCollarTransitionSignedPullbackCurrent
    programPT06AmbientSignedVectorPullback
  exact hDeterminant.smul hReverseApplied

/-- Signed determinant of the collar-transition Jacobian. -/
def programPT06WarpedNullCollarTransitionSignedJacobian
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) : Real :=
  LinearMap.det
    ((programPT06WarpedNullCollarTransitionJacobian period hPeriod datum :
      ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4).toLinearMap)

theorem programPT06WarpedNullCollarTransitionSignedJacobian_eq_fderiv
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarTransitionSignedJacobian period hPeriod datum =
      LinearMap.det
        (fderiv Real datum.transition
          (programPT06WarpedNullHyperplaneEmbedding source)).toLinearMap := by
  have hJacobian := programPT06WarpedNullCollarTransitionJacobian_coe
    period hPeriod datum
  rw [mfderiv_eq_fderiv] at hJacobian
  exact congrArg
    (fun linear : ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4 => LinearMap.det linear.toLinearMap)
    hJacobian

/-- The absolute value of the signed Jacobian is Gate 1048's positive
Jacobian density. -/
theorem programPT06WarpedNullCollarTransitionSignedJacobian_abs
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    |programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum| =
      programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum := by
  rfl

/-- Point-local four-dimensional signed Piola law for the warped-null collar
transition. -/
theorem programPT06WarpedNullCollarTransition_divergence_eq_signedJacobian_mul
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum *
        programPT06AmbientCoordinateDivergence current
          (programPT06WarpedNullHyperplaneEmbedding source) := by
  have hCurrentAtForward : DifferentiableAt Real current
      (datum.transition
        (programPT06WarpedNullHyperplaneEmbedding source)) := by
    rw [datum.transition_face period hPeriod]
    exact hCurrent
  have hForward : ContDiffAt Real 2 datum.transition
      (programPT06WarpedNullHyperplaneEmbedding source) :=
    (datum.transition_isLocalDiffeomorphAt.contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hPiola := programPT06AmbientSignedVectorPullback_divergence_eq_det_mul
    (forward := datum.transition)
    (reverse := programPT06WarpedNullCollarInverseTransition
      period hPeriod datum)
    (current := current)
    (coordinate := programPT06WarpedNullHyperplaneEmbedding source)
    (programPT06WarpedNullCollarTransitionJacobian_inverse_eventually
      period hPeriod datum)
    (programPT06WarpedNullCollarTransitionSignedPullbackCurrent_differentiableAt
      period hPeriod datum current hCurrent)
    hCurrentAtForward hForward
  rw [datum.transition_face period hPeriod] at hPiola
  rw [programPT06WarpedNullCollarTransitionSignedJacobian_eq_fderiv
    period hPeriod datum]
  exact hPiola

/-- Gate bundle: signed four-dimensional divergence covariance and the
already established face-flux covariance. -/
theorem programPT06WarpedNullCollarPiolaDivergence_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06WarpedNullCollarTransitionSignedJacobian
            period hPeriod datum *
          programPT06AmbientCoordinateDivergence current
            (programPT06WarpedNullHyperplaneEmbedding source) ∧
      programPT06WarpedNullHyperplaneFluxRestriction
          (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
            period hPeriod datum current) source =
        programPT06WarpedNullHyperplaneFluxRestriction current source :=
  ⟨programPT06WarpedNullCollarTransition_divergence_eq_signedJacobian_mul
      period hPeriod datum current hCurrent,
    programPT06WarpedNullCollarTransition_fluxRestriction_eq
      period hPeriod datum current⟩

/-- The affine collar current therefore transforms its prescribed divergence
by the signed Jacobian. -/
theorem programPT06WarpedNullCollarTransition_affineDivergence
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : DifferentiableAt Real density source) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum
          (programPT06WarpedNullCollarAffineFluxExtension density))
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum * density source := by
  have hAffine : DifferentiableAt Real
      (programPT06WarpedNullCollarAffineFluxExtension density)
      (programPT06WarpedNullHyperplaneEmbedding source) := by
    rw [← programPT06WarpedNullCollar_zeroSlice source]
    exact (programPT06WarpedNullCollarAffineFluxExtension_hasFDerivAt
      (coordinate := (source, 0)) hDensity).differentiableAt
  calc
    _ = programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum *
        programPT06AmbientCoordinateDivergence
          (programPT06WarpedNullCollarAffineFluxExtension density)
          (programPT06WarpedNullHyperplaneEmbedding source) :=
      programPT06WarpedNullCollarTransition_divergence_eq_signedJacobian_mul
        period hPeriod datum _ hAffine
    _ = _ := by
      rw [← programPT06WarpedNullCollar_zeroSlice source,
        programPT06WarpedNullCollarAffineFluxExtension_divergence
          (radius := 0) hDensity]

/-- The same transformed affine current retains the prescribed face flux. -/
theorem programPT06WarpedNullCollarTransition_affineFlux
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (density : ProgramPT06WarpedNullHyperplaneDensity) :
    programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum
          (programPT06WarpedNullCollarAffineFluxExtension density)) source =
      density source := by
  rw [programPT06WarpedNullCollarTransition_fluxRestriction_eq
    period hPeriod datum]
  exact congrFun
    (programPT06WarpedNullCollarAffineFluxExtension_rightInverse density)
    source

/-- Affine gate bundle: transformed coordinate divergence and face flux are
controlled by the same prescribed density. -/
theorem programPT06WarpedNullCollarAffinePiolaDivergence_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (density : ProgramPT06WarpedNullHyperplaneDensity)
    (hDensity : DifferentiableAt Real density source) :
    programPT06AmbientCoordinateDivergence
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum
          (programPT06WarpedNullCollarAffineFluxExtension density))
        (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum * density source ∧
      programPT06WarpedNullHyperplaneFluxRestriction
          (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
            period hPeriod datum
            (programPT06WarpedNullCollarAffineFluxExtension density)) source =
        density source :=
  ⟨programPT06WarpedNullCollarTransition_affineDivergence
      period hPeriod datum density hDensity,
    programPT06WarpedNullCollarTransition_affineFlux
      period hPeriod datum density⟩

end
end P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D
end JanusFormal
