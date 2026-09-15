import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D

/-!
# Warped-null collar transition flux covariance

Gate 1048 supplies a point-local ambient chart transition at the identified
warped-null face.  This gate exposes its chosen local inverse and inverse
Jacobian, then applies the signed ambient vector-density pullback law to the
true cut-collar face germ.  The pulled-back current has exactly the same
coordinate flux as the original current at the selected face point.

The result is point-local and uses the fixed signed coordinate volume.  It
does not assert metric-volume covariance, a four-dimensional Piola-divergence
law, or an integrated Stokes theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open Topology
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The local inverse chosen from the point-local chart transition datum. -/
def programPT06WarpedNullCollarInverseTransition
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 → ProgramPT06AmbientCoordinate4 :=
  datum.transition_isLocalDiffeomorphAt.localInverse

/-- The chosen inverse sends the fixed face point back to itself. -/
theorem programPT06WarpedNullCollarInverseTransition_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarInverseTransition period hPeriod datum
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  calc
    programPT06WarpedNullCollarInverseTransition period hPeriod datum
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarInverseTransition period hPeriod datum
        (datum.transition
          (programPT06WarpedNullHyperplaneEmbedding source)) := by
        rw [datum.transition_face period hPeriod]
    _ = programPT06WarpedNullHyperplaneEmbedding source := by
      exact datum.transition_isLocalDiffeomorphAt.localInverse_left_inv
        datum.transition_isLocalDiffeomorphAt.localInverse_mem_target

/-- Left inverse identity as a germ at the selected warped face point. -/
theorem programPT06WarpedNullCollarInverseTransition_eventuallyEq_left
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarInverseTransition period hPeriod datum ∘
        datum.transition =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)] id := by
  exact datum.transition_isLocalDiffeomorphAt.localInverse_eventuallyEq_left

/-- Right inverse identity as a germ at the same fixed face point. -/
theorem programPT06WarpedNullCollarInverseTransition_eventuallyEq_right
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    datum.transition ∘
        programPT06WarpedNullCollarInverseTransition period hPeriod datum =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)] id := by
  have hRight :=
    datum.transition_isLocalDiffeomorphAt.localInverse_eventuallyEq_right
  rw [datum.transition_face period hPeriod] at hRight
  exact hRight

/-- The inverse and forward Jacobians compose to the identity. -/
theorem programPT06WarpedNullCollarInverseTransition_fderiv_comp
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    (fderiv Real
        (programPT06WarpedNullCollarInverseTransition period hPeriod datum)
        (datum.transition
          (programPT06WarpedNullHyperplaneEmbedding source))).comp
      (fderiv Real datum.transition
        (programPT06WarpedNullHyperplaneEmbedding source)) =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4 := by
  have hForward : DifferentiableAt Real datum.transition
      (programPT06WarpedNullHyperplaneEmbedding source) :=
    (datum.transition_isLocalDiffeomorphAt.mdifferentiableAt
      (by norm_num)).differentiableAt
  have hInverse : DifferentiableAt Real
      (programPT06WarpedNullCollarInverseTransition period hPeriod datum)
      (datum.transition
        (programPT06WarpedNullHyperplaneEmbedding source)) :=
    (datum.transition_isLocalDiffeomorphAt.localInverse_mdifferentiableAt
      (by norm_num)).differentiableAt
  calc
    _ = fderiv Real
        (programPT06WarpedNullCollarInverseTransition period hPeriod datum ∘
          datum.transition)
        (programPT06WarpedNullHyperplaneEmbedding source) :=
      (fderiv_comp _ hInverse hForward).symm
    _ = fderiv Real id
        (programPT06WarpedNullHyperplaneEmbedding source) :=
      (programPT06WarpedNullCollarInverseTransition_eventuallyEq_left
        period hPeriod datum).fderiv_eq
    _ = _ := fderiv_id

/-- Inverse Jacobian of the collar transition at the selected face point. -/
def programPT06WarpedNullCollarInverseTransitionJacobian
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 ≃L[Real] ProgramPT06AmbientCoordinate4 :=
  (programPT06WarpedNullCollarTransitionJacobian
    period hPeriod datum).symm

/-- The inverse Jacobian pulls the true cut-collar normal back to `e₃`. -/
theorem programPT06WarpedNullCollarInverseJacobian_trueCutBulkChartUnitNormal
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarInverseTransitionJacobian period hPeriod datum
        (programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
          (programPT06LocalC3NullCollarMap period hPeriod incidence
            (programPT06WarpedNullZeroFace source))) =
      programPT06AmbientCoordinateBasis 3 := by
  rw [datum.trueCutBulkChartUnitNormal period hPeriod]
  exact (programPT06WarpedNullCollarTransitionJacobian
    period hPeriod datum).symm_apply_apply _

/-- On the face, the transition followed by the warped embedding agrees as a
germ with the genuine cut-collar face coordinate. -/
theorem programPT06WarpedNullCollarTransition_faceCoordinate_eventuallyEq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    datum.transition ∘ programPT06WarpedNullHyperplaneEmbedding =ᶠ[𝓝 source]
      programPT06LocalC3NullFaceCoordinate period hPeriod incidence := by
  have hZero : Filter.Tendsto programPT06WarpedNullZeroFace
      (𝓝 source) (𝓝 (programPT06WarpedNullZeroFace source)) :=
    (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [datum.collar_eventuallyEq.comp_tendsto hZero] with
    current hCurrent
  change datum.transition
      (programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullZeroFace current)) =
    programPT06LocalC3NullFaceCoordinate period hPeriod incidence current at hCurrent
  simpa only [Function.comp_apply,
    programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace] using hCurrent

/-- The incidence identity makes the transition restrict to the identity as a
germ of the warped null face. -/
theorem programPT06WarpedNullCollarTransition_warpedFace_eventuallyEq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    datum.transition ∘ programPT06WarpedNullHyperplaneEmbedding =ᶠ[𝓝 source]
      programPT06WarpedNullHyperplaneEmbedding := by
  refine (programPT06WarpedNullCollarTransition_faceCoordinate_eventuallyEq
    period hPeriod datum).trans ?_
  filter_upwards [incidence.sourceDomain_isOpen.mem_nhds hSource] with
    current hCurrent
  simpa [programPT06ExplicitWarpedNullHyperplaneGeometry] using
    programPT06LocalC3NullFaceCoordinate_eq
      period hPeriod incidence current hCurrent

/-- Signed vector-density pullback through the collar transition. -/
def programPT06WarpedNullCollarTransitionSignedPullbackCurrent
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) : ProgramPT06AmbientCurrent4D :=
  programPT06AmbientSignedVectorPullback datum.transition
    (programPT06WarpedNullCollarInverseTransition period hPeriod datum) current

/-- Pointwise signed flux covariance from the true cut-collar face coordinate
to the explicit warped face. -/
theorem programPT06WarpedNullCollarTransition_flux_covariance_trueFace
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06NullFaceFluxPullback programPT06WarpedNullHyperplaneEmbedding
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current) source =
      programPT06NullFaceFluxPullback
        (programPT06LocalC3NullFaceCoordinate period hPeriod incidence)
        current source := by
  calc
    _ = programPT06NullFaceFluxPullback
        (datum.transition ∘ programPT06WarpedNullHyperplaneEmbedding)
        current source := by
      simpa only [
        programPT06WarpedNullCollarTransitionSignedPullbackCurrent,
        programPT06ExplicitWarpedNullHyperplaneGeometry] using
        programPT06FiniteNullFaceSignedVectorPullback_flux_covariance
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          input incidence.input_mem_domain () datum.transition
          (programPT06WarpedNullCollarInverseTransition period hPeriod datum)
          current source
          (programPT06WarpedNullCollarInverseTransition_fderiv_comp
            period hPeriod datum)
          ((datum.transition_isLocalDiffeomorphAt.mdifferentiableAt
            (by norm_num)).differentiableAt)
    _ = _ := by
      have hGerm :=
        programPT06WarpedNullCollarTransition_faceCoordinate_eventuallyEq
          period hPeriod datum
      unfold programPT06NullFaceFluxPullback programPT06ThreeFormPullback
      rw [hGerm.eq_of_nhds, hGerm.fderiv_eq]

/-- At the selected point, signed pullback preserves the warped-face flux
three-form itself. -/
theorem programPT06WarpedNullCollarTransition_flux_covariance_warpedFace
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06NullFaceFluxPullback programPT06WarpedNullHyperplaneEmbedding
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current) source =
      programPT06NullFaceFluxPullback programPT06WarpedNullHyperplaneEmbedding
        current source := by
  rw [programPT06WarpedNullCollarTransition_flux_covariance_trueFace
    period hPeriod datum]
  have hFace :
      programPT06LocalC3NullFaceCoordinate period hPeriod incidence =ᶠ[𝓝 source]
        programPT06WarpedNullHyperplaneEmbedding := by
    filter_upwards [incidence.sourceDomain_isOpen.mem_nhds hSource] with
      currentPoint hCurrent
    simpa [programPT06ExplicitWarpedNullHyperplaneGeometry] using
      programPT06LocalC3NullFaceCoordinate_eq
        period hPeriod incidence currentPoint hCurrent
  unfold programPT06NullFaceFluxPullback programPT06ThreeFormPullback
  rw [hFace.eq_of_nhds, hFace.fderiv_eq]

/-- Scalar coefficient of the fixed source frame is preserved. -/
theorem programPT06WarpedNullCollarTransition_fluxRestriction_eq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
          period hPeriod datum current) source =
      programPT06WarpedNullHyperplaneFluxRestriction current source := by
  exact congrArg
    (fun form : ProgramPT06NullFaceSource3 [⋀^Fin 3]→L[Real] Real =>
      form programPT06NullFaceSourceFrame)
    (programPT06WarpedNullCollarTransition_flux_covariance_warpedFace
      period hPeriod datum current)

/-- Gate bundle: inverse normal transport and signed scalar flux covariance. -/
theorem programPT06WarpedNullCollarFluxCovariance_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06WarpedNullCollarInverseTransitionJacobian period hPeriod datum
        (programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
          (programPT06LocalC3NullCollarMap period hPeriod incidence
            (programPT06WarpedNullZeroFace source))) =
        programPT06AmbientCoordinateBasis 3 ∧
      programPT06WarpedNullHyperplaneFluxRestriction
          (programPT06WarpedNullCollarTransitionSignedPullbackCurrent
            period hPeriod datum current) source =
        programPT06WarpedNullHyperplaneFluxRestriction current source :=
  ⟨programPT06WarpedNullCollarInverseJacobian_trueCutBulkChartUnitNormal
      period hPeriod datum,
    programPT06WarpedNullCollarTransition_fluxRestriction_eq
      period hPeriod datum current⟩

end
end P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
end JanusFormal
