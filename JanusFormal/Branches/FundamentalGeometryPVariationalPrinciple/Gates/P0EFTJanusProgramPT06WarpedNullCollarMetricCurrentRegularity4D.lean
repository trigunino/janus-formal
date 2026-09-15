import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D

/-!
# Warped-null collar metric-current regularity

Gate 1053 assumes differentiability of the target current after multiplication
by its metric volume density.  The metric-volume cocycle and Gate 1049's local
inverse imply differentiability of that target density directly from the
explicit smooth warped density.  Thus an ordinary differentiable target
current supplies the regularity required by metric-divergence naturality.

The argument applies to every metric germ of Gate 1053 and hence to the
physical metric germ of Gate 1054.  Existence of either compatibility datum
remains an explicit hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarMetricCurrentRegularity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
open P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Absolute determinant of the transition derivative as a scalar field. -/
def programPT06WarpedNullCollarJacobianDensityField
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (coordinate : ProgramPT06AmbientCoordinate4) : Real :=
  |LinearMap.det (fderiv Real datum.transition coordinate).toLinearMap|

/-- The transition Jacobian density field is differentiable at the selected
face point. -/
theorem programPT06WarpedNullCollarJacobianDensityField_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    DifferentiableAt Real
      (programPT06WarpedNullCollarJacobianDensityField
        period hPeriod datum)
      (programPT06WarpedNullHyperplaneEmbedding source) := by
  let coordinate := programPT06WarpedNullHyperplaneEmbedding source
  have hForward : ContDiffAt Real 2 datum.transition coordinate :=
    (datum.transition_isLocalDiffeomorphAt.contMDiffAt.contDiffAt).of_le
      (by norm_num)
  have hForwardJacobian : ContDiffAt Real 1
      (fderiv Real datum.transition) coordinate :=
    hForward.fderiv_right (m := 1) (by norm_num)
  have hDeterminant : DifferentiableAt Real
      (fun nearby =>
        LinearMap.det (fderiv Real datum.transition nearby).toLinearMap)
      coordinate :=
    ((programPT06AmbientEndomorphismDeterminant_contDiff.contDiffAt.of_le
      (by norm_num)).comp coordinate hForwardJacobian).differentiableAt
      (by norm_num)
  have hDeterminantNonzero :
      LinearMap.det (fderiv Real datum.transition coordinate).toLinearMap ≠
        0 := by
    rw [← programPT06WarpedNullCollarTransitionSignedJacobian_eq_fderiv
      period hPeriod datum]
    have hPositive : 0 <
        |programPT06WarpedNullCollarTransitionSignedJacobian
          period hPeriod datum| := by
      rw [programPT06WarpedNullCollarTransitionSignedJacobian_abs
        period hPeriod datum]
      exact programPT06WarpedNullCollarTransitionJacobianDensity_pos
        period hPeriod datum
    exact abs_pos.mp hPositive
  exact hDeterminant.abs hDeterminantNonzero

/-- The explicit warped metric density is differentiable everywhere. -/
theorem programPT06WarpedNullAmbientMetricVolumeDensity_differentiableAt
    (coordinate : ProgramPT06AmbientCoordinate4) :
    DifferentiableAt Real programPT06WarpedNullAmbientMetricVolumeDensity
      coordinate := by
  have hCoordinate : DifferentiableAt Real
      (fun nearby : ProgramPT06AmbientCoordinate4 => nearby 0) coordinate :=
    (PiLp.hasFDerivAt_apply 2 coordinate (0 : Fin 4)).differentiableAt
  rw [show programPT06WarpedNullAmbientMetricVolumeDensity =
      fun nearby => Real.exp (nearby 0) by
    funext nearby
    exact programPT06WarpedNullAmbientMetricVolumeDensity_eq nearby]
  simpa only [Function.comp_def] using
    Real.differentiable_exp.differentiableAt.comp coordinate hCoordinate

/-- The metric-volume cocycle and the local inverse force the target metric
density to be differentiable at the fixed face point. -/
theorem ProgramPT06WarpedNullCollarMetricGermDatum.targetVolumeDensity_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (compatibility : ProgramPT06WarpedNullCollarMetricGermDatum
      period hPeriod datum) :
    DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeDensity
        compatibility.targetMetric)
      (programPT06WarpedNullHyperplaneEmbedding source) := by
  let coordinate := programPT06WarpedNullHyperplaneEmbedding source
  let jacobian := programPT06WarpedNullCollarJacobianDensityField
    period hPeriod datum
  let targetDensity := programPT06AmbientMatrixMetricVolumeDensity
    compatibility.targetMetric
  let reverse :=
    programPT06WarpedNullCollarInverseTransition period hPeriod datum
  have hWarped : DifferentiableAt Real
      programPT06WarpedNullAmbientMetricVolumeDensity coordinate :=
    programPT06WarpedNullAmbientMetricVolumeDensity_differentiableAt coordinate
  have hJacobian : DifferentiableAt Real jacobian coordinate := by
    exact programPT06WarpedNullCollarJacobianDensityField_differentiableAt
      period hPeriod datum
  have hProduct : DifferentiableAt Real
      (fun nearby =>
        jacobian nearby * targetDensity (datum.transition nearby))
      coordinate := by
    apply (compatibility.volumeDensity_eventuallyEq
      period hPeriod).differentiableAt_iff.mp
    exact hWarped
  have hJacobianNonzero : jacobian coordinate ≠ 0 := by
    dsimp only [jacobian, coordinate,
      programPT06WarpedNullCollarJacobianDensityField]
    rw [← programPT06WarpedNullCollarTransitionSignedJacobian_eq_fderiv
      period hPeriod datum,
      programPT06WarpedNullCollarTransitionSignedJacobian_abs
        period hPeriod datum]
    exact ne_of_gt
      (programPT06WarpedNullCollarTransitionJacobianDensity_pos
        period hPeriod datum)
  have hJacobianEventuallyNonzero :
      ∀ᶠ nearby in 𝓝 coordinate, jacobian nearby ≠ 0 :=
    hJacobian.continuousAt.eventually_ne hJacobianNonzero
  have hJacobianInverse : DifferentiableAt Real
      (fun nearby : ProgramPT06AmbientCoordinate4 =>
        (jacobian nearby)⁻¹) coordinate :=
    hJacobian.inv hJacobianNonzero
  have hQuotient : DifferentiableAt Real
      (fun nearby =>
        (jacobian nearby * targetDensity (datum.transition nearby)) *
          (jacobian nearby)⁻¹)
      coordinate :=
    hProduct.mul hJacobianInverse
  have hQuotientEventuallyEq :
      (fun nearby =>
        (jacobian nearby * targetDensity (datum.transition nearby)) *
          (jacobian nearby)⁻¹) =ᶠ[𝓝 coordinate]
        fun nearby => targetDensity (datum.transition nearby) :=
    hJacobianEventuallyNonzero.mono fun nearby hNearby => by
      change jacobian nearby * targetDensity (datum.transition nearby) *
          (jacobian nearby)⁻¹ =
        targetDensity (datum.transition nearby)
      calc
        _ = targetDensity (datum.transition nearby) *
            (jacobian nearby * (jacobian nearby)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hNearby, mul_one]
  have hTargetAlongForward : DifferentiableAt Real
      (fun nearby => targetDensity (datum.transition nearby)) coordinate :=
    hQuotientEventuallyEq.differentiableAt_iff.mp hQuotient
  have hReverseAtForward : DifferentiableAt Real reverse
      (datum.transition coordinate) :=
    (datum.transition_isLocalDiffeomorphAt.localInverse_contMDiffAt.contDiffAt
      ).differentiableAt (by norm_num)
  have hReverse : DifferentiableAt Real reverse coordinate := by
    rw [show datum.transition coordinate = coordinate by
      exact datum.transition_face period hPeriod] at hReverseAtForward
    exact hReverseAtForward
  have hTargetAlongForwardAtReverse : DifferentiableAt Real
      (fun nearby => targetDensity (datum.transition nearby))
      (reverse coordinate) := by
    rw [show reverse coordinate = coordinate by
      exact programPT06WarpedNullCollarInverseTransition_face
        period hPeriod datum]
    exact hTargetAlongForward
  have hBack : DifferentiableAt Real
      (fun nearby => targetDensity (datum.transition (reverse nearby)))
      coordinate :=
    hTargetAlongForwardAtReverse.comp coordinate hReverse
  have hBackEventuallyEq :
      (fun nearby => targetDensity (datum.transition (reverse nearby))) =ᶠ[
        𝓝 coordinate] targetDensity := by
    filter_upwards [
      programPT06WarpedNullCollarInverseTransition_eventuallyEq_right
        period hPeriod datum] with nearby hNearby
    exact congrArg targetDensity hNearby
  exact hBackEventuallyEq.differentiableAt_iff.mp hBack

/-- An ordinary differentiable target current becomes differentiable after
densitization by every compatible target metric germ. -/
theorem ProgramPT06WarpedNullCollarMetricGermDatum.volumeCurrent_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (compatibility : ProgramPT06WarpedNullCollarMetricGermDatum
      period hPeriod datum)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        compatibility.targetMetric current)
      (programPT06WarpedNullHyperplaneEmbedding source) := by
  unfold programPT06AmbientMatrixMetricVolumeCurrent
  exact (ProgramPT06WarpedNullCollarMetricGermDatum.targetVolumeDensity_differentiableAt
      period hPeriod compatibility).smul hCurrent

/-- Metric-divergence naturality now requires only ordinary `C¹` regularity
of the target current. -/
theorem programPT06WarpedNullCollarMetricDivergence_natural_of_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (compatibility : ProgramPT06WarpedNullCollarMetricGermDatum
      period hPeriod datum)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06WarpedNullMetricVolumeDivergence
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence
        compatibility.targetMetric current
        (programPT06WarpedNullHyperplaneEmbedding source) :=
  programPT06WarpedNullCollarMetricDivergence_natural
    period hPeriod compatibility current
    (ProgramPT06WarpedNullCollarMetricGermDatum.volumeCurrent_differentiableAt
        period hPeriod compatibility current hCurrent)

/-- Physical metric-divergence naturality with only ordinary current
regularity. -/
theorem programPT06WarpedNullCollarPhysicalMetricDivergence_natural_of_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06WarpedNullMetricVolumeDivergence
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor)
        current (programPT06WarpedNullHyperplaneEmbedding source) :=
  programPT06WarpedNullCollarMetricDivergence_natural_of_differentiableAt
    period hPeriod physical.toMetricGermDatum current hCurrent

/-- Regular physical metric-divergence bundle. -/
theorem programPT06WarpedNullCollarMetricCurrentRegularity_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    DifferentiableAt Real
        (programPT06AmbientMatrixMetricVolumeDensity
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physical.physicalMetric incidence.chartAnchor))
        (programPT06WarpedNullHyperplaneEmbedding source) ∧
      DifferentiableAt Real
        (programPT06AmbientMatrixMetricVolumeCurrent
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physical.physicalMetric incidence.chartAnchor)
          current)
        (programPT06WarpedNullHyperplaneEmbedding source) ∧
      programPT06WarpedNullMetricVolumeDivergence
          (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physical.physicalMetric incidence.chartAnchor)
          current (programPT06WarpedNullHyperplaneEmbedding source) := by
  exact ⟨ProgramPT06WarpedNullCollarMetricGermDatum.targetVolumeDensity_differentiableAt
        period hPeriod physical.toMetricGermDatum,
    ProgramPT06WarpedNullCollarMetricGermDatum.volumeCurrent_differentiableAt
        period hPeriod physical.toMetricGermDatum current hCurrent,
    programPT06WarpedNullCollarPhysicalMetricDivergence_natural_of_differentiableAt
      period hPeriod physical current hCurrent⟩

end

end P0EFTJanusProgramPT06WarpedNullCollarMetricCurrentRegularity4D
end JanusFormal
