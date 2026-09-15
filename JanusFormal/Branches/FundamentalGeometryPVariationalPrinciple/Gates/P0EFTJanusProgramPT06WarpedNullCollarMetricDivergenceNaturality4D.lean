import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D

/-!
# Warped-null collar metric-divergence naturality

Gate 1052 proves the metric-volume law at one face point.  This gate assumes
the corresponding metric congruence throughout the local transition germ.
It then identifies the warped volume-densitized pullback current with Gate
1051's absolute Piola pullback and proves naturality of metric divergence at
the selected face point.

The target metric is still a supplied coordinate field.  Its congruence with
the warped metric is conditional and local; no physical bulk metric or atlas
gluing is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter
open scoped Manifold Topology
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
open P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Matrix of the transition derivative at an arbitrary nearby coordinate. -/
def programPT06WarpedNullCollarTransitionFDerivMatrix
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  LinearMap.toMatrix programPT06AmbientCoordinateBasis
    programPT06AmbientCoordinateBasis
    (fderiv Real datum.transition coordinate).toLinearMap

/-- At the selected face point, the derivative matrix is Gate 1052's
invertible Jacobian matrix. -/
theorem programPT06WarpedNullCollarTransitionFDerivMatrix_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarTransitionFDerivMatrix
        period hPeriod datum
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarTransitionJacobianMatrix
        period hPeriod datum := by
  have hJacobian := programPT06WarpedNullCollarTransitionJacobian_coe
    period hPeriod datum
  rw [mfderiv_eq_fderiv] at hJacobian
  change LinearMap.toMatrix programPT06AmbientCoordinateBasis
      programPT06AmbientCoordinateBasis
        (fderiv Real datum.transition
          (programPT06WarpedNullHyperplaneEmbedding source)).toLinearMap =
    LinearMap.toMatrix programPT06AmbientCoordinateBasis
      programPT06AmbientCoordinateBasis
        ((programPT06WarpedNullCollarTransitionJacobian
          period hPeriod datum :
            ProgramPT06AmbientCoordinate4 →L[Real]
              ProgramPT06AmbientCoordinate4).toLinearMap)
  rw [← hJacobian]

/-- A target metric field whose pullback agrees with the warped metric
throughout the selected transition germ. -/
structure ProgramPT06WarpedNullCollarMetricGermDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) where
  targetMetric : ProgramPT06AmbientCoordinate4 →
    FiniteNullFaceAmbientMatrix4
  pullback_metric_eventuallyEq :
    (fun coordinate =>
      metricCongruence
        (programPT06WarpedNullCollarTransitionFDerivMatrix
          period hPeriod datum coordinate)
        (targetMetric (datum.transition coordinate))) =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
      programPT06WarpedNullHyperplaneAmbientMetric

/-- Coordinate volume density of a supplied ambient metric matrix field. -/
def programPT06AmbientMatrixMetricVolumeDensity
    (metric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (coordinate : ProgramPT06AmbientCoordinate4) : Real :=
  Real.sqrt |Matrix.det (metric coordinate)|

/-- Current densitized by a supplied ambient metric matrix field. -/
def programPT06AmbientMatrixMetricVolumeCurrent
    (metric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (current : ProgramPT06AmbientCurrent4D) : ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    programPT06AmbientMatrixMetricVolumeDensity metric coordinate •
      current coordinate

/-- Coordinate formula for divergence with respect to a supplied metric
volume density. -/
def programPT06AmbientMatrixMetricVolumeDivergence
    (metric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4) : Real :=
  programPT06AmbientCoordinateDivergence
      (programPT06AmbientMatrixMetricVolumeCurrent metric current)
      coordinate /
    programPT06AmbientMatrixMetricVolumeDensity metric coordinate

/-- The generic matrix-field density specializes definitionally to Gate
1043's warped density. -/
@[simp] theorem programPT06AmbientMatrixMetricVolumeDensity_warped
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientMatrixMetricVolumeDensity
        programPT06WarpedNullHyperplaneAmbientMetric coordinate =
      programPT06WarpedNullAmbientMetricVolumeDensity coordinate := by
  rfl

/-- The generic volume current specializes to Gate 1043's warped volume
current. -/
theorem programPT06AmbientMatrixMetricVolumeCurrent_warped
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06AmbientMatrixMetricVolumeCurrent
        programPT06WarpedNullHyperplaneAmbientMetric current =
      programPT06WarpedNullMetricVolumeCurrent current := by
  rfl

/-- The generic metric-divergence formula specializes to Gate 1043's warped
formula. -/
theorem programPT06AmbientMatrixMetricVolumeDivergence_warped
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientMatrixMetricVolumeDivergence
        programPT06WarpedNullHyperplaneAmbientMetric current coordinate =
      programPT06WarpedNullMetricVolumeDivergence current coordinate := by
  rfl

/-- Ordinary vector-field pullback through the transition and Gate 1049's
chosen local inverse. -/
def programPT06WarpedNullCollarTransitionVectorPullbackCurrent
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D) : ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    fderiv Real
      (programPT06WarpedNullCollarInverseTransition period hPeriod datum)
      (datum.transition coordinate)
      (current (datum.transition coordinate))

/-- The germ congruence specializes to Gate 1052's pointwise metric
compatibility. -/
theorem ProgramPT06WarpedNullCollarMetricGermDatum.metric_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (compatibility : ProgramPT06WarpedNullCollarMetricGermDatum
      period hPeriod datum) :
    metricCongruence
        (programPT06WarpedNullCollarTransitionJacobianMatrix
          period hPeriod datum)
        (compatibility.targetMetric
          (programPT06WarpedNullHyperplaneEmbedding source)) =
      programPT06WarpedNullHyperplaneAmbientMetric
        (programPT06WarpedNullHyperplaneEmbedding source) := by
  have hMetric := compatibility.pullback_metric_eventuallyEq.eq_of_nhds
  rw [programPT06WarpedNullCollarTransitionFDerivMatrix_face,
    datum.transition_face period hPeriod] at hMetric
  exact hMetric

/-- Metric congruence on the transition germ gives the absolute density
transformation law throughout that germ. -/
theorem ProgramPT06WarpedNullCollarMetricGermDatum.volumeDensity_eventuallyEq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (compatibility : ProgramPT06WarpedNullCollarMetricGermDatum
      period hPeriod datum) :
    programPT06WarpedNullAmbientMetricVolumeDensity =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
      fun coordinate =>
        |LinearMap.det
          (fderiv Real datum.transition coordinate).toLinearMap| *
        programPT06AmbientMatrixMetricVolumeDensity
          compatibility.targetMetric (datum.transition coordinate) := by
  filter_upwards [compatibility.pullback_metric_eventuallyEq] with
    coordinate hMetric
  change Real.sqrt |Matrix.det
      (programPT06WarpedNullHyperplaneAmbientMetric coordinate)| = _
  rw [← hMetric, metricVolume_diagonal_weight]
  unfold programPT06WarpedNullCollarTransitionFDerivMatrix
    programPT06AmbientMatrixMetricVolumeDensity
  rw [LinearMap.det_toMatrix]

/-- The warped volume-densitized ordinary pullback is the absolute Piola
pullback of the target volume-densitized current as a germ. -/
theorem ProgramPT06WarpedNullCollarMetricGermDatum.volumeCurrent_eventuallyEq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (compatibility : ProgramPT06WarpedNullCollarMetricGermDatum
      period hPeriod datum)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06WarpedNullMetricVolumeCurrent
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current) =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
      programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
        period hPeriod datum
        (programPT06AmbientMatrixMetricVolumeCurrent
          compatibility.targetMetric current) := by
  filter_upwards [compatibility.volumeDensity_eventuallyEq
    period hPeriod] with coordinate hDensity
  unfold programPT06WarpedNullMetricVolumeCurrent
    programPT06WarpedNullCollarTransitionVectorPullbackCurrent
    programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
    programPT06AmbientAbsoluteVectorPullback
    programPT06AmbientMatrixMetricVolumeCurrent
  rw [hDensity, map_smul, smul_smul]

/-- Metric divergence is natural at the face point under germ-level metric
compatibility and differentiability of the target densitized current. -/
theorem programPT06WarpedNullCollarMetricDivergence_natural
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
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        compatibility.targetMetric current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06WarpedNullMetricVolumeDivergence
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence
        compatibility.targetMetric current
        (programPT06WarpedNullHyperplaneEmbedding source) := by
  have hVolumeCurrent := compatibility.volumeCurrent_eventuallyEq
    period hPeriod current
  have hVolume := programPT06WarpedNullCollarMetricVolume_compatible
    period hPeriod datum
    (compatibility.targetMetric
      (programPT06WarpedNullHyperplaneEmbedding source))
    (compatibility.metric_face period hPeriod)
  have hJacobian : 0 <
      programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum :=
    programPT06WarpedNullCollarTransitionJacobianDensity_pos
      period hPeriod datum
  unfold programPT06WarpedNullMetricVolumeDivergence
  rw [programPT06AmbientCoordinateDivergence_congr hVolumeCurrent,
    programPT06WarpedNullCollarTransitionAbsolutePullback_divergence
      period hPeriod datum _ hCurrent,
    hVolume]
  unfold programPT06AmbientMatrixMetricVolumeDivergence
    programPT06AmbientMatrixMetricVolumeDensity
  rw [mul_div_mul_left _ _ (ne_of_gt hJacobian)]

/-- Germ-level metric-divergence naturality bundle. -/
theorem programPT06WarpedNullCollarMetricDivergenceNaturality_bundle
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
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        compatibility.targetMetric current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    metricCongruence
        (programPT06WarpedNullCollarTransitionJacobianMatrix
          period hPeriod datum)
        (compatibility.targetMetric
          (programPT06WarpedNullHyperplaneEmbedding source)) =
        programPT06WarpedNullHyperplaneAmbientMetric
          (programPT06WarpedNullHyperplaneEmbedding source) ∧
      programPT06WarpedNullMetricVolumeDivergence
          (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06AmbientMatrixMetricVolumeDivergence
          compatibility.targetMetric current
          (programPT06WarpedNullHyperplaneEmbedding source) := by
  exact ⟨compatibility.metric_face period hPeriod,
    programPT06WarpedNullCollarMetricDivergence_natural
      period hPeriod compatibility current hCurrent⟩

end

end P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
end JanusFormal
