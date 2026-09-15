import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionDensityCovariance

/-!
# Warped-null collar metric-volume covariance

Gate 1051 identifies the positive absolute Jacobian weight of the local
collar transition.  This gate writes its derivative in the fixed ambient
basis and proves the corresponding metric-volume transformation law.

If the pullback of a supplied target metric matrix is the explicit warped
metric at the selected face point, its target volume density transforms into
the warped density and hence into the homogeneous screen area.  That metric
compatibility remains an explicit point-local hypothesis; no physical bulk
metric field or atlas gluing is constructed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Matrix of the local collar-transition Jacobian in the fixed ambient
coordinate basis. -/
def programPT06WarpedNullCollarTransitionJacobianMatrix
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    FiniteNullFaceAmbientMatrix4 :=
  LinearMap.toMatrix programPT06AmbientCoordinateBasis
    programPT06AmbientCoordinateBasis
    (programPT06WarpedNullCollarTransitionJacobian
      period hPeriod datum).toLinearEquiv.toLinearMap

/-- Gate 1048's abstract determinant is the determinant of its fixed-basis
Jacobian matrix. -/
theorem programPT06WarpedNullCollarTransitionJacobianMatrix_det
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    Matrix.det (programPT06WarpedNullCollarTransitionJacobianMatrix
      period hPeriod datum) =
      LinearMap.det
        (programPT06WarpedNullCollarTransitionJacobian
          period hPeriod datum).toLinearEquiv.toLinearMap := by
  exact LinearMap.det_toMatrix programPT06AmbientCoordinateBasis _

/-- The positive transition density is the absolute determinant of the
fixed-basis Jacobian matrix. -/
theorem programPT06WarpedNullCollarTransitionJacobianDensity_eq_matrix
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum =
      |Matrix.det (programPT06WarpedNullCollarTransitionJacobianMatrix
        period hPeriod datum)| := by
  rw [programPT06WarpedNullCollarTransitionJacobianDensity,
    programPT06WarpedNullCollarTransitionJacobianMatrix_det]

/-- Coordinate metric volume has absolute Jacobian weight under the local
collar transition. -/
theorem programPT06WarpedNullCollarMetricVolume_weight
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : FiniteNullFaceAmbientMatrix4) :
    Real.sqrt |Matrix.det
        (metricCongruence
          (programPT06WarpedNullCollarTransitionJacobianMatrix
            period hPeriod datum)
          targetMetric)| =
      programPT06WarpedNullCollarTransitionJacobianDensity
          period hPeriod datum *
        Real.sqrt |Matrix.det targetMetric| := by
  rw [metricVolume_diagonal_weight,
    ← programPT06WarpedNullCollarTransitionJacobianDensity_eq_matrix]

/-- If the target metric pulls back to the warped face metric, its volume
density pulls back to the explicit warped density. -/
theorem programPT06WarpedNullCollarMetricVolume_compatible
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : FiniteNullFaceAmbientMatrix4)
    (hMetric :
      metricCongruence
          (programPT06WarpedNullCollarTransitionJacobianMatrix
            period hPeriod datum)
          targetMetric =
        programPT06WarpedNullHyperplaneAmbientMetric
          (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06WarpedNullAmbientMetricVolumeDensity
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullCollarTransitionJacobianDensity
          period hPeriod datum *
        Real.sqrt |Matrix.det targetMetric| := by
  change Real.sqrt |Matrix.det
      (programPT06WarpedNullHyperplaneAmbientMetric
        (programPT06WarpedNullHyperplaneEmbedding source))| = _
  rw [← hMetric]
  exact programPT06WarpedNullCollarMetricVolume_weight
    period hPeriod datum targetMetric

/-- Under the same point-local metric compatibility, the warped screen area
is the target metric density multiplied by the transition Jacobian density. -/
theorem programPT06WarpedNullCollarScreenArea_compatible
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : FiniteNullFaceAmbientMatrix4)
    (hMetric :
      metricCongruence
          (programPT06WarpedNullCollarTransitionJacobianMatrix
            period hPeriod datum)
          targetMetric =
        programPT06WarpedNullHyperplaneAmbientMetric
          (programPT06WarpedNullHyperplaneEmbedding source)) :
    finiteNullFaceHomogeneousScreenArea
        programPT06WarpedNullHyperplaneScreenMetric source.1 =
      programPT06WarpedNullCollarTransitionJacobianDensity
          period hPeriod datum *
        Real.sqrt |Matrix.det targetMetric| := by
  rw [← programPT06WarpedNullMetricVolumeDensity_face_eq_screenArea]
  exact programPT06WarpedNullCollarMetricVolume_compatible
    period hPeriod datum targetMetric hMetric

/-- Point-local metric-volume covariance bundle. -/
theorem programPT06WarpedNullCollarMetricVolumeCovariance_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : FiniteNullFaceAmbientMatrix4)
    (hMetric :
      metricCongruence
          (programPT06WarpedNullCollarTransitionJacobianMatrix
            period hPeriod datum)
          targetMetric =
        programPT06WarpedNullHyperplaneAmbientMetric
          (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum =
        |Matrix.det (programPT06WarpedNullCollarTransitionJacobianMatrix
          period hPeriod datum)| ∧
      programPT06WarpedNullAmbientMetricVolumeDensity
          (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06WarpedNullCollarTransitionJacobianDensity
            period hPeriod datum *
          Real.sqrt |Matrix.det targetMetric| ∧
      finiteNullFaceHomogeneousScreenArea
          programPT06WarpedNullHyperplaneScreenMetric source.1 =
        programPT06WarpedNullCollarTransitionJacobianDensity
            period hPeriod datum *
          Real.sqrt |Matrix.det targetMetric| := by
  exact ⟨programPT06WarpedNullCollarTransitionJacobianDensity_eq_matrix
      period hPeriod datum,
    programPT06WarpedNullCollarMetricVolume_compatible
      period hPeriod datum targetMetric hMetric,
    programPT06WarpedNullCollarScreenArea_compatible
      period hPeriod datum targetMetric hMetric⟩

end

end P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D
end JanusFormal
