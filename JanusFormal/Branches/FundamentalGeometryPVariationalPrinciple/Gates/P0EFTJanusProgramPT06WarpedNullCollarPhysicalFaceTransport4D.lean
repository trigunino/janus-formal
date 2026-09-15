import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D

/-!
# Physical target-chart transport of warped-null face geometry

Gate 1058 identifies the null generator, normalized rigging, induced screen
metric, and oriented density in physical pullback coordinates.  This gate
transports the metric identities through the collar-transition Jacobian into the
genuine mapping-torus metric coefficients.  The target generator and rigging
remain a normalized null pair, the target screen metric is the explicit
positive warped screen metric, and its area is `exp u`.

The result remains point-local and conditional on Gate 1056's face-metric
datum.  It adds no regional metric compatibility or incidence inhabitant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceTransport4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
open P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
open P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricPullback4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem programPT06AmbientMetricPairing_eq_toBilin
    (metric : FiniteNullFaceAmbientMatrix4)
    (first second : ProgramPT06AmbientCoordinate4) :
    finiteNullFaceAmbientMetricPairing metric first second =
      Matrix.toBilin programPT06AmbientCoordinateBasis metric first second := by
  rw [Matrix.toBilin_apply]
  simp only [programPT06AmbientCoordinateBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  ring

/-- Evaluating a matrix congruence is the same as evaluating the original
metric on the transported vectors. -/
theorem programPT06AmbientMetricPairing_metricCongruence_toMatrix
    (linear : ProgramPT06AmbientCoordinate4 →ₗ[Real]
      ProgramPT06AmbientCoordinate4)
    (metric : FiniteNullFaceAmbientMatrix4)
    (first second : ProgramPT06AmbientCoordinate4) :
    finiteNullFaceAmbientMetricPairing
        (metricCongruence
          (LinearMap.toMatrix programPT06AmbientCoordinateBasis
            programPT06AmbientCoordinateBasis linear)
          metric)
        first second =
      finiteNullFaceAmbientMetricPairing metric (linear first) (linear second) := by
  rw [programPT06AmbientMetricPairing_eq_toBilin,
    programPT06AmbientMetricPairing_eq_toBilin]
  have hCongruence := Matrix.toBilin_comp
    (b := programPT06AmbientCoordinateBasis)
    (c := programPT06AmbientCoordinateBasis)
    metric
    (LinearMap.toMatrix programPT06AmbientCoordinateBasis
      programPT06AmbientCoordinateBasis linear)
    (LinearMap.toMatrix programPT06AmbientCoordinateBasis
      programPT06AmbientCoordinateBasis linear)
  have hApplied := congrArg
    (fun form : LinearMap.BilinForm Real ProgramPT06AmbientCoordinate4 =>
      form first second) hCongruence.symm
  simpa only [metricCongruence, LinearMap.BilinForm.comp_apply,
    Matrix.toLin_toMatrix] using hApplied

/-- Generator transported into the genuine bulk-chart coordinates. -/
def programPT06WarpedNullPhysicalTransportedGenerator
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
    (programPT06WarpedNullHyperplaneGeneratorDifferential 1)

/-- Screen differential transported into the genuine bulk-chart coordinates. -/
def programPT06WarpedNullPhysicalTransportedScreenDifferential
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    FiniteNullFaceScreenCoordinate2 →L[Real] ProgramPT06AmbientCoordinate4 :=
  (programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
      ).toContinuousLinearMap.comp
    programPT06WarpedNullHyperplaneScreenDifferential

/-- Gate 1058's normalized null rigging transported into the genuine chart. -/
def programPT06WarpedNullPhysicalTransportedRigging
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
    (programPT06WarpedNullNormalizedNullRigging source)

/-- Genuine physical metric matrix in the incidence chart at the face. -/
def programPT06WarpedNullPhysicalTargetMetricAtFace
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) : FiniteNullFaceAmbientMatrix4 :=
  programPT06EffectiveBulkChartPhysicalMetricMatrix period hPeriod
    physical.physicalMetric incidence.chartAnchor
    (programPT06WarpedNullHyperplaneEmbedding source)

/-- Pairing in the pulled-back physical metric is pairing of the transported
vectors in the genuine target metric. -/
theorem programPT06WarpedNullPhysicalPullback_pairing_eq_target
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum)
    (first second : ProgramPT06AmbientCoordinate4) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        first second =
      finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
        (programPT06WarpedNullCollarTransitionJacobian
          period hPeriod datum first)
        (programPT06WarpedNullCollarTransitionJacobian
          period hPeriod datum second) := by
  unfold programPT06WarpedNullCollarPhysicalPullbackMetric
    programPT06WarpedNullCollarMetricPullback
    programPT06WarpedNullPhysicalTargetMetricAtFace
  rw [programPT06WarpedNullCollarTransitionFDerivMatrix_face,
    datum.transition_face period hPeriod]
  unfold programPT06WarpedNullCollarTransitionJacobianMatrix
  exact programPT06AmbientMetricPairing_metricCongruence_toMatrix
    (programPT06WarpedNullCollarTransitionJacobian
      period hPeriod datum).toLinearEquiv.toLinearMap
    (programPT06EffectiveBulkChartPhysicalMetricMatrix period hPeriod
      physical.physicalMetric incidence.chartAnchor
      (programPT06WarpedNullHyperplaneEmbedding source)) first second

/-- The transported generator is null for the genuine physical target metric. -/
theorem programPT06WarpedNullPhysicalTransportedGenerator_null
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
        (programPT06WarpedNullPhysicalTransportedGenerator period hPeriod datum)
        (programPT06WarpedNullPhysicalTransportedGenerator period hPeriod datum) = 0 := by
  unfold programPT06WarpedNullPhysicalTransportedGenerator
  rw [← programPT06WarpedNullPhysicalPullback_pairing_eq_target period hPeriod physical]
  exact
    P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D.ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.generator_null
      period hPeriod physical

/-- The transported generator is orthogonal to the transported screen. -/
theorem programPT06WarpedNullPhysicalTransportedGenerator_screen_orthogonal
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum)
    (index : Fin 2) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
        (programPT06WarpedNullPhysicalTransportedGenerator period hPeriod datum)
        (programPT06WarpedNullPhysicalTransportedScreenDifferential period hPeriod datum
          (EuclideanSpace.single index 1)) = 0 := by
  unfold programPT06WarpedNullPhysicalTransportedGenerator programPT06WarpedNullPhysicalTransportedScreenDifferential
  simp only [ContinuousLinearMap.comp_apply]
  change finiteNullFaceAmbientMetricPairing
      (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
      ((programPT06WarpedNullCollarTransitionJacobian period hPeriod datum)
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1))
      ((programPT06WarpedNullCollarTransitionJacobian period hPeriod datum)
        (programPT06WarpedNullHyperplaneScreenDifferential
          (EuclideanSpace.single index 1))) = 0
  rw [← programPT06WarpedNullPhysicalPullback_pairing_eq_target period hPeriod physical,
    physical.pullback_metric_face]
  fin_cases index <;>
    simp [finiteNullFaceAmbientMetricPairing,
      programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]

/-- Screen matrix induced by the transported screen in the physical target
metric. -/
def programPT06WarpedNullPhysicalTransportedScreenMetric
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) : Matrix2 :=
  fun first second =>
    finiteNullFaceInducedScreenMetricComponent
      (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
      (programPT06WarpedNullPhysicalTransportedScreenDifferential period hPeriod datum) first second

/-- The physical target screen matrix is exactly the explicit warped screen
matrix. -/
theorem programPT06WarpedNullPhysicalTransportedScreenMetric_eq_warped
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    programPT06WarpedNullPhysicalTransportedScreenMetric period hPeriod physical =
      programPT06WarpedNullHyperplaneScreenMetric source.1 := by
  funext first second
  unfold programPT06WarpedNullPhysicalTransportedScreenMetric finiteNullFaceInducedScreenMetricComponent
    programPT06WarpedNullPhysicalTransportedScreenDifferential
  simp only [ContinuousLinearMap.comp_apply]
  calc
    _ = finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullHyperplaneScreenDifferential
          (EuclideanSpace.single first 1))
        (programPT06WarpedNullHyperplaneScreenDifferential
          (EuclideanSpace.single second 1)) :=
      (programPT06WarpedNullPhysicalPullback_pairing_eq_target period hPeriod physical _ _).symm
    _ = _ :=
      P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D.ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.inducedScreenMetric_eq_explicit
        period hPeriod physical first second

/-- The physical target screen area has the expected density `exp u`. -/
theorem programPT06WarpedNullPhysicalTransportedScreenArea_eq_exp
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    Real.sqrt |Matrix.det (programPT06WarpedNullPhysicalTransportedScreenMetric period hPeriod physical)| =
      Real.exp source.1 := by
  rw [programPT06WarpedNullPhysicalTransportedScreenMetric_eq_warped period hPeriod physical]
  simpa [finiteNullFaceHomogeneousScreenArea] using
    programPT06WarpedNullHyperplaneScreenArea source.1

/-- The transported rigging stays null for the genuine target metric. -/
theorem programPT06WarpedNullPhysicalTransportedRigging_null
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
        (programPT06WarpedNullPhysicalTransportedRigging period hPeriod datum)
        (programPT06WarpedNullPhysicalTransportedRigging period hPeriod datum) = 0 := by
  unfold programPT06WarpedNullPhysicalTransportedRigging
  rw [← programPT06WarpedNullPhysicalPullback_pairing_eq_target period hPeriod physical]
  exact
    P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D.ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_null
      period hPeriod physical

/-- The transported null pair retains `g(N,k) = -1`. -/
theorem programPT06WarpedNullPhysicalTransportedRigging_generator
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
        (programPT06WarpedNullPhysicalTransportedRigging period hPeriod datum)
        (programPT06WarpedNullPhysicalTransportedGenerator period hPeriod datum) = -1 := by
  unfold programPT06WarpedNullPhysicalTransportedRigging programPT06WarpedNullPhysicalTransportedGenerator
  rw [← programPT06WarpedNullPhysicalPullback_pairing_eq_target period hPeriod physical]
  exact
    P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D.ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_generator
      period hPeriod physical

/-- The transported rigging stays orthogonal to the physical screen. -/
theorem programPT06WarpedNullPhysicalTransportedRigging_screen_orthogonal
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum)
    (index : Fin 2) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
        (programPT06WarpedNullPhysicalTransportedRigging period hPeriod datum)
        (programPT06WarpedNullPhysicalTransportedScreenDifferential period hPeriod datum
          (EuclideanSpace.single index 1)) = 0 := by
  unfold programPT06WarpedNullPhysicalTransportedRigging programPT06WarpedNullPhysicalTransportedScreenDifferential
  simp only [ContinuousLinearMap.comp_apply]
  change finiteNullFaceAmbientMetricPairing
      (programPT06WarpedNullPhysicalTargetMetricAtFace period hPeriod physical)
      ((programPT06WarpedNullCollarTransitionJacobian period hPeriod datum)
        (programPT06WarpedNullNormalizedNullRigging source))
      ((programPT06WarpedNullCollarTransitionJacobian period hPeriod datum)
        (programPT06WarpedNullHyperplaneScreenDifferential
          (EuclideanSpace.single index 1))) = 0
  rw [← programPT06WarpedNullPhysicalPullback_pairing_eq_target period hPeriod physical]
  exact
    P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D.ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_screen_orthogonal
      period hPeriod physical index

end
end P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceTransport4D
end JanusFormal
