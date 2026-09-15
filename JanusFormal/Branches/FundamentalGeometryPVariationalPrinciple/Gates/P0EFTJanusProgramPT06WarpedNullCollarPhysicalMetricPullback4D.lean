import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D

/-!
# Physical metric pullback on the warped-null collar

The preceding metric-germ bridge asks the fixed warped metric to equal the
pullback of a physical metric throughout a germ.  This gate instead defines
the collar metric to be that physical pullback.  Metric-volume and divergence
naturality are then unconditional consequences of congruence and the absolute
Piola law.  Matching this physical collar metric to the explicit warped screen
area is then reduced to a pointwise face condition.  Identifying derivatives
with the fixed warped metric still requires equality on a germ.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricPullback4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
open P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pull a target metric matrix field back through the collar transition. -/
def programPT06WarpedNullCollarMetricPullback
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  metricCongruence
    (programPT06WarpedNullCollarTransitionFDerivMatrix
      period hPeriod datum coordinate)
    (targetMetric (datum.transition coordinate))

/-- Metric volume transforms pointwise by the absolute transition
Jacobian. -/
theorem programPT06WarpedNullCollarMetricPullback_volumeDensity
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientMatrixMetricVolumeDensity
        (programPT06WarpedNullCollarMetricPullback
          period hPeriod datum targetMetric) coordinate =
      |LinearMap.det
          (fderiv Real datum.transition coordinate).toLinearMap| *
        programPT06AmbientMatrixMetricVolumeDensity targetMetric
          (datum.transition coordinate) := by
  unfold programPT06WarpedNullCollarMetricPullback
    programPT06AmbientMatrixMetricVolumeDensity
  rw [metricVolume_diagonal_weight]
  unfold programPT06WarpedNullCollarTransitionFDerivMatrix
  rw [LinearMap.det_toMatrix]

/-- Densitizing the ordinary vector pullback by the pulled metric gives the
absolute Piola pullback of the target metric-volume current. -/
theorem programPT06WarpedNullCollarMetricPullback_volumeCurrent
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06WarpedNullCollarMetricPullback
          period hPeriod datum targetMetric)
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current) =
      programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
        period hPeriod datum
        (programPT06AmbientMatrixMetricVolumeCurrent targetMetric current) := by
  funext coordinate
  unfold programPT06AmbientMatrixMetricVolumeCurrent
    programPT06WarpedNullCollarTransitionVectorPullbackCurrent
    programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
    programPT06AmbientAbsoluteVectorPullback
  rw [programPT06WarpedNullCollarMetricPullback_volumeDensity
    period hPeriod datum targetMetric coordinate, map_smul, smul_smul]

/-- Metric divergence is natural for the metric that is actually pulled back
through the transition. -/
theorem programPT06WarpedNullCollarMetricPullback_divergence_natural
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (targetMetric : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent targetMetric current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06WarpedNullCollarMetricPullback
          period hPeriod datum targetMetric)
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence targetMetric current
        (programPT06WarpedNullHyperplaneEmbedding source) := by
  have hVolumeCurrent :=
    programPT06WarpedNullCollarMetricPullback_volumeCurrent
      period hPeriod datum targetMetric current
  have hJacobian : 0 <
      programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum :=
    programPT06WarpedNullCollarTransitionJacobianDensity_pos
      period hPeriod datum
  unfold programPT06AmbientMatrixMetricVolumeDivergence
  rw [hVolumeCurrent,
    programPT06WarpedNullCollarTransitionAbsolutePullback_divergence
      period hPeriod datum _ hCurrent,
    programPT06WarpedNullCollarMetricPullback_volumeDensity,
    datum.transition_face period hPeriod,
    ← programPT06WarpedNullCollarTransitionSignedJacobian_eq_fderiv
      period hPeriod datum,
    programPT06WarpedNullCollarTransitionSignedJacobian_abs
      period hPeriod datum,
    mul_div_mul_left _ _ (ne_of_gt hJacobian)]

/-- Metric divergence depends only on the metric-matrix germ at the evaluation
point. -/
theorem programPT06AmbientMatrixMetricVolumeDivergence_congr_metric
    {first second : ProgramPT06AmbientCoordinate4 →
      FiniteNullFaceAmbientMatrix4}
    {current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hMetrics : first =ᶠ[𝓝 coordinate] second) :
    programPT06AmbientMatrixMetricVolumeDivergence first current coordinate =
      programPT06AmbientMatrixMetricVolumeDivergence second current
        coordinate := by
  have hDensities :
      programPT06AmbientMatrixMetricVolumeDensity first =ᶠ[𝓝 coordinate]
        programPT06AmbientMatrixMetricVolumeDensity second :=
    hMetrics.mono fun nearby hNearby => by
      unfold programPT06AmbientMatrixMetricVolumeDensity
      rw [hNearby]
  have hVolumeCurrents :
      programPT06AmbientMatrixMetricVolumeCurrent first current =ᶠ[
        𝓝 coordinate]
        programPT06AmbientMatrixMetricVolumeCurrent second current :=
    hDensities.mono fun nearby hNearby => by
      unfold programPT06AmbientMatrixMetricVolumeCurrent
      rw [hNearby]
  unfold programPT06AmbientMatrixMetricVolumeDivergence
  rw [programPT06AmbientCoordinateDivergence_congr hVolumeCurrents,
    hDensities.eq_of_nhds]

/-- Pullback of the genuine physical metric coefficients from Gate 1054. -/
def programPT06WarpedNullCollarPhysicalPullbackMetric
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (physicalMetric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  programPT06WarpedNullCollarMetricPullback period hPeriod datum
    (programPT06EffectiveBulkChartPhysicalMetricMatrix
      period hPeriod physicalMetric incidence.chartAnchor)
    coordinate

/-- Gate 1054's stronger compatibility datum says precisely that the physical
pullback metric equals the fixed warped metric as a germ. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricGermDatum.physicalPullback_eventuallyEq_warped
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum) :
    programPT06WarpedNullCollarPhysicalPullbackMetric
        period hPeriod datum physical.physicalMetric =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
      programPT06WarpedNullHyperplaneAmbientMetric := by
  change (fun coordinate =>
      metricCongruence
        (programPT06WarpedNullCollarTransitionFDerivMatrix
          period hPeriod datum coordinate)
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor
          (datum.transition coordinate))) =ᶠ[
    𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
    programPT06WarpedNullHyperplaneAmbientMetric
  exact physical.pullback_metric_eventuallyEq

/-- Under the stronger germ datum, divergence for the induced physical collar
metric agrees with divergence for the fixed warped metric. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricGermDatum.physicalPullback_divergence_eq_warped
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum)
    (current : ProgramPT06AmbientCurrent4D) :
    programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric)
        current (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullMetricVolumeDivergence current
        (programPT06WarpedNullHyperplaneEmbedding source) := by
  rw [← programPT06AmbientMatrixMetricVolumeDivergence_warped]
  exact programPT06AmbientMatrixMetricVolumeDivergence_congr_metric
    (ProgramPT06WarpedNullCollarPhysicalMetricGermDatum.physicalPullback_eventuallyEq_warped
      period hPeriod physical)

/-- The physical pullback density has the expected absolute Jacobian
factor. -/
theorem programPT06WarpedNullCollarPhysicalPullbackMetric_volumeDensity
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (physicalMetric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientMatrixMetricVolumeDensity
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physicalMetric) coordinate =
      |LinearMap.det
          (fderiv Real datum.transition coordinate).toLinearMap| *
        programPT06AmbientMatrixMetricVolumeDensity
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physicalMetric incidence.chartAnchor)
          (datum.transition coordinate) :=
  programPT06WarpedNullCollarMetricPullback_volumeDensity
    period hPeriod datum _ coordinate

/-- Divergence naturality for a genuine physical metric and its actual collar
pullback. -/
theorem programPT06WarpedNullCollarPhysicalPullbackMetric_divergence_natural
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (physicalMetric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physicalMetric incidence.chartAnchor)
        current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physicalMetric)
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physicalMetric incidence.chartAnchor)
        current (programPT06WarpedNullHyperplaneEmbedding source) :=
  programPT06WarpedNullCollarMetricPullback_divergence_natural
    period hPeriod datum _ current hCurrent

/-- Weaker face datum: the physical pullback metric agrees with the explicit
warped null model only at the selected face point. -/
structure ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) where
  physicalMetric : SmoothGeneralLorentzMetric period hPeriod
  pullback_metric_face :
    programPT06WarpedNullCollarPhysicalPullbackMetric
        period hPeriod datum physicalMetric
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullHyperplaneAmbientMetric
        (programPT06WarpedNullHyperplaneEmbedding source)

/-- The weakened face datum is sufficient to match the physical pullback
volume with the explicit homogeneous screen area. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.volumeDensity_face_eq_screenArea
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    programPT06AmbientMatrixMetricVolumeDensity
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      finiteNullFaceHomogeneousScreenArea
        programPT06WarpedNullHyperplaneScreenMetric source.1 := by
  unfold programPT06AmbientMatrixMetricVolumeDensity
  rw [physical.pullback_metric_face]
  exact programPT06WarpedNullMetricVolumeDensity_face_eq_screenArea source

/-- The stronger Gate 1054 germ datum forgets to the weaker face datum. -/
def ProgramPT06WarpedNullCollarPhysicalMetricGermDatum.toPhysicalMetricFaceDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum) :
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum where
  physicalMetric := physical.physicalMetric
  pullback_metric_face := by
    change metricCongruence
        (programPT06WarpedNullCollarTransitionFDerivMatrix
          period hPeriod datum
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor
          (datum.transition
            (programPT06WarpedNullHyperplaneEmbedding source))) = _
    exact physical.pullback_metric_eventuallyEq.eq_of_nhds

/-- Physical pullback bundle: the coordinate transition stays in the valid
chart germ, metric volume transforms pointwise, and divergence is natural. -/
theorem programPT06WarpedNullCollarPhysicalMetricPullback_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (physicalMetric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physicalMetric incidence.chartAnchor)
        current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    (∀ᶠ coordinate in
        𝓝 (programPT06WarpedNullHyperplaneEmbedding source),
      programPT06AmbientCoverCoordinate (datum.transition coordinate) ∈
        (extChartAt coverModelWithCorners incidence.chartAnchor).target) ∧
      (∀ coordinate,
        programPT06AmbientMatrixMetricVolumeDensity
            (programPT06WarpedNullCollarPhysicalPullbackMetric
              period hPeriod datum physicalMetric) coordinate =
          |LinearMap.det
              (fderiv Real datum.transition coordinate).toLinearMap| *
            programPT06AmbientMatrixMetricVolumeDensity
              (programPT06EffectiveBulkChartPhysicalMetricMatrix
                period hPeriod physicalMetric incidence.chartAnchor)
              (datum.transition coordinate)) ∧
      programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06WarpedNullCollarPhysicalPullbackMetric
            period hPeriod datum physicalMetric)
          (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physicalMetric incidence.chartAnchor)
          current (programPT06WarpedNullHyperplaneEmbedding source) := by
  exact ⟨programPT06WarpedNullCollarTransition_eventually_mem_chartTarget
      period hPeriod datum,
    programPT06WarpedNullCollarPhysicalPullbackMetric_volumeDensity
      period hPeriod datum physicalMetric,
    programPT06WarpedNullCollarPhysicalPullbackMetric_divergence_natural
      period hPeriod datum physicalMetric current hCurrent⟩

end

end P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricPullback4D
end JanusFormal
