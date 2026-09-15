import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# Physical mapping-torus metric on the warped-null collar germ

Gate 1053 accepts an abstract target matrix field.  This gate constructs that
field by evaluating a genuine smooth Lorentz metric on the derivative frame
of the inverse of the incidence chart.  The inverse chart sends the warped
face coordinate back to the selected true mapping-torus boundary point.

Compatibility of this physical metric with the warped model remains an
explicit germ hypothesis.  Under it, Gate 1053 gives metric-divergence
naturality for the actual metric coefficients in the incidence chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricVolumeCovariance4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Convert the fixed ambient Euclidean coordinates to the model coordinates
used by the extended mapping-torus chart. -/
def programPT06AmbientCoverCoordinate
    (coordinate : ProgramPT06AmbientCoordinate4) : CoverCoordinates :=
  holonomicCoordinateEquiv.symm
    (programPT06AmbientHolonomicEquiv coordinate)

theorem continuous_programPT06AmbientCoverCoordinate :
    Continuous programPT06AmbientCoverCoordinate :=
  holonomicCoordinateEquiv.symm.continuous.comp
    programPT06AmbientHolonomicEquiv.continuous

/-- Total representative of the inverse incidence chart.  Its geometric
meaning is used only on the target of the extended chart. -/
def programPT06EffectiveBulkChartPoint
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    ProgramPT06EffectiveBulk period hPeriod :=
  (extChartAt coverModelWithCorners anchor).symm
    (programPT06AmbientCoverCoordinate coordinate)

/-- On the chart source, the inverse coordinate representative recovers the
original mapping-torus point. -/
theorem programPT06EffectiveBulkChartPoint_coordinate
    (anchor point : ProgramPT06EffectiveBulk period hPeriod)
    (hPoint : point ∈ (extChartAt coverModelWithCorners anchor).source) :
    programPT06EffectiveBulkChartPoint period hPeriod anchor
        (programPT06EffectiveBulkChartCoordinate
          period hPeriod anchor point) =
      point := by
  unfold programPT06EffectiveBulkChartPoint
    programPT06AmbientCoverCoordinate
    programPT06EffectiveBulkChartCoordinate
  simp only [ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  exact (extChartAt coverModelWithCorners anchor).left_inv hPoint

/-- The selected true boundary point lies in the incidence chart. -/
theorem programPT06WarpedNullTrueBoundaryPoint_mem_chart
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06WarpedNullTrueBoundaryPoint
        period hPeriod incidence source ∈
      (chartAt CoverModel incidence.chartAnchor).source := by
  have hChart := incidence.collar_image_mem_chart source hSource
    (⊥ : CutCollarInterval)
  change cutThroatBoundaryToBulk period hPeriod
      (incidence.boundaryMap source) ∈
    (chartAt CoverModel incidence.chartAnchor).source
  rw [← cutBulkToAmbient_cutBoundaryInclusion,
    ← cutCollarAttachment_cutThroatFace]
  simpa only [cutBulkFiniteCollarToAmbient, cutThroatFace] using hChart

/-- The inverse incidence chart sends the warped face coordinate to the
actual selected boundary point. -/
theorem programPT06EffectiveBulkChartPoint_warpedFace
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06EffectiveBulkChartPoint period hPeriod incidence.chartAnchor
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullTrueBoundaryPoint
        period hPeriod incidence source := by
  rw [← programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
    period hPeriod incidence source hSource]
  exact programPT06EffectiveBulkChartPoint_coordinate
    period hPeriod incidence.chartAnchor
    (programPT06WarpedNullTrueBoundaryPoint
      period hPeriod incidence source)
    (by
      simpa only [extChartAt_source] using
    (programPT06WarpedNullTrueBoundaryPoint_mem_chart
          period hPeriod incidence source hSource))

/-- Gate 1048's transition remains in the valid target of the inverse
incidence chart throughout a neighborhood of the selected face point. -/
theorem programPT06WarpedNullCollarTransition_eventually_mem_chartTarget
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ∀ᶠ coordinate in
        𝓝 (programPT06WarpedNullHyperplaneEmbedding source),
      programPT06AmbientCoverCoordinate (datum.transition coordinate) ∈
        (extChartAt coverModelWithCorners incidence.chartAnchor).target := by
  let faceCoordinate := programPT06WarpedNullHyperplaneEmbedding source
  have hFaceSource :
      programPT06WarpedNullTrueBoundaryPoint
          period hPeriod incidence source ∈
        (extChartAt coverModelWithCorners incidence.chartAnchor).source := by
    simpa only [extChartAt_source] using
      (programPT06WarpedNullTrueBoundaryPoint_mem_chart
        period hPeriod incidence source hSource)
  have hFaceTarget :
      programPT06AmbientCoverCoordinate faceCoordinate ∈
        (extChartAt coverModelWithCorners incidence.chartAnchor).target := by
    rw [show faceCoordinate =
        programPT06EffectiveBulkChartCoordinate period hPeriod
          incidence.chartAnchor
          (programPT06WarpedNullTrueBoundaryPoint
            period hPeriod incidence source) by
      exact (programPT06WarpedNullTrueBoundaryPoint_chartCoordinate
        period hPeriod incidence source hSource).symm]
    unfold programPT06AmbientCoverCoordinate
      programPT06EffectiveBulkChartCoordinate
    simp only [ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt coverModelWithCorners incidence.chartAnchor).map_source
      hFaceSource
  have hTransition : ContinuousAt datum.transition faceCoordinate :=
    datum.transition_isLocalDiffeomorphAt.contMDiffAt.continuousAt
  have hComposition : ContinuousAt
      (fun coordinate =>
        programPT06AmbientCoverCoordinate (datum.transition coordinate))
      faceCoordinate :=
    continuous_programPT06AmbientCoverCoordinate.continuousAt.comp hTransition
  have hAtTransition :
      programPT06AmbientCoverCoordinate
          (datum.transition faceCoordinate) ∈
        (extChartAt coverModelWithCorners incidence.chartAnchor).target := by
    rw [show datum.transition faceCoordinate = faceCoordinate by
      exact datum.transition_face period hPeriod]
    exact hFaceTarget
  exact hComposition
    ((isOpen_extChartAt_target incidence.chartAnchor).mem_nhds hAtTransition)

/-- Coordinate derivative frame of the inverse incidence chart. -/
def programPT06EffectiveBulkChartTangentFrame
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    Fin 4 → TangentSpace coverModelWithCorners
      (programPT06EffectiveBulkChartPoint
        period hPeriod anchor coordinate) :=
  fun index =>
    mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners
      (programPT06EffectiveBulkChartPoint period hPeriod anchor)
      coordinate (programPT06AmbientCoordinateBasis index)

/-- Matrix of a genuine smooth Lorentz metric in the inverse incidence-chart
derivative frame. -/
def programPT06EffectiveBulkChartPhysicalMetricMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  metricGramMatrix period hPeriod metric
    (programPT06EffectiveBulkChartPoint period hPeriod anchor coordinate)
    (programPT06EffectiveBulkChartTangentFrame
      period hPeriod anchor coordinate)

@[simp] theorem programPT06EffectiveBulkChartPhysicalMetricMatrix_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (first second : Fin 4) :
    programPT06EffectiveBulkChartPhysicalMetricMatrix
        period hPeriod metric anchor coordinate first second =
      metric.tensor.tensor
        (programPT06EffectiveBulkChartPoint
          period hPeriod anchor coordinate)
        (programPT06EffectiveBulkChartTangentFrame
          period hPeriod anchor coordinate first)
        (programPT06EffectiveBulkChartTangentFrame
          period hPeriod anchor coordinate second) := by
  rfl

/-- A genuine mapping-torus Lorentz metric whose incidence-chart
coefficients pull back to the warped metric throughout the transition germ. -/
structure ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) where
  physicalMetric : SmoothGeneralLorentzMetric period hPeriod
  pullback_metric_eventuallyEq :
    (fun coordinate =>
      metricCongruence
        (programPT06WarpedNullCollarTransitionFDerivMatrix
          period hPeriod datum coordinate)
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physicalMetric incidence.chartAnchor
          (datum.transition coordinate))) =ᶠ[
      𝓝 (programPT06WarpedNullHyperplaneEmbedding source)]
      programPT06WarpedNullHyperplaneAmbientMetric

/-- Forget the physical origin of the target matrices and recover Gate
1053's metric-germ datum. -/
def ProgramPT06WarpedNullCollarPhysicalMetricGermDatum.toMetricGermDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum) :
    ProgramPT06WarpedNullCollarMetricGermDatum period hPeriod datum where
  targetMetric := programPT06EffectiveBulkChartPhysicalMetricMatrix
    period hPeriod physical.physicalMetric incidence.chartAnchor
  pullback_metric_eventuallyEq := physical.pullback_metric_eventuallyEq

/-- Gate 1053's pointwise compatibility now concerns actual coefficient
matrices of the supplied smooth mapping-torus metric. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricGermDatum.metric_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricGermDatum
      period hPeriod datum) :
    metricCongruence
        (programPT06WarpedNullCollarTransitionJacobianMatrix
          period hPeriod datum)
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor
          (programPT06WarpedNullHyperplaneEmbedding source)) =
      programPT06WarpedNullHyperplaneAmbientMetric
        (programPT06WarpedNullHyperplaneEmbedding source) :=
  physical.toMetricGermDatum.metric_face period hPeriod

/-- Metric-divergence naturality for the supplied physical metric in the
incidence chart. -/
theorem programPT06WarpedNullCollarPhysicalMetricDivergence_natural
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
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor)
        current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06WarpedNullMetricVolumeDivergence
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor)
        current (programPT06WarpedNullHyperplaneEmbedding source) :=
  programPT06WarpedNullCollarMetricDivergence_natural
    period hPeriod physical.toMetricGermDatum current hCurrent

/-- Physical metric-germ bridge bundle. -/
theorem programPT06WarpedNullCollarPhysicalMetricGerm_bundle
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
    (hCurrent : DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod physical.physicalMetric incidence.chartAnchor)
        current)
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06EffectiveBulkChartPoint period hPeriod incidence.chartAnchor
        (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06WarpedNullTrueBoundaryPoint
          period hPeriod incidence source ∧
      (∀ᶠ coordinate in
          𝓝 (programPT06WarpedNullHyperplaneEmbedding source),
        programPT06AmbientCoverCoordinate (datum.transition coordinate) ∈
          (extChartAt coverModelWithCorners incidence.chartAnchor).target) ∧
      metricCongruence
          (programPT06WarpedNullCollarTransitionJacobianMatrix
            period hPeriod datum)
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physical.physicalMetric incidence.chartAnchor
            (programPT06WarpedNullHyperplaneEmbedding source)) =
        programPT06WarpedNullHyperplaneAmbientMetric
          (programPT06WarpedNullHyperplaneEmbedding source) ∧
      programPT06WarpedNullMetricVolumeDivergence
          (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod physical.physicalMetric incidence.chartAnchor)
          current (programPT06WarpedNullHyperplaneEmbedding source) := by
  exact ⟨programPT06EffectiveBulkChartPoint_warpedFace
      period hPeriod incidence source hSource,
    programPT06WarpedNullCollarTransition_eventually_mem_chartTarget
      period hPeriod datum,
    physical.metric_face period hPeriod,
    programPT06WarpedNullCollarPhysicalMetricDivergence_natural
      period hPeriod physical current hCurrent⟩

end

end P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D
end JanusFormal
