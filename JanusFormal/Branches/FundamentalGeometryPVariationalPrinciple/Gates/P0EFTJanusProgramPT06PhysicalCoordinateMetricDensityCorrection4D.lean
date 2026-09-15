import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D

/-!
# Physical-coordinate metric and density correction

A physical partial diffeomorphism turns every smooth Lorentz metric into its
coordinate Gram matrix on the chart target.  Its metric density is positive
there.  Rescaling a coordinate current by the ratio of the warped and physical
densities makes the two densitized currents, and hence their coordinate
divergences, agree locally.  No metric isometry or null-face hypothesis is
used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06WarpedNullMetricVolumeFiberStokes4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06WarpedNullCoordinateIncidence4D
open P0EFTJanusProgramPT06CanonicalFirstSheetGlobalStripCoordinate4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A smooth physical coordinate with four ambient real coordinates. -/
abbrev ProgramPT06PhysicalCoordinateChart :=
  PartialDiffeomorph coverModelWithCorners
    (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    (ProgramPT06EffectiveBulk period hPeriod)
    ProgramPT06AmbientCoordinate4 ∞

/-- Coordinate basis transported through the inverse physical chart. -/
def programPT06PhysicalCoordinateTangentFrame
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    Fin 4 → TangentSpace coverModelWithCorners (chart.symm coordinate) :=
  fun index =>
    mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners chart.symm coordinate
      (programPT06AmbientCoordinateBasis index)

/-- A genuine physical Lorentz metric in the inverse-chart derivative
frame. -/
def programPT06PhysicalCoordinateMetricMatrix
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  metricGramMatrix period hPeriod metric (chart.symm coordinate)
    (programPT06PhysicalCoordinateTangentFrame
      period hPeriod chart coordinate)

@[simp] theorem programPT06PhysicalCoordinateMetricMatrix_apply
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (first second : Fin 4) :
    programPT06PhysicalCoordinateMetricMatrix period hPeriod chart metric
        coordinate first second =
      metric.tensor.tensor (chart.symm coordinate)
        (programPT06PhysicalCoordinateTangentFrame
          period hPeriod chart coordinate first)
        (programPT06PhysicalCoordinateTangentFrame
          period hPeriod chart coordinate second) := by
  rfl

private def programPT06PhysicalCoordinateTangentBasis
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners (chart.symm coordinate)) :=
  programPT06AmbientCoordinateBasis.map
    ((PartialDiffeomorph.isLocalDiffeomorphAt
      (I := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (J := coverModelWithCorners)
      (M := ProgramPT06AmbientCoordinate4)
      (N := ProgramPT06EffectiveBulk period hPeriod)
      (n := ∞) chart.symm hCoordinate).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv

private theorem programPT06PhysicalCoordinateTangentBasis_apply
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target)
    (index : Fin 4) :
    programPT06PhysicalCoordinateTangentBasis period hPeriod chart coordinate
        hCoordinate index =
      programPT06PhysicalCoordinateTangentFrame
        period hPeriod chart coordinate index := by
  let hLocal := PartialDiffeomorph.isLocalDiffeomorphAt
    (I := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    (J := coverModelWithCorners)
    (M := ProgramPT06AmbientCoordinate4)
    (N := ProgramPT06EffectiveBulk period hPeriod)
    (n := ∞) chart.symm hCoordinate
  unfold programPT06PhysicalCoordinateTangentBasis
    programPT06PhysicalCoordinateTangentFrame
  rw [Module.Basis.map_apply]
  rw [← hLocal.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact congrFun
    (ContinuousLinearEquiv.coe_toLinearEquiv
      (hLocal.mfderivToContinuousLinearEquiv (by simp)))
    (programPT06AmbientCoordinateBasis index)

private def programPT06PhysicalCoordinateMetricBilinForm
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    LinearMap.BilinForm Real
      (TangentSpace coverModelWithCorners (chart.symm coordinate)) :=
  (metric.tensor.tensor (chart.symm coordinate)).toBilinForm

private theorem programPT06PhysicalCoordinateMetricBilinForm_nondegenerate
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    (programPT06PhysicalCoordinateMetricBilinForm
      period hPeriod chart metric coordinate).Nondegenerate := by
  constructor
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric
    apply ContinuousLinearMap.ext
    intro second
    simpa [programPT06PhysicalCoordinateMetricBilinForm] using hVector second
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric
    apply ContinuousLinearMap.ext
    intro second
    rw [metric.tensor.symmetric]
    simpa [programPT06PhysicalCoordinateMetricBilinForm] using hVector second

/-- The physical coordinate metric is nonsingular on the chart target. -/
theorem programPT06PhysicalCoordinateMetricMatrix_det_ne_zero
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    Matrix.det
      (programPT06PhysicalCoordinateMetricMatrix
        period hPeriod chart metric coordinate) ≠ 0 := by
  let basis := programPT06PhysicalCoordinateTangentBasis
    period hPeriod chart coordinate hCoordinate
  have hDet :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero basis).mp
      (programPT06PhysicalCoordinateMetricBilinForm_nondegenerate
        period hPeriod chart metric coordinate)
  have hMatrix :
      programPT06PhysicalCoordinateMetricMatrix
          period hPeriod chart metric coordinate =
        LinearMap.BilinForm.toMatrix basis
          (programPT06PhysicalCoordinateMetricBilinForm
            period hPeriod chart metric coordinate) := by
    ext first second
    simp [basis, programPT06PhysicalCoordinateMetricMatrix,
      metricGramMatrix, programPT06PhysicalCoordinateMetricBilinForm,
      programPT06PhysicalCoordinateTangentBasis_apply]
  rw [hMatrix]
  exact hDet

/-- The physical coordinate metric-volume density is positive on the chart
target. -/
theorem programPT06PhysicalCoordinateMetricVolumeDensity_pos
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    0 < programPT06AmbientMatrixMetricVolumeDensity
      (programPT06PhysicalCoordinateMetricMatrix
        period hPeriod chart metric) coordinate := by
  unfold programPT06AmbientMatrixMetricVolumeDensity
  exact Real.sqrt_pos.2 (abs_pos.mpr
    (programPT06PhysicalCoordinateMetricMatrix_det_ne_zero
      period hPeriod chart metric coordinate hCoordinate))

/-- Ratio that converts a coordinate current to the same densitized current
as in the explicit warped metric. -/
def programPT06PhysicalCoordinateMetricDensityRatio
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) : Real :=
  programPT06WarpedNullAmbientMetricVolumeDensity coordinate /
    programPT06AmbientMatrixMetricVolumeDensity
      (programPT06PhysicalCoordinateMetricMatrix
        period hPeriod chart metric) coordinate

/-- Current corrected by the warped-to-physical metric-density ratio. -/
def programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D) :
    ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    programPT06PhysicalCoordinateMetricDensityRatio
        period hPeriod chart metric coordinate •
      current coordinate

/-- The corrected current has exactly the warped densitized current wherever
the physical coordinate is valid. -/
theorem programPT06PhysicalCoordinateMetricDensityCorrected_volumeCurrent
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod chart metric)
        (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
          period hPeriod chart metric current) coordinate =
      programPT06AmbientMatrixMetricVolumeCurrent
        programPT06WarpedNullHyperplaneAmbientMetric current coordinate := by
  have hDensity : programPT06AmbientMatrixMetricVolumeDensity
      (programPT06PhysicalCoordinateMetricMatrix
        period hPeriod chart metric) coordinate ≠ 0 :=
    ne_of_gt (programPT06PhysicalCoordinateMetricVolumeDensity_pos
      period hPeriod chart metric coordinate hCoordinate)
  unfold programPT06AmbientMatrixMetricVolumeCurrent
    programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
    programPT06PhysicalCoordinateMetricDensityRatio
  rw [smul_smul]
  congr 1
  rw [programPT06AmbientMatrixMetricVolumeDensity_warped]
  field_simp

/-- The corrected physical and warped densitized currents agree on a
neighborhood of every point of the chart target. -/
theorem programPT06PhysicalCoordinateMetricDensityCorrected_volumeCurrent_eventuallyEq
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod chart metric)
        (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
          period hPeriod chart metric current) =ᶠ[𝓝 coordinate]
      programPT06AmbientMatrixMetricVolumeCurrent
        programPT06WarpedNullHyperplaneAmbientMetric current := by
  filter_upwards [chart.open_target.mem_nhds hCoordinate] with nearby hNearby
  exact programPT06PhysicalCoordinateMetricDensityCorrected_volumeCurrent
    period hPeriod chart metric current nearby hNearby

/-- The physical corrected and warped coordinate divergences of the
densitized currents agree. -/
theorem programPT06PhysicalCoordinateMetricDensityCorrected_coordinateDivergence
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    programPT06AmbientCoordinateDivergence
        (programPT06AmbientMatrixMetricVolumeCurrent
          (programPT06PhysicalCoordinateMetricMatrix
            period hPeriod chart metric)
          (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
            period hPeriod chart metric current)) coordinate =
      programPT06AmbientCoordinateDivergence
        (programPT06AmbientMatrixMetricVolumeCurrent
          programPT06WarpedNullHyperplaneAmbientMetric current) coordinate :=
  programPT06AmbientCoordinateDivergence_congr
    (programPT06PhysicalCoordinateMetricDensityCorrected_volumeCurrent_eventuallyEq
      period hPeriod chart metric current coordinate hCoordinate)

/-- Metric volume times physical divergence equals the common densitized
coordinate divergence. -/
theorem programPT06PhysicalCoordinateMetricDensityCorrected_densitizedDivergence
    (chart : ProgramPT06PhysicalCoordinateChart period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈ chart.target) :
    programPT06AmbientMatrixMetricVolumeDensity
          (programPT06PhysicalCoordinateMetricMatrix
            period hPeriod chart metric) coordinate *
        programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06PhysicalCoordinateMetricMatrix
            period hPeriod chart metric)
          (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
            period hPeriod chart metric current) coordinate =
      programPT06AmbientCoordinateDivergence
        (programPT06AmbientMatrixMetricVolumeCurrent
          programPT06WarpedNullHyperplaneAmbientMetric current) coordinate := by
  have hDensity : programPT06AmbientMatrixMetricVolumeDensity
      (programPT06PhysicalCoordinateMetricMatrix
        period hPeriod chart metric) coordinate ≠ 0 :=
    ne_of_gt (programPT06PhysicalCoordinateMetricVolumeDensity_pos
      period hPeriod chart metric coordinate hCoordinate)
  unfold programPT06AmbientMatrixMetricVolumeDivergence
  rw [programPT06PhysicalCoordinateMetricDensityCorrected_coordinateDivergence
    period hPeriod chart metric current coordinate hCoordinate]
  field_simp

/-- Gate 1064 supplies target validity for the corrected current on its
selected face. -/
theorem programPT06PhysicalCoordinateMetricDensityCorrected_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullCoordinateIncidenceDatum
      period hPeriod input)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod incidence.coordinateChart metric)
        (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
          period hPeriod incidence.coordinateChart metric current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeCurrent
        programPT06WarpedNullHyperplaneAmbientMetric current
        (programPT06WarpedNullHyperplaneEmbedding source) := by
  exact programPT06PhysicalCoordinateMetricDensityCorrected_volumeCurrent
    period hPeriod incidence.coordinateChart metric current
    (programPT06WarpedNullHyperplaneEmbedding source)
    (programPT06WarpedNullCoordinateWarpedFace_mem_chartTarget
      period hPeriod incidence source hSource)

/-- Gate 1065 supplies target validity on the whole canonical finite collar. -/
theorem programPT06CanonicalFirstSheetPhysicalCoordinateMetricDensityCorrected_fullCollar
    (pole : StandardEquatorialTwoSphere)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval)
    (hTime : source.1 ∈ canonicalLorentzInteriorTime period) :
    programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06PhysicalCoordinateMetricMatrix period hPeriod
          (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
            period hPeriod pole) metric)
        (programPT06PhysicalCoordinateMetricDensityCorrectedCurrent
          period hPeriod
          (programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
            period hPeriod pole) metric current)
        (programPT06WarpedNullClosedHalfCollarEmbedding (source, normal)) =
      programPT06AmbientMatrixMetricVolumeCurrent
        programPT06WarpedNullHyperplaneAmbientMetric current
        (programPT06WarpedNullClosedHalfCollarEmbedding (source, normal)) := by
  let chart :=
    programPT06CanonicalFirstSheetGlobalStripCoordinatePartialDiffeomorph
      period hPeriod pole
  let physicalPoint :=
    cutBulkFiniteCollarToAmbient period hPeriod
      (programPT06CanonicalFirstSheetBoundaryMap
        period hPeriod pole source, normal)
  have hPhysical : physicalPoint ∈ chart.source := by
    exact programPT06CanonicalFirstSheetFullCollar_mem_globalStripCoordinate
      period hPeriod pole source normal hTime
  have hCoordinate :
      programPT06WarpedNullClosedHalfCollarEmbedding (source, normal) ∈
        chart.target := by
    rw [← programPT06CanonicalFirstSheetGlobalStripCoordinate_fullCollar
      period hPeriod pole source normal hTime]
    exact chart.map_source hPhysical
  exact programPT06PhysicalCoordinateMetricDensityCorrected_volumeCurrent
    period hPeriod chart metric current
    (programPT06WarpedNullClosedHalfCollarEmbedding (source, normal))
    hCoordinate

end
end P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D
end JanusFormal
