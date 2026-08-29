import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionDensityCovariance
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Frame-free relative Lorentz volume

For every smooth Lorentz metric, the local quotient
`sqrt |det g| / sqrt |det g₀|` is invariant under canonical holonomic chart
changes.  It therefore glues to a positive smooth scalar used to weight
the explicit finite nonzero intrinsic volume measure.  The resulting measure
is a volume relative to that fixed reference measure; no chartwise
Radon--Nikodym theorem or covariance under arbitrary diffeomorphisms is
claimed.

This is a static construction.  No topology on the space of metrics and no
Fréchet variation with respect to the metric are asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The positive coordinate volume factor of a smooth Lorentz metric. -/
def localMetricVolumeFactor
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  Real.sqrt
    |Matrix.det (localMetricMatrix period hPeriod metric patch coordinate)|

theorem localMetricVolumeFactor_pos
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    0 < localMetricVolumeFactor period hPeriod metric patch coordinate := by
  apply Real.sqrt_pos.2
  exact abs_pos.mpr
    (localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate)

theorem localMetricVolumeFactor_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMetricVolumeFactor period hPeriod metric patch coordinate ≠ 0 :=
  (localMetricVolumeFactor_pos period hPeriod metric patch coordinate).ne'

/-- The local determinant factor is exactly the existing metric-density
evaluation on the holonomic frame. -/
theorem localMetricVolumeFactor_eq_metricVolumeDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMetricVolumeFactor period hPeriod metric patch coordinate =
      metricVolumeDensity period hPeriod metric
        (patch.coordinateMap coordinate) (patch.frame coordinate) := by
  rfl

theorem localMetricDeterminant_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      Matrix.det
        (localMetricMatrix period hPeriod metric patch coordinate)) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro permutation _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro index _
  exact localMetricCoefficient_contDiff period hPeriod metric patch
    (permutation index) index

theorem localMetricVolumeFactor_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (localMetricVolumeFactor period hPeriod metric patch) := by
  have hDet :=
    localMetricDeterminant_contDiff period hPeriod metric patch
  exact
    (hDet.abs (fun coordinate =>
      localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate))
      |>.sqrt (fun coordinate =>
        abs_ne_zero.mpr
          (localMetricMatrix_det_ne_zero period hPeriod metric patch
            coordinate))

theorem localMetricVolumeFactor_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Continuous (localMetricVolumeFactor period hPeriod metric patch) := by
  exact
    (localMetricMatrix_contDiff period hPeriod metric patch).continuous
      |>.matrix_det.abs.sqrt

/-- Both local metric volumes acquire the same absolute transition
Jacobian. -/
theorem localMetricVolumeFactor_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localMetricVolumeFactor period hPeriod metric firstPatch firstCoordinate =
      |Matrix.det
        (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint)| *
        localMetricVolumeFactor period hPeriod metric secondPatch
          secondCoordinate := by
  rw [localMetricVolumeFactor,
    localMetricMatrix_transition_congruence period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint]
  simpa [metricCongruence, localMetricVolumeFactor] using
    metricVolume_diagonal_weight
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint)
      (localMetricMatrix period hPeriod metric secondPatch secondCoordinate)

/-- Relative determinant ratio against the intrinsic reference metric. -/
def localMetricVolumeRatio
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  localMetricVolumeFactor period hPeriod metric patch coordinate /
    localMetricVolumeFactor period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate

theorem localMetricVolumeRatio_pos
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    0 < localMetricVolumeRatio period hPeriod metric patch coordinate := by
  exact div_pos
    (localMetricVolumeFactor_pos period hPeriod metric patch coordinate)
    (localMetricVolumeFactor_pos period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

theorem localMetricVolumeRatio_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Continuous (localMetricVolumeRatio period hPeriod metric patch) := by
  exact
    (localMetricVolumeFactor_continuous period hPeriod metric patch).div
      (localMetricVolumeFactor_continuous period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
      (fun coordinate =>
        localMetricVolumeFactor_ne_zero period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

theorem localMetricVolumeRatio_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (localMetricVolumeRatio period hPeriod metric patch) := by
  exact
    (localMetricVolumeFactor_contDiff period hPeriod metric patch).div
      (localMetricVolumeFactor_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
      (fun coordinate =>
        localMetricVolumeFactor_ne_zero period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

/-- The local ratio is independent of the canonical holonomic
representative. -/
theorem localMetricVolumeRatio_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localMetricVolumeRatio period hPeriod metric firstPatch firstCoordinate =
      localMetricVolumeRatio period hPeriod metric secondPatch
        secondCoordinate := by
  let transition :=
    holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have hTransitionUnit : IsUnit transition :=
    holonomicCoordinateTransitionMatrixAt_isUnit period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  have hTransitionDet : Matrix.det transition ≠ 0 :=
    isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det transition).mp hTransitionUnit)
  have hJacobian : |Matrix.det transition| ≠ 0 :=
    abs_ne_zero.mpr hTransitionDet
  unfold localMetricVolumeRatio
  rw [
    localMetricVolumeFactor_transition period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint,
    localMetricVolumeFactor_transition period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint]
  field_simp [transition, hJacobian,
    localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) secondPatch
      secondCoordinate]

@[simp]
theorem localMetricVolumeRatio_intrinsic
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMetricVolumeRatio period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate =
      1 := by
  exact div_self
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

/-- A canonical holonomic representative of one quotient point. -/
structure MetricVolumeRatioChartWitness
    (point : EffectiveQuotient period hPeriod) where
  patch : SmoothHolonomicFrameChart4 period hPeriod
  coordinate : Vector4
  coordinateMap_eq : patch.coordinateMap coordinate = point

private theorem metricVolumeRatioChartWitness_nonempty
    (point : EffectiveQuotient period hPeriod) :
    Nonempty (MetricVolumeRatioChartWitness period hPeriod point) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  exact ⟨⟨patch, coordinate, hCoordinate⟩⟩

def selectedMetricVolumeRatioChart
    (point : EffectiveQuotient period hPeriod) :
    MetricVolumeRatioChartWitness period hPeriod point :=
  Classical.choice
    (metricVolumeRatioChartWitness_nonempty period hPeriod point)

/-- The chart-independent volume ratio of an arbitrary smooth Lorentz
metric. -/
def globalMetricVolumeRatio
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness := selectedMetricVolumeRatioChart period hPeriod point
  localMetricVolumeRatio period hPeriod metric witness.patch witness.coordinate

theorem globalMetricVolumeRatio_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalMetricVolumeRatio period hPeriod metric
        (patch.coordinateMap coordinate) =
      localMetricVolumeRatio period hPeriod metric patch coordinate := by
  let witness :=
    selectedMetricVolumeRatioChart period hPeriod
      (patch.coordinateMap coordinate)
  change
    localMetricVolumeRatio period hPeriod metric witness.patch
        witness.coordinate =
      localMetricVolumeRatio period hPeriod metric patch coordinate
  exact localMetricVolumeRatio_transition period hPeriod metric witness.patch
    patch witness.coordinate coordinate witness.coordinateMap_eq

theorem globalMetricVolumeRatio_pos
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 < globalMetricVolumeRatio period hPeriod metric point := by
  let witness := selectedMetricVolumeRatioChart period hPeriod point
  change 0 < localMetricVolumeRatio period hPeriod metric witness.patch
    witness.coordinate
  exact localMetricVolumeRatio_pos period hPeriod metric witness.patch
    witness.coordinate

/-- On every holonomic chart, the global ratio converts the intrinsic
reference determinant factor into the determinant factor of `metric`. -/
theorem globalMetricVolumeRatio_mul_intrinsic_density
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalMetricVolumeRatio period hPeriod metric
          (patch.coordinateMap coordinate) *
        metricVolumeDensity period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          (patch.coordinateMap coordinate) (patch.frame coordinate) =
      metricVolumeDensity period hPeriod metric
        (patch.coordinateMap coordinate) (patch.frame coordinate) := by
  rw [globalMetricVolumeRatio_eq_local,
    ← localMetricVolumeFactor_eq_metricVolumeDensity period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate,
    ← localMetricVolumeFactor_eq_metricVolumeDensity period hPeriod metric
      patch coordinate]
  exact div_mul_cancel₀ _
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

/-- The scalar gluing pattern gives a continuous global density. -/
theorem globalMetricVolumeRatio_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Continuous (globalMetricVolumeRatio period hPeriod metric) := by
  rw [continuous_iff_continuousAt]
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let hLocal := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hRepresentative :
      ContinuousAt
        (localMetricVolumeRatio period hPeriod metric patch ∘
          hLocal.localInverse)
        (patch.coordinateMap coordinate) :=
    (localMetricVolumeRatio_continuous period hPeriod metric patch).continuousAt
      |>.comp hLocal.localInverse_contMDiffAt.continuousAt
  apply hRepresentative.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
  have hRight :
      patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
    simpa only [Function.comp_apply, id_eq] using hNearby
  change
    globalMetricVolumeRatio period hPeriod metric nearby =
      localMetricVolumeRatio period hPeriod metric patch
        (hLocal.localInverse nearby)
  calc
    globalMetricVolumeRatio period hPeriod metric nearby =
        globalMetricVolumeRatio period hPeriod metric
          (patch.coordinateMap (hLocal.localInverse nearby)) :=
      congrArg (globalMetricVolumeRatio period hPeriod metric) hRight.symm
    _ = _ := globalMetricVolumeRatio_eq_local period hPeriod metric patch
      (hLocal.localInverse nearby)

/-- For a fixed metric, the global volume ratio is smooth on spacetime. -/
theorem globalMetricVolumeRatio_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (globalMetricVolumeRatio period hPeriod metric) := by
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let hLocal := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hRepresentative :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (localMetricVolumeRatio period hPeriod metric patch ∘
          hLocal.localInverse)
        (patch.coordinateMap coordinate) :=
    (localMetricVolumeRatio_contDiff period hPeriod metric patch).contMDiff
      |>.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hRepresentative.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
  have hRight :
      patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
    simpa only [Function.comp_apply, id_eq] using hNearby
  change
    globalMetricVolumeRatio period hPeriod metric nearby =
      localMetricVolumeRatio period hPeriod metric patch
        (hLocal.localInverse nearby)
  calc
    globalMetricVolumeRatio period hPeriod metric nearby =
        globalMetricVolumeRatio period hPeriod metric
          (patch.coordinateMap (hLocal.localInverse nearby)) :=
      congrArg (globalMetricVolumeRatio period hPeriod metric) hRight.symm
    _ = _ := globalMetricVolumeRatio_eq_local period hPeriod metric patch
      (hLocal.localInverse nearby)

/-- Smooth spacetime representative of the relative Lorentz-volume ratio. -/
def globalSmoothMetricVolumeRatio
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := globalMetricVolumeRatio period hPeriod metric
  contMDiff_toFun := globalMetricVolumeRatio_contMDiff period hPeriod metric

@[simp]
theorem globalMetricVolumeRatio_intrinsic
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) point = 1 := by
  let witness := selectedMetricVolumeRatioChart period hPeriod point
  change
    localMetricVolumeRatio period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) witness.patch
        witness.coordinate = 1
  exact localMetricVolumeRatio_intrinsic period hPeriod witness.patch
    witness.coordinate

/-- The metric volume is the intrinsic reference measure weighted by the
global determinant ratio. -/
def generalLorentzVolumeMeasure
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Measure (EffectiveQuotient period hPeriod) :=
  (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).withDensity
    (fun point =>
      ENNReal.ofReal (globalMetricVolumeRatio period hPeriod metric point))

theorem generalLorentzVolumeMeasure_isFinite
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    IsFiniteMeasure (generalLorentzVolumeMeasure period hPeriod metric) := by
  letI := intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  apply isFiniteMeasure_withDensity_ofReal
  have hContinuous :=
    globalMetricVolumeRatio_continuous period hPeriod metric
  have hSupport :
      HasCompactSupport (globalMetricVolumeRatio period hPeriod metric) :=
    HasCompactSupport.of_compactSpace _
  have hIntegrable :
      Integrable (globalMetricVolumeRatio period hPeriod metric)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    Continuous.integrable_of_hasCompactSupport hContinuous hSupport
  exact hIntegrable.hasFiniteIntegral

theorem generalLorentzVolumeMeasure_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    generalLorentzVolumeMeasure period hPeriod metric ≠ 0 := by
  let reference := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let density := fun point : EffectiveQuotient period hPeriod =>
    ENNReal.ofReal (globalMetricVolumeRatio period hPeriod metric point)
  have hDensityMeasurable' : Measurable density :=
    ENNReal.measurable_ofReal.comp
      (globalMetricVolumeRatio_continuous period hPeriod metric).measurable
  have hDensityMeasurable : AEMeasurable density reference :=
    hDensityMeasurable'.aemeasurable
  have hDensityNonzero : ∀ᵐ point ∂reference, density point ≠ 0 :=
    Filter.Eventually.of_forall fun point =>
      ENNReal.ofReal_ne_zero_iff.mpr
        (globalMetricVolumeRatio_pos period hPeriod metric point)
  have hAbsolutelyContinuous :
      reference ≪ reference.withDensity density :=
    withDensity_absolutelyContinuous' hDensityMeasurable hDensityNonzero
  change reference.withDensity density ≠ 0
  intro hZero
  rw [hZero] at hAbsolutelyContinuous
  exact intrinsicCanonicalLorentzVolumeMeasure_ne_zero period hPeriod
    (Measure.absolutelyContinuous_zero_iff.mp hAbsolutelyContinuous)

/-- The varying metric volume in the action-measure interface. -/
def generalLorentzActionMeasure
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    FiniteNonzeroActionMeasure period hPeriod where
  measure := generalLorentzVolumeMeasure period hPeriod metric
  finite := generalLorentzVolumeMeasure_isFinite period hPeriod metric
  nonzero := generalLorentzVolumeMeasure_ne_zero period hPeriod metric

/-- The construction recovers the canonical reference volume at the
intrinsic metric. -/
theorem generalLorentzVolumeMeasure_intrinsic :
    generalLorentzVolumeMeasure period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) =
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold generalLorentzVolumeMeasure
  rw [show
      (fun point : EffectiveQuotient period hPeriod =>
        ENNReal.ofReal
          (globalMetricVolumeRatio period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) point)) =
        1 by
      funext point
      simp]
  exact withDensity_one

/-- Integration against the relative metric volume is integration against
the fixed intrinsic measure with the global positive ratio inserted. -/
theorem integral_generalLorentzVolumeMeasure_eq_reference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (integrand : EffectiveQuotient period hPeriod → Real) :
    (∫ point, integrand point
        ∂generalLorentzVolumeMeasure period hPeriod metric) =
      ∫ point,
        globalMetricVolumeRatio period hPeriod metric point * integrand point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let density := fun point : EffectiveQuotient period hPeriod =>
    ENNReal.ofReal (globalMetricVolumeRatio period hPeriod metric point)
  have hDensityMeasurable : Measurable density :=
    ENNReal.measurable_ofReal.comp
      (globalMetricVolumeRatio_continuous period hPeriod metric).measurable
  have hDensityFinite : ∀ᵐ point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
      density point < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  change
    (∫ point, integrand point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod).withDensity
          density) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    hDensityMeasurable hDensityFinite]
  apply integral_congr_ae
  filter_upwards [] with point
  simp [density,
    ENNReal.toReal_ofReal
      (le_of_lt (globalMetricVolumeRatio_pos period hPeriod metric point))]

@[simp]
theorem generalLorentzActionMeasure_intrinsic_measure :
    (generalLorentzActionMeasure period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)).measure =
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
  generalLorentzVolumeMeasure_intrinsic period hPeriod

end

end P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
end JanusFormal
