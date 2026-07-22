import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D

/-!
# Unconditional smooth scalar density in physical bulk L2

Mathlib's smooth approximation theorem approximates every continuous real-valued
function on a sigma-compact real manifold by a smooth function with any
prescribed positive continuous pointwise error.  Apply it to the compact
effective mapping torus with the uniform error `1/(n+1)`.

The resulting smooth functions converge uniformly.  Continuity of the canonical
continuous-function-to-L2 map turns uniform convergence into physical L2
convergence.  Since continuous functions are already dense in L2, smooth
quotient scalar fields are dense unconditionally.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Uniform approximation radius. -/
def smoothApproximationRadius (index : Nat) : Real :=
  1 / (index + 1 : Real)

/-- The approximation radius is positive. -/
theorem smoothApproximationRadius_pos (index : Nat) :
    0 < smoothApproximationRadius index := by
  unfold smoothApproximationRadius
  positivity

/-- Existence of one smooth uniform approximation. -/
theorem exists_smoothApproximation
    (continuousField : C(EffectiveQuotient period hPeriod, Real))
    (index : Nat) :
    ∃ smoothField : SmoothQuotientField period hPeriod Real,
      ∀ point,
        dist (continuousField point) (smoothField point) <
          smoothApproximationRadius index := by
  obtain ⟨approximation, hApproximation⟩ :=
    continuousField.continuous.exists_contMDiff_approx
      coverModelWithCorners ∞
      (continuous_const : Continuous
        (fun _ : EffectiveQuotient period hPeriod =>
          smoothApproximationRadius index))
      (fun _ => smoothApproximationRadius_pos index)
  exact ⟨{
    toFun := approximation
    contMDiff_toFun := approximation.contMDiff }, hApproximation⟩

/-- Chosen smooth approximation. -/
def smoothApproximation
    (continuousField : C(EffectiveQuotient period hPeriod, Real))
    (index : Nat) : SmoothQuotientField period hPeriod Real :=
  Classical.choose
    (exists_smoothApproximation period hPeriod continuousField index)

/-- Pointwise approximation estimate. -/
theorem smoothApproximation_spec
    (continuousField : C(EffectiveQuotient period hPeriod, Real))
    (index : Nat) (point : EffectiveQuotient period hPeriod) :
    dist (continuousField point)
        (smoothApproximation period hPeriod continuousField index point) <
      smoothApproximationRadius index :=
  Classical.choose_spec
    (exists_smoothApproximation period hPeriod continuousField index) point

/-- Continuous-map form of the chosen smooth approximation. -/
def smoothApproximationContinuousMap
    (continuousField : C(EffectiveQuotient period hPeriod, Real))
    (index : Nat) : C(EffectiveQuotient period hPeriod, Real) :=
  ⟨smoothApproximation period hPeriod continuousField index,
    (smoothApproximation period hPeriod continuousField index)
      |>.contMDiff_toFun.continuous⟩

/-- Uniform distance estimate. -/
theorem smoothApproximationContinuousMap_dist_le
    (continuousField : C(EffectiveQuotient period hPeriod, Real))
    (index : Nat) :
    dist (smoothApproximationContinuousMap
        period hPeriod continuousField index) continuousField ≤
      smoothApproximationRadius index := by
  apply (ContinuousMap.dist_le
    (smoothApproximationRadius_pos index).le).2
  intro point
  exact le_of_lt
    (smoothApproximation_spec period hPeriod continuousField index point)

/-- Uniform convergence of the smooth approximants. -/
theorem smoothApproximationContinuousMap_tendsto
    (continuousField : C(EffectiveQuotient period hPeriod, Real)) :
    Tendsto
      (smoothApproximationContinuousMap period hPeriod continuousField)
      atTop (𝓝 continuousField) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (Filter.Eventually.of_forall fun index =>
      smoothApproximationContinuousMap_dist_le
        period hPeriod continuousField index)
  simpa [smoothApproximationRadius] using
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The continuous and smooth L2 realizations of one approximant agree. -/
theorem continuousToBulkL2_smoothApproximation
    (continuousField : C(EffectiveQuotient period hPeriod, Real))
    (index : Nat) :
    continuousToCanonicalPhysicalBulkL2 period hPeriod
        (smoothApproximationContinuousMap
          period hPeriod continuousField index) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (smoothApproximation period hPeriod continuousField index) := by
  apply Lp.ext
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal))
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (𝕜 := Real)
      (smoothApproximationContinuousMap
        period hPeriod continuousField index),
     smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (smoothApproximation period hPeriod continuousField index)]
    with point hContinuous hSmooth
  rw [hContinuous, hSmooth]
  rfl

/-- Physical L2 convergence of the chosen smooth approximants. -/
theorem smoothApproximation_tendsto_l2
    (continuousField : C(EffectiveQuotient period hPeriod, Real)) :
    Tendsto
      (fun index => smoothToCanonicalPhysicalBulkL2 period hPeriod
        (smoothApproximation period hPeriod continuousField index))
      atTop
      (𝓝 (continuousToCanonicalPhysicalBulkL2
        period hPeriod continuousField)) := by
  have hContinuous : Tendsto
      (fun index => continuousToCanonicalPhysicalBulkL2 period hPeriod
        (smoothApproximationContinuousMap
          period hPeriod continuousField index))
      atTop
      (𝓝 (continuousToCanonicalPhysicalBulkL2
        period hPeriod continuousField)) :=
    (continuousToCanonicalPhysicalBulkL2 period hPeriod).continuous.continuousAt
      |>.tendsto.comp
        (smoothApproximationContinuousMap_tendsto
          period hPeriod continuousField)
  exact hContinuous.congr'
    (Filter.Eventually.of_forall fun index =>
      (continuousToBulkL2_smoothApproximation
        period hPeriod continuousField index).symm)

/-- Unconditional continuous-to-smooth physical approximation package. -/
def canonicalPhysicalScalarContinuousSmoothApproximationData :
    CanonicalPhysicalScalarContinuousSmoothApproximationData
      period hPeriod where
  approximation := smoothApproximation period hPeriod
  tendsto_l2 := smoothApproximation_tendsto_l2 period hPeriod

/-- Smooth quotient scalar fields are dense in physical bulk L2. -/
theorem smoothToCanonicalPhysicalBulkL2_denseRange :
    DenseRange (smoothToCanonicalPhysicalBulkL2 period hPeriod) :=
  (canonicalPhysicalScalarContinuousSmoothApproximationData period hPeriod)
    |>.smoothToCanonicalPhysicalBulkL2_denseRange

/-- Unconditional smooth-density certificate. -/
theorem certificate :
    DenseRange (smoothToCanonicalPhysicalBulkL2 period hPeriod) ∧
      (∀ continuousField : C(EffectiveQuotient period hPeriod, Real),
        Tendsto
          (fun index => smoothToCanonicalPhysicalBulkL2 period hPeriod
            (smoothApproximation period hPeriod continuousField index))
          atTop
          (𝓝 (continuousToCanonicalPhysicalBulkL2
            period hPeriod continuousField))) :=
  ⟨smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod,
    smoothApproximation_tendsto_l2 period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
end JanusFormal
