import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

/-!
# Smooth scalar density in physical bulk `L²`

Continuous real functions are dense in `L²` for the finite Borel measure on the
compact effective quotient.  Therefore it remains only to approximate each
continuous function in `L²` by smooth quotient scalar fields.

This file proves that any such continuous-to-smooth approximation scheme makes
the canonical smooth physical bulk inclusion dense.  It isolates the manifold
smoothing theorem from all later boundary and operator arguments.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D

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

/-- Continuous functions included in physical bulk `L²`. -/
def continuousToCanonicalPhysicalBulkL2 :
    C(EffectiveQuotient period hPeriod, Real) →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  ContinuousMap.toLp (2 : ENNReal)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) Real

/-- Continuous functions are dense in physical bulk `L²`. -/
theorem continuousToCanonicalPhysicalBulkL2_denseRange :
    DenseRange (continuousToCanonicalPhysicalBulkL2 period hPeriod) := by
  exact ContinuousMap.toLp_denseRange Real
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) Real
    (by norm_num : (2 : ENNReal) ≠ ∞)

/-- An `L²` smoothing scheme from continuous functions to smooth quotient
scalars. -/
structure CanonicalPhysicalScalarContinuousSmoothApproximationData where
  approximation : C(EffectiveQuotient period hPeriod, Real) →
    Nat → SmoothQuotientField period hPeriod Real
  tendsto_l2 : ∀ continuousField,
    Tendsto
      (fun index => smoothToCanonicalPhysicalBulkL2 period hPeriod
        (approximation continuousField index))
      atTop
      (𝓝 (continuousToCanonicalPhysicalBulkL2
        period hPeriod continuousField))

namespace CanonicalPhysicalScalarContinuousSmoothApproximationData

/-- Every continuous `L²` vector lies in the closure of the smooth physical
range. -/
theorem continuous_mem_closure_smoothRange
    (approximationData :
      CanonicalPhysicalScalarContinuousSmoothApproximationData
        period hPeriod)
    (continuousField : C(EffectiveQuotient period hPeriod, Real)) :
    continuousToCanonicalPhysicalBulkL2 period hPeriod continuousField ∈
      closure (Set.range
        (smoothToCanonicalPhysicalBulkL2 period hPeriod)) := by
  apply mem_closure_of_tendsto
    (approximationData.tendsto_l2 continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨approximationData.approximation continuousField index, rfl⟩

/-- Continuous physical range is contained in the closure of the smooth range. -/
theorem continuousRange_subset_closure_smoothRange
    (approximationData :
      CanonicalPhysicalScalarContinuousSmoothApproximationData
        period hPeriod) :
    Set.range (continuousToCanonicalPhysicalBulkL2 period hPeriod) ⊆
      closure (Set.range
        (smoothToCanonicalPhysicalBulkL2 period hPeriod)) := by
  rintro value ⟨continuousField, rfl⟩
  exact approximationData.continuous_mem_closure_smoothRange continuousField

/-- Continuous-to-smooth approximation proves density of smooth physical scalar
fields in bulk `L²`. -/
theorem smoothToCanonicalPhysicalBulkL2_denseRange
    (approximationData :
      CanonicalPhysicalScalarContinuousSmoothApproximationData
        period hPeriod) :
    DenseRange (smoothToCanonicalPhysicalBulkL2 period hPeriod) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (continuousToCanonicalPhysicalBulkL2 period hPeriod)) :=
    continuousToCanonicalPhysicalBulkL2_denseRange period hPeriod value
  exact (closure_minimal
    approximationData.continuousRange_subset_closure_smoothRange
    isClosed_closure) hContinuous

/-- Smooth-density certificate. -/
theorem certificate
    (approximationData :
      CanonicalPhysicalScalarContinuousSmoothApproximationData
        period hPeriod) :
    DenseRange (smoothToCanonicalPhysicalBulkL2 period hPeriod) ∧
      (∀ continuousField,
        continuousToCanonicalPhysicalBulkL2 period hPeriod continuousField ∈
          closure (Set.range
            (smoothToCanonicalPhysicalBulkL2 period hPeriod))) :=
  ⟨approximationData.smoothToCanonicalPhysicalBulkL2_denseRange,
    approximationData.continuous_mem_closure_smoothRange⟩

end CanonicalPhysicalScalarContinuousSmoothApproximationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
end JanusFormal
