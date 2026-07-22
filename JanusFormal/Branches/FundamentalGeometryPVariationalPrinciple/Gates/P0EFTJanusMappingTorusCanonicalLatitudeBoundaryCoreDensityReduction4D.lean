import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

/-!
# Boundary-core density from continuous deck-compatible approximation

Continuous real functions are dense in `L²` for the finite canonical latitude
base measure.  Therefore density of the canonical periodic and antiperiodic
smooth cores is reduced to two approximation constructions:

* approximate every continuous function in `L²` by smooth periodic
  representatives;
* approximate every continuous function in `L²` by smooth antiperiodic
  representatives.

The endpoint identifications have measure zero, so these approximation theorems
may later be constructed by smoothing on one period followed by periodic or
sign-twisted periodization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

variable (period : Real)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Continuous latitude-base functions included in boundary `L²`. -/
def continuousToCanonicalLatitudeBoundaryL2 :
    C(CanonicalLatitudeBase, Real) →L[Real] BoundaryL2 period :=
  ContinuousMap.toLp (2 : ENNReal)
    (canonicalLatitudeBaseMeasure period) Real

/-- Continuous functions are dense in the canonical latitude boundary `L²`. -/
theorem continuousToCanonicalLatitudeBoundaryL2_denseRange :
    DenseRange (continuousToCanonicalLatitudeBoundaryL2 period) := by
  exact ContinuousMap.toLp_denseRange Real
    (canonicalLatitudeBaseMeasure period) Real
    (by norm_num : (2 : ENNReal) ≠ ∞)

/-- Continuous-to-smooth periodic approximation data. -/
structure CanonicalLatitudePeriodicContinuousSmoothApproximationData where
  approximation : C(CanonicalLatitudeBase, Real) → Nat →
    CanonicalLatitudeSmoothPeriodicValueCore period
  tendsto_l2 : ∀ continuousField,
    Tendsto
      (fun index => canonicalLatitudeSmoothPeriodicValueEmbedding period
        (approximation continuousField index))
      atTop
      (𝓝 (continuousToCanonicalLatitudeBoundaryL2 period continuousField))

/-- Continuous-to-smooth antiperiodic approximation data. -/
structure CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData where
  approximation : C(CanonicalLatitudeBase, Real) → Nat →
    CanonicalLatitudeSmoothAntiperiodicNormalCore period
  tendsto_l2 : ∀ continuousField,
    Tendsto
      (fun index => canonicalLatitudeSmoothAntiperiodicNormalEmbedding period
        (approximation continuousField index))
      atTop
      (𝓝 (continuousToCanonicalLatitudeBoundaryL2 period continuousField))

namespace CanonicalLatitudePeriodicContinuousSmoothApproximationData

/-- Every continuous boundary vector belongs to the closure of the periodic
smooth range. -/
theorem continuous_mem_closure_periodicRange
    (approximationData :
      CanonicalLatitudePeriodicContinuousSmoothApproximationData period)
    (continuousField : C(CanonicalLatitudeBase, Real)) :
    continuousToCanonicalLatitudeBoundaryL2 period continuousField ∈
      closure (Set.range
        (canonicalLatitudeSmoothPeriodicValueEmbedding period)) := by
  apply mem_closure_of_tendsto
    (approximationData.tendsto_l2 continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨approximationData.approximation continuousField index, rfl⟩

/-- Continuous range lies in the closure of the periodic smooth range. -/
theorem continuousRange_subset_closure_periodicRange
    (approximationData :
      CanonicalLatitudePeriodicContinuousSmoothApproximationData period) :
    Set.range (continuousToCanonicalLatitudeBoundaryL2 period) ⊆
      closure (Set.range
        (canonicalLatitudeSmoothPeriodicValueEmbedding period)) := by
  rintro value ⟨continuousField, rfl⟩
  exact approximationData.continuous_mem_closure_periodicRange continuousField

/-- Periodic smooth boundary representatives are dense. -/
theorem denseRange
    (approximationData :
      CanonicalLatitudePeriodicContinuousSmoothApproximationData period) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (continuousToCanonicalLatitudeBoundaryL2 period)) :=
    continuousToCanonicalLatitudeBoundaryL2_denseRange period value
  exact (closure_minimal
    approximationData.continuousRange_subset_closure_periodicRange
    isClosed_closure) hContinuous

end CanonicalLatitudePeriodicContinuousSmoothApproximationData

namespace CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData

/-- Every continuous boundary vector belongs to the closure of the
antiperiodic smooth range. -/
theorem continuous_mem_closure_antiperiodicRange
    (approximationData :
      CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period)
    (continuousField : C(CanonicalLatitudeBase, Real)) :
    continuousToCanonicalLatitudeBoundaryL2 period continuousField ∈
      closure (Set.range
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)) := by
  apply mem_closure_of_tendsto
    (approximationData.tendsto_l2 continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨approximationData.approximation continuousField index, rfl⟩

/-- Continuous range lies in the closure of the antiperiodic smooth range. -/
theorem continuousRange_subset_closure_antiperiodicRange
    (approximationData :
      CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period) :
    Set.range (continuousToCanonicalLatitudeBoundaryL2 period) ⊆
      closure (Set.range
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)) := by
  rintro value ⟨continuousField, rfl⟩
  exact approximationData.continuous_mem_closure_antiperiodicRange continuousField

/-- Antiperiodic smooth boundary representatives are dense. -/
theorem denseRange
    (approximationData :
      CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period) :
    DenseRange
      (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (continuousToCanonicalLatitudeBoundaryL2 period)) :=
    continuousToCanonicalLatitudeBoundaryL2_denseRange period value
  exact (closure_minimal
    approximationData.continuousRange_subset_closure_antiperiodicRange
    isClosed_closure) hContinuous

end CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData

/-- Combined canonical boundary-core approximation package. -/
structure CanonicalLatitudeBoundaryContinuousSmoothApproximationData where
  periodic : CanonicalLatitudePeriodicContinuousSmoothApproximationData period
  antiperiodic :
    CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period

namespace CanonicalLatitudeBoundaryContinuousSmoothApproximationData

/-- Install the canonical boundary-core density data. -/
def toBoundaryCoreDensityData
    (approximationData :
      CanonicalLatitudeBoundaryContinuousSmoothApproximationData period) :
    CanonicalLatitudeSmoothBoundaryCoreDensityData period where
  valueDense := approximationData.periodic.denseRange
  normalDense := approximationData.antiperiodic.denseRange

/-- Boundary-density reduction certificate. -/
theorem certificate
    (approximationData :
      CanonicalLatitudeBoundaryContinuousSmoothApproximationData period) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) :=
  ⟨approximationData.periodic.denseRange,
    approximationData.antiperiodic.denseRange⟩

end CanonicalLatitudeBoundaryContinuousSmoothApproximationData

end
end P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D
end JanusFormal
