import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

/-!
# Boundary-core density from bounded continuous approximation

The canonical latitude base is `S² × ℝ`, hence it is not compact.  The correct
general dense subspace of boundary `L²` is therefore the space of bounded
continuous functions, not `ContinuousMap` equipped with a compact-domain norm.

Bounded continuous real functions are dense for the finite weakly regular
canonical latitude measure.  Density of the periodic and antiperiodic smooth
cores is reduced to approximation of these bounded continuous representatives.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal BoundedContinuousFunction
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

variable (period : Real)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Bounded continuous latitude-base functions included in boundary `L²`. -/
def boundedContinuousToCanonicalLatitudeBoundaryL2 :
    (CanonicalLatitudeBase →ᵇ Real) →L[Real] BoundaryL2 period :=
  BoundedContinuousFunction.toLp (2 : ENNReal)
    (canonicalLatitudeBaseMeasure period) Real

/-- Bounded continuous functions are dense in canonical boundary `L²`. -/
theorem boundedContinuousToCanonicalLatitudeBoundaryL2_denseRange :
    DenseRange (boundedContinuousToCanonicalLatitudeBoundaryL2 period) := by
  exact BoundedContinuousFunction.toLp_denseRange Real
    (canonicalLatitudeBaseMeasure period) Real
    (by norm_num : (2 : ENNReal) ≠ (∞ : ENNReal))

/-- Bounded-continuous-to-smooth periodic approximation data. -/
structure CanonicalLatitudePeriodicContinuousSmoothApproximationData where
  approximation : (CanonicalLatitudeBase →ᵇ Real) → Nat →
    CanonicalLatitudeSmoothPeriodicValueCore period
  tendsto_l2 : ∀ continuousField,
    Tendsto
      (fun index => canonicalLatitudeSmoothPeriodicValueEmbedding period
        (approximation continuousField index))
      atTop
      (𝓝 (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField))

/-- Bounded-continuous-to-smooth antiperiodic approximation data. -/
structure CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData where
  approximation : (CanonicalLatitudeBase →ᵇ Real) → Nat →
    CanonicalLatitudeSmoothAntiperiodicNormalCore period
  tendsto_l2 : ∀ continuousField,
    Tendsto
      (fun index => canonicalLatitudeSmoothAntiperiodicNormalEmbedding period
        (approximation continuousField index))
      atTop
      (𝓝 (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField))

namespace CanonicalLatitudePeriodicContinuousSmoothApproximationData

/-- Every bounded continuous boundary vector belongs to the closure of the
periodic smooth range. -/
theorem continuous_mem_closure_periodicRange
    (approximationData :
      CanonicalLatitudePeriodicContinuousSmoothApproximationData period)
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    boundedContinuousToCanonicalLatitudeBoundaryL2 period continuousField ∈
      closure (Set.range
        (canonicalLatitudeSmoothPeriodicValueEmbedding period)) := by
  apply mem_closure_of_tendsto
    (approximationData.tendsto_l2 continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨approximationData.approximation continuousField index, rfl⟩

/-- The bounded continuous range lies in the closure of the periodic range. -/
theorem continuousRange_subset_closure_periodicRange
    (approximationData :
      CanonicalLatitudePeriodicContinuousSmoothApproximationData period) :
    Set.range (boundedContinuousToCanonicalLatitudeBoundaryL2 period) ⊆
      closure (Set.range
        (canonicalLatitudeSmoothPeriodicValueEmbedding period)) := by
  rintro value ⟨continuousField, rfl⟩
  exact approximationData.continuous_mem_closure_periodicRange
    period continuousField

/-- Periodic smooth boundary representatives are dense. -/
theorem denseRange
    (approximationData :
      CanonicalLatitudePeriodicContinuousSmoothApproximationData period) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (boundedContinuousToCanonicalLatitudeBoundaryL2 period)) :=
    boundedContinuousToCanonicalLatitudeBoundaryL2_denseRange period value
  exact (closure_minimal
    (approximationData.continuousRange_subset_closure_periodicRange period)
    isClosed_closure) hContinuous

end CanonicalLatitudePeriodicContinuousSmoothApproximationData

namespace CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData

/-- Every bounded continuous boundary vector belongs to the closure of the
antiperiodic smooth range. -/
theorem continuous_mem_closure_antiperiodicRange
    (approximationData :
      CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period)
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    boundedContinuousToCanonicalLatitudeBoundaryL2 period continuousField ∈
      closure (Set.range
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)) := by
  apply mem_closure_of_tendsto
    (approximationData.tendsto_l2 continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨approximationData.approximation continuousField index, rfl⟩

/-- The bounded continuous range lies in the closure of the antiperiodic range. -/
theorem continuousRange_subset_closure_antiperiodicRange
    (approximationData :
      CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period) :
    Set.range (boundedContinuousToCanonicalLatitudeBoundaryL2 period) ⊆
      closure (Set.range
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period)) := by
  rintro value ⟨continuousField, rfl⟩
  exact approximationData.continuous_mem_closure_antiperiodicRange
    period continuousField

/-- Antiperiodic smooth boundary representatives are dense. -/
theorem denseRange
    (approximationData :
      CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period) :
    DenseRange
      (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (boundedContinuousToCanonicalLatitudeBoundaryL2 period)) :=
    boundedContinuousToCanonicalLatitudeBoundaryL2_denseRange period value
  exact (closure_minimal
    (approximationData.continuousRange_subset_closure_antiperiodicRange period)
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
  valueDense := approximationData.periodic.denseRange period
  normalDense := approximationData.antiperiodic.denseRange period

/-- Boundary-density reduction certificate. -/
theorem certificate
    (approximationData :
      CanonicalLatitudeBoundaryContinuousSmoothApproximationData period) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) :=
  ⟨approximationData.periodic.denseRange period,
    approximationData.antiperiodic.denseRange period⟩

end CanonicalLatitudeBoundaryContinuousSmoothApproximationData

end
end P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D
end JanusFormal
