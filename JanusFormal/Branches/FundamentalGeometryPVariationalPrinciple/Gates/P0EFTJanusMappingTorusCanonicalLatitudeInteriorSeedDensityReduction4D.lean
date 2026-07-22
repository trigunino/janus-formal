import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D

/-!
# Both boundary densities from one interior seed approximation

Bounded continuous functions are dense in the canonical boundary `L²`.  It is
therefore enough to approximate each bounded continuous function by smooth seeds
supported inside the open fundamental time interval.

The periodization theorem sends the same seed sequence to both the periodic
value core and the antiperiodic normal core without changing its `L²` class.
Thus the two former approximation inputs are replaced by one common
bounded-continuous-to-interior-smooth approximation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedDensityReduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A single bounded-continuous-to-smooth approximation by interior-supported
seeds. -/
structure CanonicalLatitudeContinuousInteriorSeedApproximationData where
  approximation : (CanonicalLatitudeBase →ᵇ Real) → Nat →
    CanonicalLatitudeSmoothInteriorSeedCore period
  tendsto_l2 : ∀ continuousField,
    Tendsto
      (fun index => canonicalLatitudeSmoothInteriorSeedEmbedding period
        (approximation continuousField index))
      atTop
      (𝓝 (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField))

namespace CanonicalLatitudeContinuousInteriorSeedApproximationData

/-- Every bounded continuous boundary vector belongs to the closure of the
interior-seed range. -/
theorem continuous_mem_closure_seedRange
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period)
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    boundedContinuousToCanonicalLatitudeBoundaryL2 period continuousField ∈
      closure (Set.range
        (canonicalLatitudeSmoothInteriorSeedEmbedding period)) := by
  apply mem_closure_of_tendsto
    (approximationData.tendsto_l2 continuousField)
  exact Filter.Eventually.of_forall fun index =>
    ⟨approximationData.approximation continuousField index, rfl⟩

/-- The bounded continuous range lies in the closure of the interior-seed
range. -/
theorem continuousRange_subset_closure_seedRange
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    Set.range (boundedContinuousToCanonicalLatitudeBoundaryL2 period) ⊆
      closure (Set.range
        (canonicalLatitudeSmoothInteriorSeedEmbedding period)) := by
  rintro value ⟨continuousField, rfl⟩
  exact approximationData.continuous_mem_closure_seedRange continuousField

/-- Smooth interior-supported seeds are dense in boundary `L²`. -/
theorem denseRange
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    DenseRange (canonicalLatitudeSmoothInteriorSeedEmbedding period) := by
  intro value
  have hContinuous : value ∈ closure
      (Set.range (boundedContinuousToCanonicalLatitudeBoundaryL2 period)) :=
    boundedContinuousToCanonicalLatitudeBoundaryL2_denseRange period value
  exact (closure_minimal
    approximationData.continuousRange_subset_closure_seedRange
    isClosed_closure) hContinuous

/-- Install the single interior-seed density datum. -/
def toInteriorSeedDensityData
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    CanonicalLatitudeSmoothInteriorSeedDensityData period where
  dense := approximationData.denseRange

/-- Install both canonical periodic and antiperiodic boundary densities. -/
def toBoundaryCoreDensityData
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    CanonicalLatitudeSmoothBoundaryCoreDensityData period :=
  approximationData.toInteriorSeedDensityData
    |>.toSmoothBoundaryCoreDensityData hPeriod

/-- Periodic approximation obtained by periodizing the common seed sequence. -/
def toPeriodicApproximationData
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    CanonicalLatitudePeriodicContinuousSmoothApproximationData period where
  approximation continuousField index :=
    canonicalLatitudePeriodicCoreOfInteriorSeed period hPeriod
      (approximationData.approximation continuousField index)
  tendsto_l2 continuousField := by
    simpa only [canonicalLatitudePeriodicCoreOfInteriorSeed_embedding] using
      approximationData.tendsto_l2 continuousField

/-- Antiperiodic approximation obtained from the same seed sequence. -/
def toAntiperiodicApproximationData
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    CanonicalLatitudeAntiperiodicContinuousSmoothApproximationData period where
  approximation continuousField index :=
    canonicalLatitudeAntiperiodicCoreOfInteriorSeed period hPeriod
      (approximationData.approximation continuousField index)
  tendsto_l2 continuousField := by
    simpa only [canonicalLatitudeAntiperiodicCoreOfInteriorSeed_embedding] using
      approximationData.tendsto_l2 continuousField

/-- Common-seed density certificate. -/
theorem certificate
    (approximationData :
      CanonicalLatitudeContinuousInteriorSeedApproximationData period) :
    DenseRange (canonicalLatitudeSmoothInteriorSeedEmbedding period) ∧
      DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) :=
  ⟨approximationData.denseRange,
    approximationData.toPeriodicApproximationData hPeriod |>.denseRange,
    approximationData.toAntiperiodicApproximationData hPeriod |>.denseRange⟩

end CanonicalLatitudeContinuousInteriorSeedApproximationData

end
end P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedDensityReduction4D
end JanusFormal
