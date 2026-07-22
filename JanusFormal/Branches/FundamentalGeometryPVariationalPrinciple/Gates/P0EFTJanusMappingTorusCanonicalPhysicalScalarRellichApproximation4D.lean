import Mathlib.Analysis.Normed.Operator.Compact.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D

/-!
# Rellich compactness from operator-norm compact approximations

To prove compactness of the physical `H¹ -> L²` inclusion it is enough to
construct compact approximating operators converging to the inclusion in the
continuous-linear-map topology.  In applications these approximants may be
finite-mode, Galerkin, heat-kernel, or local mollifier truncations.

The space of compact continuous linear maps into a complete space is closed, so
the limiting physical inclusion is compact.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Compact approximation scheme for the physical `H¹ -> L²` inclusion. -/
structure CanonicalPhysicalScalarRellichApproximationData where
  approximation : Nat →
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod
  compact : ∀ index : Nat,
    IsCompactOperator (approximation index)
  tendsto : Tendsto approximation atTop
    (𝓝 (canonicalPhysicalScalarH1ToBulkL2 period hPeriod))

namespace CanonicalPhysicalScalarRellichApproximationData

/-- The compact approximation limit is the physical Rellich embedding. -/
theorem rellich
    (approximationData : CanonicalPhysicalScalarRellichApproximationData
      period hPeriod) :
    PhysicalH1RellichCompactness period hPeriod :=
  isCompactOperator_of_tendsto approximationData.tendsto
    (Filter.Eventually.of_forall approximationData.compact)

/-- Every completed physical scalar Green core can use the same Rellich
approximation theorem. -/
theorem maximalGraphInclusion_compact
    (approximationData : CanonicalPhysicalScalarRellichApproximationData
      period hPeriod)
    (green :
      P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
        period hPeriod massSquared)
    (elliptic : green.GraphEllipticEstimate period hPeriod) :
    IsCompactOperator
      (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
        green.core) :=
  green.maximalGraphInclusion_compact period hPeriod elliptic
    approximationData.rellich

/-- Compact-approximation certificate. -/
theorem certificate
    (approximationData : CanonicalPhysicalScalarRellichApproximationData
      period hPeriod) :
    IsCompactOperator
        (canonicalPhysicalScalarH1ToBulkL2 period hPeriod) ∧
      Tendsto approximationData.approximation atTop
        (𝓝 (canonicalPhysicalScalarH1ToBulkL2 period hPeriod)) :=
  ⟨approximationData.rellich, approximationData.tendsto⟩

end CanonicalPhysicalScalarRellichApproximationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
end JanusFormal
