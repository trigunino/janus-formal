import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D

/-!
# Physical Rellich compactness from finite-rank truncations

Galerkin, Fourier and spectral truncations naturally have finite-dimensional
range.  Such operators are compact automatically: factor the approximation
through its range, use compactness of the identity on a finite-dimensional
space, then include the range back into bulk `L²`.

Therefore a Rellich approximation scheme only needs:

* continuous linear approximants;
* finite dimensionality of each range;
* operator-norm convergence to the physical `H¹ -> L²` inclusion.

No separate compactness proof is required for each truncation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Finite-rank approximation scheme for the physical Rellich embedding. -/
structure CanonicalPhysicalScalarFiniteRankRellichData where
  approximation : Nat →
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod
  finiteRange : ∀ index : Nat,
    FiniteDimensional Real
      (LinearMap.range (approximation index).toLinearMap)
  tendsto : Tendsto approximation atTop
    (𝓝 (canonicalPhysicalScalarH1ToBulkL2 period hPeriod))

namespace CanonicalPhysicalScalarFiniteRankRellichData

/-- Every finite-rank approximation is compact. -/
theorem approximation_compact
    (data : CanonicalPhysicalScalarFiniteRankRellichData period hPeriod)
    (index : Nat) :
    IsCompactOperator (data.approximation index) := by
  let range := LinearMap.range (data.approximation index).toLinearMap
  letI : FiniteDimensional Real range := data.finiteRange index
  have hRangeCompact : IsCompactOperator
      (data.approximation index).rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom
      (data.approximation index).rangeRestrict
  have hIncluded : IsCompactOperator
      (range.subtypeL ∘L (data.approximation index).rangeRestrict) :=
    hRangeCompact.clm_comp range.subtypeL
  have hFactor :
      range.subtypeL ∘L (data.approximation index).rangeRestrict =
        data.approximation index := by
    rfl
  rwa [hFactor] at hIncluded

/-- Conversion to the generic compact-approximation package. -/
def toRellichApproximationData
    (data : CanonicalPhysicalScalarFiniteRankRellichData period hPeriod) :
    CanonicalPhysicalScalarRellichApproximationData period hPeriod where
  approximation := data.approximation
  compact := data.approximation_compact period hPeriod
  tendsto := data.tendsto

/-- Physical Rellich compactness. -/
theorem rellich
    (data : CanonicalPhysicalScalarFiniteRankRellichData period hPeriod) :
    PhysicalH1RellichCompactness period hPeriod :=
  (data.toRellichApproximationData period hPeriod).rellich

/-- Finite-rank Rellich certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarFiniteRankRellichData period hPeriod) :
    (∀ index : Nat, IsCompactOperator (data.approximation index)) ∧
      IsCompactOperator
        (canonicalPhysicalScalarH1ToBulkL2 period hPeriod) ∧
      Tendsto data.approximation atTop
        (𝓝 (canonicalPhysicalScalarH1ToBulkL2 period hPeriod)) :=
  ⟨data.approximation_compact period hPeriod,
    data.rellich period hPeriod,
    data.tendsto⟩

end CanonicalPhysicalScalarFiniteRankRellichData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
end JanusFormal
