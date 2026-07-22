import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D

/-!
# Physical Rellich compactness from finite coordinate factorizations

Fourier, Galerkin and spectral truncations are most naturally presented as

`H¹ --analysis_n--> ℝ^{n} --synthesis_n--> L²`.

The analysis map is compact because its codomain is finite dimensional, and
composition with the continuous synthesis map remains compact.  Thus the user
need not prove finite-dimensionality of the range of the composite operator.

Only the two coordinate maps and operator-norm convergence of their composite to
the physical `H¹ -> L²` inclusion remain.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Finite-coordinate factorization of physical Rellich approximants. -/
structure CanonicalPhysicalScalarFiniteCoordinateRellichData where
  analysis : ∀ index : Nat,
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      EuclideanSpace Real (Fin index)
  synthesis : ∀ index : Nat,
    EuclideanSpace Real (Fin index) →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod
  tendsto : Tendsto
    (fun index => (synthesis index).comp (analysis index))
    atTop
    (𝓝 (canonicalPhysicalScalarH1ToBulkL2 period hPeriod))

namespace CanonicalPhysicalScalarFiniteCoordinateRellichData

/-- The `n`th finite-coordinate approximant. -/
def approximation
    (data : CanonicalPhysicalScalarFiniteCoordinateRellichData
      period hPeriod)
    (index : Nat) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  (data.synthesis index).comp (data.analysis index)

/-- The analysis map into finite coordinates is compact. -/
theorem analysis_compact
    (data : CanonicalPhysicalScalarFiniteCoordinateRellichData
      period hPeriod)
    (index : Nat) :
    IsCompactOperator (data.analysis index) :=
  isCompactOperator_of_locallyCompactSpace_dom (data.analysis index)

/-- Every finite-coordinate approximant is compact. -/
theorem approximation_compact
    (data : CanonicalPhysicalScalarFiniteCoordinateRellichData
      period hPeriod)
    (index : Nat) :
    IsCompactOperator (data.approximation index) :=
  (data.analysis_compact index).clm_comp (data.synthesis index)

/-- Conversion to the generic compact-approximation package. -/
def toRellichApproximationData
    (data : CanonicalPhysicalScalarFiniteCoordinateRellichData
      period hPeriod) :
    CanonicalPhysicalScalarRellichApproximationData period hPeriod where
  approximation := data.approximation
  compact := data.approximation_compact
  tendsto := by
    simpa [approximation] using data.tendsto

/-- Physical Rellich compactness. -/
theorem rellich
    (data : CanonicalPhysicalScalarFiniteCoordinateRellichData
      period hPeriod) :
    PhysicalH1RellichCompactness period hPeriod :=
  data.toRellichApproximationData.rellich

/-- Finite-coordinate Rellich certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarFiniteCoordinateRellichData
      period hPeriod) :
    (∀ index : Nat, IsCompactOperator (data.approximation index)) ∧
      IsCompactOperator
        (canonicalPhysicalScalarH1ToBulkL2 period hPeriod) ∧
      Tendsto data.approximation atTop
        (𝓝 (canonicalPhysicalScalarH1ToBulkL2 period hPeriod)) :=
  ⟨data.approximation_compact,
    data.rellich,
    by simpa [approximation] using data.tendsto⟩

end CanonicalPhysicalScalarFiniteCoordinateRellichData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
end JanusFormal
