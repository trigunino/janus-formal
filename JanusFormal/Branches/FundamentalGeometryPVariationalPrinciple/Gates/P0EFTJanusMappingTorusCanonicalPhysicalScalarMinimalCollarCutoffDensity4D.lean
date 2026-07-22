import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D

/-!
# Physical minimal-core density from smoothing and shrinking collar cutoffs

Two concrete approximation mechanisms suffice for the physical minimal domain:

1. continuous scalar functions are approximated in `L²` by smooth quotient
   scalars;
2. every smooth scalar is approximated in `L²` by smooth fields whose value and
   normal traces vanish, obtained by shrinking collar cutoffs.

The first mechanism proves density of the smooth physical core.  The second
feeds the generic minimal-cutoff theorem and proves density of the zero-Cauchy
minimal core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCollarCutoffDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Physical smoothing plus zero-Cauchy collar cutoff data. -/
structure CanonicalPhysicalScalarMinimalCollarCutoffData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  smoothing : CanonicalPhysicalScalarContinuousSmoothApproximationData
    period hPeriod
  cutoff : Nat →
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      SmoothQuotientField period hPeriod Real
  boundary_zero : ∀ (index : Nat)
    (field : SmoothQuotientField period hPeriod Real),
    green.core.boundaryTrace (cutoff index field) = 0
  tendsto_l2 : ∀ field : SmoothQuotientField period hPeriod Real,
    Tendsto
      (fun index => green.core.inclusion (cutoff index field))
      atTop (𝓝 (green.core.inclusion field))

namespace CanonicalPhysicalScalarMinimalCollarCutoffData

/-- Conversion to the generic zero-Cauchy cutoff package. -/
def toGeneric
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (cutoffData : CanonicalPhysicalScalarMinimalCollarCutoffData
      period hPeriod green) :
    CanonicalScalarGreenCoreMinimalCutoffData green.core where
  smoothDense := by
    simpa [CanonicalPhysicalScalarFirstSheetGreenCoreData.core] using
      cutoffData.smoothing.smoothToCanonicalPhysicalBulkL2_denseRange
  cutoff := cutoffData.cutoff
  boundary_zero := cutoffData.boundary_zero
  tendsto_inclusion := cutoffData.tendsto_l2

/-- Physical zero-Cauchy minimal domain is dense. -/
theorem minimalCoreDense
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (cutoffData : CanonicalPhysicalScalarMinimalCollarCutoffData
      period hPeriod green) :
    green.MinimalCoreDense period hPeriod :=
  (cutoffData.toGeneric green).minimalCoreDense

/-- The physical maximal graph inclusion is injective. -/
theorem graphInclusion_injective
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (cutoffData : CanonicalPhysicalScalarMinimalCollarCutoffData
      period hPeriod green) :
    Function.Injective
      (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
        green.core) :=
  (cutoffData.toGeneric green).graphInclusion_injective

/-- Physical smoothing/cutoff density certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (cutoffData : CanonicalPhysicalScalarMinimalCollarCutoffData
      period hPeriod green) :
    DenseRange (smoothToCanonicalPhysicalBulkL2 period hPeriod) ∧
      green.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          green.core) :=
  ⟨cutoffData.smoothing.smoothToCanonicalPhysicalBulkL2_denseRange,
    cutoffData.minimalCoreDense green,
    cutoffData.graphInclusion_injective green⟩

end CanonicalPhysicalScalarMinimalCollarCutoffData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCollarCutoffDensity4D
end JanusFormal
