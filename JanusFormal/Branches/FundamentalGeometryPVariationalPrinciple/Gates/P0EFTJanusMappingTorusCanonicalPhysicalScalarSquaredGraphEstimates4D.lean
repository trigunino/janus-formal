import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

/-!
# Squared physical graph estimates

PDE energy estimates are naturally proved in squared norm form.  The physical
boundary-triple interface uses linear norm bounds.  Since all constants and
norms are nonnegative, the squared inequalities immediately imply the required
linear estimates.

This file packages that conversion for both the physical `H¹` graph estimate and
the first-sheet normal trace.  Coarea is already a theorem, so a squared
elliptic estimate, a squared normal estimate, minimal-core density and completed
trace surjectivity are sufficient to install the completed physical boundary
triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarSquaredGraphEstimates4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Squared graph-elliptic estimate. -/
structure SquaredGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound_sq : ∀ field : SmoothQuotientField period hPeriod Real,
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
      constant ^ 2 * ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2

/-- Squared normal-trace graph estimate. -/
structure SquaredNormalGraphEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound_sq : ∀ field : SmoothQuotientField period hPeriod Real,
    ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
        period hPeriod field‖ ^ 2 ≤
      constant ^ 2 * ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2

/-- A squared elliptic estimate gives the linear graph estimate. -/
def SquaredGraphEllipticEstimate.toGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (estimate : green.SquaredGraphEllipticEstimate period hPeriod) :
    green.GraphEllipticEstimate period hPeriod where
  constant := estimate.constant
  nonnegative := estimate.nonnegative
  bound := by
    intro field
    have hSquare := estimate.bound_sq field
    have hLeft :
        0 ≤ ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ :=
      norm_nonneg _
    have hRight :
        0 ≤ estimate.constant *
          ‖canonicalScalarGreenCoreToGraph green.core field‖ :=
      mul_nonneg estimate.nonnegative (norm_nonneg _)
    nlinarith

/-- A squared normal estimate gives the linear graph estimate. -/
def SquaredNormalGraphEstimate.toNormalGraphEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (estimate : green.SquaredNormalGraphEstimate period hPeriod) :
    green.NormalGraphEstimate period hPeriod where
  constant := estimate.constant
  nonnegative := estimate.nonnegative
  bound := by
    intro field
    have hSquare := estimate.bound_sq field
    have hLeft :
        0 ≤ ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
          period hPeriod field‖ := norm_nonneg _
    have hRight :
        0 ≤ estimate.constant *
          ‖canonicalScalarGreenCoreToGraph green.core field‖ :=
      mul_nonneg estimate.nonnegative (norm_nonneg _)
    nlinarith

/-- Completed-boundary inputs stated entirely in the squared energy language. -/
structure SquaredCompletedBoundaryInputs
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  elliptic : green.SquaredGraphEllipticEstimate period hPeriod
  normal : green.SquaredNormalGraphEstimate period hPeriod
  minimalDense : green.MinimalCoreDense period hPeriod
  completedTraceSurjective : green.CompletedBoundaryTraceSurjective
    period hPeriod
    (green.boundaryGraphBound period hPeriod
      (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
      (elliptic.toGraphEllipticEstimate green)
      (normal.toNormalGraphEstimate green))

namespace SquaredCompletedBoundaryInputs

/-- Conversion to the completed physical boundary-triple input. -/
def toCompletedBoundaryTripleInputs
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.SquaredCompletedBoundaryInputs period hPeriod) :
    green.CompletedBoundaryTripleInputs period hPeriod where
  coarea := canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod
  elliptic := inputs.elliptic.toGraphEllipticEstimate green
  normal := inputs.normal.toNormalGraphEstimate green
  minimalDense := inputs.minimalDense
  completedTraceSurjective := inputs.completedTraceSurjective

/-- Completed physical boundary triple generated by squared estimates. -/
def triple
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.SquaredCompletedBoundaryInputs period hPeriod) :=
  (inputs.toCompletedBoundaryTripleInputs green).triple green

/-- Squared estimates install all boundary-completion data. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.SquaredCompletedBoundaryInputs period hPeriod) :
    Function.Injective
        (canonicalScalarGreenCoreGraphInclusion green.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace green.core
          ((inputs.toCompletedBoundaryTripleInputs green).traceBound green)) :=
  ⟨(inputs.triple green).inclusion_injective,
    (inputs.triple green).boundary_surjective⟩

end SquaredCompletedBoundaryInputs

/-- Squared-estimate conversion certificate. -/
theorem squaredGraphEstimates_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (elliptic : green.SquaredGraphEllipticEstimate period hPeriod)
    (normal : green.SquaredNormalGraphEstimate period hPeriod) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ≤
        elliptic.constant *
          ‖canonicalScalarGreenCoreToGraph green.core field‖) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
            period hPeriod field‖ ≤
          normal.constant *
            ‖canonicalScalarGreenCoreToGraph green.core field‖) :=
  ⟨(elliptic.toGraphEllipticEstimate green).bound,
    (normal.toNormalGraphEstimate green).bound⟩

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarSquaredGraphEstimates4D
end JanusFormal
