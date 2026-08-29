import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

/-!
# Gaussian response at the resolvent-reduced physical endpoint

The positive shifted decomposition supplies the bounded real reference
resolvent.  This is simultaneously the classical source solution and the
Gaussian response operator.  No adjoint regularity datum is needed.

The endpoint exposes the symmetric source pairing, generating functional,
on-shell action identity, exact polarization, quadratic homogeneity and
nonnegativity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedGaussian4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedGaussian4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData

/-- Symmetric physical Gaussian pairing. -/
def gaussianPairing
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (first second : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianPairing
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- Physical Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) source

/-- Symmetry of the Gaussian response. -/
theorem gaussianPairing_comm
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (first second : BulkL2 period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  analytic.boundary.triple.lagrangianGaussianPairing_comm
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- Generating functional equals minus the on-shell source action. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
      -analytic.boundary.triple.lagrangianSourceAction
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) := by
  unfold gaussianGeneratingFunctional sourceSolution
  exact analytic.boundary.triple
    |>.lagrangianGaussianGeneratingFunctional_eq_neg_onShell
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod) source

/-- Exact Gaussian polarization. -/
theorem gaussianGeneratingFunctional_add
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (first second : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod (first + second) =
      analytic.gaussianGeneratingFunctional period hPeriod first +
        analytic.gaussianGeneratingFunctional period hPeriod second +
        analytic.gaussianPairing period hPeriod first second :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional_add
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- Quadratic homogeneity. -/
theorem gaussianGeneratingFunctional_smul
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (scalar : Real) (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod (scalar • source) =
      scalar ^ 2 *
        analytic.gaussianGeneratingFunctional period hPeriod source :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional_smul
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) scalar source

/-- Positive shifted coercivity gives a nonnegative Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source := by
  unfold gaussianGeneratingFunctional
  exact (analytic.shiftedFormCoercive period hPeriod).gaussian_nonnegative
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod) source

/-- Resolvent-reduced Gaussian certificate. -/
theorem gaussian_certificate
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  ⟨analytic.gaussianGeneratingFunctional_eq_neg_onShell
      period hPeriod source,
    analytic.gaussianGeneratingFunctional_nonnegative
      period hPeriod source⟩

end CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
end JanusFormal
