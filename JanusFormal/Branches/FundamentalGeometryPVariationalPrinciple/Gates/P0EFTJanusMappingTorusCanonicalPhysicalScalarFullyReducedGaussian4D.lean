import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

/-!
# Fully reduced physical scalar Gaussian response

The compact reference resolvent of a fully reduced physical scalar realization
is the Gaussian response operator.  This file exports its symmetric source
pairing, generating functional, on-shell action identity, exact polarization and
nonnegativity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedGaussian4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedVariational4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

namespace CanonicalPhysicalScalarFullyReducedAnalyticData

/-- Physical Gaussian response pairing at the coercive reference parameter. -/
def gaussianPairing
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (first second :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianPairing
    analytic.condition analytic.referenceParameter
    (analytic.compactResolvent period hPeriod).bounded first second

/-- Physical Gaussian generating functional. -/
def gaussianGeneratingFunctional
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional
    analytic.condition analytic.referenceParameter
    (analytic.compactResolvent period hPeriod).bounded source

/-- Symmetry of the physical Gaussian pairing. -/
theorem gaussianPairing_comm
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (first second :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  analytic.boundary.triple.lagrangianGaussianPairing_comm
    analytic.condition analytic.referenceParameter
    (analytic.compactResolvent period hPeriod).bounded first second

/-- Physical generating functional is minus the on-shell source action. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
      -analytic.boundary.triple.lagrangianSourceAction
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) := by
  unfold gaussianGeneratingFunctional sourceSolution
  exact analytic.boundary.triple
    |>.lagrangianGaussianGeneratingFunctional_eq_neg_onShell
      analytic.condition analytic.referenceParameter
      (analytic.compactResolvent period hPeriod).bounded source

/-- Exact physical Gaussian polarization. -/
theorem gaussianGeneratingFunctional_add
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (first second :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod (first + second) =
      analytic.gaussianGeneratingFunctional period hPeriod first +
        analytic.gaussianGeneratingFunctional period hPeriod second +
        analytic.gaussianPairing period hPeriod first second :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional_add
    analytic.condition analytic.referenceParameter
    (analytic.compactResolvent period hPeriod).bounded first second

/-- Nonnegativity of the physical Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source := by
  unfold gaussianGeneratingFunctional
  exact analytic.shiftedFormCoercive.gaussian_nonnegative
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    ((analytic.toEllipticAnalyticData period hPeriod)
      |>.toSequentialAnalyticData period hPeriod
      |>.toConstructiveAnalyticData period hPeriod
      |>.shiftedFormData period hPeriod
      |>.denseDomain period hPeriod)
    source

/-- Fully reduced physical Gaussian certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  ⟨analytic.gaussianGeneratingFunctional_eq_neg_onShell
      period hPeriod source,
    analytic.gaussianGeneratingFunctional_nonnegative
      period hPeriod source⟩

end CanonicalPhysicalScalarFullyReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedGaussian4D
end JanusFormal
