import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D

/-!
# Fully reduced physical scalar analytic closure

This is the smallest current physical scalar closure interface.

The boundary triple is constructed from geometric naturality, the divergence
integral, smooth Cauchy extension, continuous-to-smooth approximation, shrinking
collar cutoffs, Gårding and higher normal regularity.  The true Hilbert adjoint
is controlled by smooth graph approximation.  A coercive canonical shifted form
constructs the reference resolvent and lower form bound by Lax--Milgram.  A
compact approximation scheme proves Rellich compactness.

All density, closability, completed trace surjectivity, semiboundedness and
resolvent-surjectivity conclusions are derived.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Fully reduced physical scalar analytic inputs. -/
structure CanonicalPhysicalScalarFullyReducedAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  boundary : CanonicalPhysicalScalarFullyGeometricBoundaryData
    period hPeriod massSquared ValueCore NormalCore
    (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointApproximation : boundary.triple.AdjointPairSmoothApproximationData
    condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellichApproximation : CanonicalPhysicalScalarRellichApproximationData
    period hPeriod

namespace CanonicalPhysicalScalarFullyReducedAnalyticData

/-- Conversion to the elliptic analytic package. -/
def toEllipticAnalyticData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticAnalyticClosure4D.CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      analytic.boundary.green.core.minimalDomainSubmodule
      (Regularity := Regularity) where
  boundary := analytic.boundary.cutoffEllipticBoundaryData.toEllipticBoundaryData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellich := analytic.rellichApproximation.rellich

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toEllipticAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (analytic.toEllipticAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toEllipticAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toEllipticAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the physical compact resolvent. -/
theorem spectral_complete
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toEllipticAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Fully reduced physical scalar closure certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
          period hPeriod) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.green.core
          analytic.boundary.cutoffEllipticBoundaryData.toEllipticBoundaryData
            |>.toBoundaryConstructionData.traceBound) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        analytic.boundary.triple.LagrangianHasEigenvalue
            analytic.condition eigenvalue →
          analytic.referenceParameter ≤ eigenvalue) :=
  ⟨analytic.boundary.smoothing.smoothToCanonicalPhysicalBulkL2_denseRange,
    analytic.boundary.cutoffEllipticBoundaryData.toEllipticBoundaryData
      |>.toBoundaryConstructionData.completedTraceSurjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellichApproximation.rellich,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarFullyReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
end JanusFormal
