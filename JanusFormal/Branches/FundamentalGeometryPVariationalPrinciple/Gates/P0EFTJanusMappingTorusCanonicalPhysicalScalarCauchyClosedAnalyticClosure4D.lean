import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D

/-!
# Analytic closure with the explicit Cauchy extension installed

This interface removes the abstract smooth Cauchy extension, the independent
completed-trace surjectivity hypothesis, the smooth-density hypothesis and the
minimal-core cutoff hypothesis.

The remaining analytic inputs are:

* the Cauchy-closed boundary data constructed from the explicit latitude jet;
* smooth approximation of Hilbert-adjoint graph pairs;
* coercivity of one canonical shifted form;
* compact approximations of the physical `H¹ -> L²` inclusion.

Everything else is derived: density, closability, completed trace surjectivity,
actual Hilbert self-adjointness, a compact reference resolvent, the Fredholm
alternative, finite eigenspace multiplicity, spectral completeness and the
lower spectral bound.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
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

/-- Full physical analytic data after closing the smooth Cauchy extension. -/
structure CanonicalPhysicalScalarCauchyClosedAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  boundary : CanonicalPhysicalScalarCauchyClosedBoundaryData
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

namespace CanonicalPhysicalScalarCauchyClosedAnalyticData

/-- Conversion to the previously completed fully reduced analytic package. -/
def toFullyReducedAnalyticData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  boundary := analytic.boundary.toCutoffClosedBoundaryData
    |>.toFullyGeometricBoundaryData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Physical Fredholm alternative away from the coercive reference point. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the physical compact resolvent. -/
theorem spectral_complete
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Cauchy-closed analytic certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCauchyClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.cauchy.greenCore.core
          analytic.boundary.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
            |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
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
              analytic.condition spectralParameter) :=
  ⟨analytic.boundary.cauchy.boundaryTrace_denseRange,
    analytic.boundary.extensionEstimate.completedBoundaryTrace_surjective
      (analytic.boundary.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
        |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
        |>.toBoundaryConstructionData.traceBound),
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellichApproximation.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarCauchyClosedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedAnalyticClosure4D
end JanusFormal
