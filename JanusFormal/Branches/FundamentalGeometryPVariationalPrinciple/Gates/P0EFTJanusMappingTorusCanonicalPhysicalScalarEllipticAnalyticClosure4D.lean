import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticBoundaryTriple4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSequentialAnalyticClosure4D

/-!
# Elliptic physical scalar analytic closure

This is the most concrete current scalar closure interface.

Boundary completion is driven by Gårding, higher normal regularity, smooth Cauchy
extension, and a dense interior core.  Actual adjoint regularity is supplied by
smooth graph approximation.  One coercive shifted form and physical Rellich
compactness then give the self-adjoint compact spectral realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSequentialAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe x y z r

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Full elliptic physical scalar analytic data. -/
structure CanonicalPhysicalScalarEllipticAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y) (InteriorCore : Type z)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore] where
  boundary : CanonicalPhysicalScalarEllipticBoundaryData
    period hPeriod massSquared ValueCore NormalCore InteriorCore
    (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointApproximation : boundary.triple.AdjointPairSmoothApproximationData
    condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellich : PhysicalH1RellichCompactness period hPeriod

namespace CanonicalPhysicalScalarEllipticAnalyticData

/-- Conversion to the general sequential constructive closure. -/
def toSequentialAnalyticData
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore where
  boundary := analytic.boundary.toBoundaryConstructionData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellich := analytic.rellich

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toSequentialAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :=
  (analytic.toSequentialAnalyticData period hPeriod)
    |>.toConstructiveAnalyticData period hPeriod
    |>.compactResolvent period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toSequentialAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toSequentialAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the physical compact resolvent. -/
theorem spectral_complete
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toSequentialAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Elliptic physical analytic-closure certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarEllipticAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :
    Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.green.core
          analytic.boundary.toBoundaryConstructionData.traceBound) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
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
  ⟨analytic.boundary.toBoundaryConstructionData.completedTraceSurjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarEllipticAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticAnalyticClosure4D
end JanusFormal
