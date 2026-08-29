import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarConstructiveAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D

/-!
# Physical scalar closure from smooth adjoint-pair approximation

The final adjoint regularity input is made constructive here.  Instead of
postulating a maximal graph representative for every Hilbert adjoint pair, it is
enough to supply smooth physical scalar fields whose values converge to the
candidate and whose Euler images converge to the proposed adjoint value.

Together with the constructive boundary triple, coercivity of one shifted form,
and physical Rellich compactness, this sequential approximation yields the full
physical scalar self-adjoint compact spectral closure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarSequentialAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryTripleConstruction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarConstructiveAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe x y z

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Fully constructive physical analytic data using smooth graph approximation
for the adjoint regularity theorem. -/
structure CanonicalPhysicalScalarSequentialAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y) (InteriorCore : Type z)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore] where
  boundary : CanonicalPhysicalScalarBoundaryTripleConstructionData
    period hPeriod massSquared ValueCore NormalCore InteriorCore
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointApproximation :
    boundary.triple.AdjointPairSmoothApproximationData condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellich : PhysicalH1RellichCompactness period hPeriod

namespace CanonicalPhysicalScalarSequentialAnalyticData

/-- Conversion to the constructive physical closure package. -/
def toConstructiveAnalyticData
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore where
  boundary := analytic.boundary
  condition := analytic.condition
  adjointRegularity := analytic.adjointApproximation.maximalAdjointRegularity
    analytic.boundary.triple analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellich := analytic.rellich

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toConstructiveAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toConstructiveAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toConstructiveAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the physical compact reference resolvent. -/
theorem spectral_complete
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (((analytic.toConstructiveAnalyticData period hPeriod)
          |>.compactResolvent period hPeriod).bounded.ambientResolvent
            analytic.boundary.triple analytic.condition
              analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toConstructiveAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Sequential constructive closure certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarSequentialAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    analytic.boundary.triple.AdjointPairGraphRegularity analytic.condition ∧
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
  ⟨analytic.adjointApproximation.graphRegularity
      analytic.boundary.triple analytic.condition,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarSequentialAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarSequentialAnalyticClosure4D
end JanusFormal
