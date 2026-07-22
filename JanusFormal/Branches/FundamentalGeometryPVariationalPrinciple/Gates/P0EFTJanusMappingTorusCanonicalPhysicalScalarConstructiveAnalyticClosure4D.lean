import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryTripleConstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetShiftedFormClosure4D

/-!
# Constructive physical scalar analytic closure

This file combines the two constructive halves of the physical scalar program.

The boundary half consists of a smooth Cauchy jet extension, squared elliptic and
normal estimates, a dense interior zero-trace core, and a graph bound for the
extension.  It constructs the corrected completed physical boundary triple.

The operator half consists of maximal adjoint regularity, coercivity of the
canonical shifted form at one real reference parameter, and physical Rellich
compactness.  Lax--Milgram and compact spectral theory then give actual
self-adjointness, compact resolvent, Fredholm alternative, spectral completeness
and the lower spectral bound.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarConstructiveAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryTripleConstruction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetShiftedFormClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe x y z

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Fully constructive scalar analytic input. -/
structure CanonicalPhysicalScalarConstructiveAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y) (InteriorCore : Type z)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore] where
  boundary : CanonicalPhysicalScalarBoundaryTripleConstructionData
    period hPeriod massSquared ValueCore NormalCore InteriorCore
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointRegularity : boundary.triple.MaximalAdjointRegularity condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellich : PhysicalH1RellichCompactness period hPeriod

namespace CanonicalPhysicalScalarConstructiveAnalyticData

/-- Physical shifted-form analytic package constructed from the boundary data. -/
def shiftedFormData
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod analytic.boundary.green analytic.boundary.completedInputs where
  condition := analytic.condition
  adjointRegularity := analytic.adjointRegularity
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellich := analytic.rellich

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.shiftedFormData period hPeriod).actualAdjointDomain_eq
    period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    analytic.boundary.triple.LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormData period hPeriod).compactResolvent period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.shiftedFormData period hPeriod).fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.shiftedFormData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the compact physical resolvent. -/
theorem spectral_complete
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.shiftedFormData period hPeriod).spectral_complete period hPeriod

/-- Fully constructive physical closure certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (analytic : CanonicalPhysicalScalarConstructiveAnalyticData
      period hPeriod massSquared ValueCore NormalCore InteriorCore) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          analytic.boundary.green.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.green.core analytic.boundary.traceBound) ∧
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
  ⟨analytic.boundary.smooth.boundaryTrace_denseRange,
    analytic.boundary.triple.inclusion_injective,
    analytic.boundary.completedTraceSurjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarConstructiveAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarConstructiveAnalyticClosure4D
end JanusFormal
