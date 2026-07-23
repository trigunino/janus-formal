import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D

/-!
# Analytic closure after smooth density and cutoff closure

Smooth physical `L²` density and the shrinking zero-Cauchy collar cutoff family
are now theorems.  The final analytic package can therefore use the
cutoff-closed boundary data directly, instead of carrying a smoothing scheme and
an abstract cutoff sequence.

The remaining analytic inputs are exactly:

* geometric Green-core data;
* Gårding and higher normal regularity;
* a graph-bounded smooth Cauchy extension;
* smooth approximation of Hilbert-adjoint graph pairs;
* coercivity at one shifted parameter;
* compact approximations of the physical `H¹ -> L²` inclusion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final physical analytic inputs after global cutoff closure. -/
structure CanonicalPhysicalScalarCutoffClosedAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  boundary : CanonicalPhysicalScalarCutoffClosedBoundaryData
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

namespace CanonicalPhysicalScalarCutoffClosedAnalyticData

/-- Conversion to the previous fully reduced package.  The smoothing and cutoff
fields are filled by the unconditional theorems. -/
def toFullyReducedAnalyticData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  boundary := analytic.boundary.toFullyGeometricBoundaryData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- The zero-Cauchy minimal core is unconditionally dense. -/
theorem minimalCoreDense
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    analytic.boundary.geometric.greenCore.MinimalCoreDense period hPeriod :=
  (analytic.boundary.certificate).1

/-- The maximal graph inclusion is single-valued. -/
theorem graphInclusion_injective
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    Function.Injective
      (canonicalScalarGreenCoreGraphInclusion
        analytic.boundary.geometric.greenCore.core) :=
  (analytic.boundary.certificate).2.1

/-- The completed physical Cauchy trace is surjective. -/
theorem completedTrace_surjective
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace
        analytic.boundary.geometric.greenCore.core
        (analytic.boundary.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
          |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound)) :=
  (analytic.boundary.certificate).2.2

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
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

/-- Every eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the compact physical resolvent. -/
theorem spectral_complete
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toFullyReducedAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Cutoff-closed analytic certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
          period hPeriod) ∧
      analytic.boundary.geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          analytic.boundary.geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.geometric.greenCore.core
          (analytic.boundary.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
            |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound)) ∧
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
  ⟨P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D.smoothToCanonicalPhysicalBulkL2_denseRange
      period hPeriod,
    analytic.minimalCoreDense period hPeriod,
    analytic.graphInclusion_injective period hPeriod,
    analytic.completedTrace_surjective period hPeriod,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellichApproximation.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarCutoffClosedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticClosure4D
end JanusFormal
