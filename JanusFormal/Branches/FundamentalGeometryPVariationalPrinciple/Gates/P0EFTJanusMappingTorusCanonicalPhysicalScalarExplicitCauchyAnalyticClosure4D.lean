import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedAnalytic4D

/-!
# Explicit-Cauchy physical scalar analytic closure

This is the preferred constructive physical scalar interface after closing the
Cauchy extension architecture.  The boundary layer is expressed entirely by
geometric globalization, deck-compatible smooth approximation, tubular inverse
regularity and product-coordinate estimates.

The remaining operator-theoretic inputs are exactly:

* smooth approximation of Hilbert-adjoint graph pairs;
* coercivity of one shifted form;
* compact approximation of the physical `H¹ -> L²` inclusion.

The output includes actual Hilbert self-adjointness, a compact resolvent, the
Fredholm alternative, finite multiplicity, spectral completeness, the lower
spectral bound and the direct variational/Gaussian constructions inherited from
the completed boundary triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyBoundary4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedAnalytic4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Fully explicit-Cauchy physical analytic data. -/
structure CanonicalPhysicalScalarExplicitCauchyAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarExplicitCauchyBoundaryData
    period hPeriod massSquared (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointApproximation : boundary.triple.AdjointPairSmoothApproximationData
    condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellichApproximation : CanonicalPhysicalScalarRellichApproximationData
    period hPeriod

namespace CanonicalPhysicalScalarExplicitCauchyAnalyticData

/-- Conversion to the canonical Cauchy-closed analytic package. -/
def toCanonicalCauchyClosedAnalyticData
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toCanonicalCauchyClosedBoundaryData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  analytic.toCanonicalCauchyClosedAnalyticData.actualAdjointDomain_eq
    period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :=
  analytic.toCanonicalCauchyClosedAnalyticData.compactResolvent
    period hPeriod

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  analytic.toCanonicalCauchyClosedAnalyticData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  analytic.toCanonicalCauchyClosedAnalyticData
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  analytic.toCanonicalCauchyClosedAnalyticData.spectral_complete
    period hPeriod

/-- Explicit-Cauchy analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarExplicitCauchyAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.green.greenCore.core
          analytic.boundary.toCanonicalCauchyClosedBoundaryData
            |>.toCauchyClosedBoundaryData.toCutoffClosedBoundaryData
            |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
            |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) ∧
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
  ⟨analytic.boundary.green.toCanonicalCauchyJetGreenCoreData
      |>.boundaryTrace_denseRange,
    analytic.boundary.toCanonicalCauchyClosedBoundaryData
      |>.toCauchyClosedBoundaryData.extensionEstimate
      |>.completedBoundaryTrace_surjective
        (analytic.boundary.toCanonicalCauchyClosedBoundaryData
          |>.toCauchyClosedBoundaryData.toCutoffClosedBoundaryData
          |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
          |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound),
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellichApproximation.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarExplicitCauchyAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyAnalyticClosure4D
end JanusFormal
