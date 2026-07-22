import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D

/-!
# Final reduced canonical physical scalar analytic closure

This is the smallest current full spectral interface.

The boundary package already derives physical measure full support, both smooth
boundary-core densities, minimal-core density, the tubular Cauchy extension,
completed trace surjectivity, Gårding and the normal graph estimate from natural
identities and bounded operators.

The final analytic package adds only:

* graph membership of every actual Hilbert adjoint pair;
* a positive-square decomposition of one shifted form;
* finite-rank operators converging in norm to the physical `H¹ -> L²` inclusion.

Sequential adjoint approximation, shifted coercivity constants and compactness
of every Rellich approximant are all constructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Smallest current full analytic package. -/
structure CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalReducedPDEData
    period hPeriod massSquared (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointGraphRegularity : boundary.triple.AdjointPairGraphRegularity
    condition
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      condition referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData

/-- Canonical shifted-form coercivity generated from the positive decomposition. -/
def shiftedFormCoercive
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.LagrangianShiftedFormCoerciveData
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedPositiveDecomposition.toShiftedFormCoerciveData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Compact Rellich approximation package generated from finite-rank truncations. -/
def rellichApproximation
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :=
  analytic.finiteRankRellich.toRellichApproximationData

/-- Conversion to the reduced analytic closure. -/
def toReducedAnalyticData
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary
  condition := analytic.condition
  adjointGraphRegularity := analytic.adjointGraphRegularity
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive period hPeriod
  rellichApproximation := analytic.rellichApproximation period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toReducedAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toReducedAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toReducedAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity of every nonreference direct eigenspace. -/
theorem finiteDimensional_operatorEigenspace
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toReducedAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Every physical eigenvalue lies above the positive-decomposition gap
reference. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toReducedAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the compact physical reference resolvent. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toReducedAnalyticData period hPeriod)
    |>.toWaveBoundedCoefficientAnalyticData period hPeriod
    |>.toWaveAutomaticSixCoefficientAnalyticData period hPeriod
    |>.toCanonicalInteriorAutomaticSixCoefficientAnalyticData period hPeriod
    |>.toDenseParametrizedAutomaticSixCoefficientAnalyticData period hPeriod
    |>.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod
    |>.toCanonicalFinalPDEAnalyticData period hPeriod
    |>.toFinalPDEAnalyticData period hPeriod
    |>.toEllipticAnalyticData period hPeriod
    |>.spectral_complete period hPeriod

/-- Final reduced analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.AdjointPairGraphRegularity analytic.condition ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianShiftedForm
            analytic.condition analytic.referenceParameter field field =
          ‖analytic.shiftedPositiveDecomposition.positivePart field‖ ^ 2 +
            analytic.shiftedPositiveDecomposition.gap * ‖field‖ ^ 2) ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        eigenvalue ≠ analytic.referenceParameter →
          FiniteDimensional Real
            (analytic.boundary.triple.lagrangianOperatorEigenspace
              analytic.condition eigenvalue)) ∧
      (∀ eigenvalue : Real,
        analytic.boundary.triple.LagrangianHasEigenvalue
            analytic.condition eigenvalue →
          analytic.referenceParameter ≤ eigenvalue) :=
  ⟨analytic.adjointGraphRegularity,
    analytic.shiftedPositiveDecomposition.form_eq,
    analytic.finiteRankRellich.rellich,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedAnalyticClosure4D
end JanusFormal
