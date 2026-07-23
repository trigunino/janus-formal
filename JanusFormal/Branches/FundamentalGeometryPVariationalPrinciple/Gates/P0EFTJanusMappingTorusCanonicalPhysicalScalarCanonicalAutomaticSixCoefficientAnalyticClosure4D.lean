import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalPDEAnalyticClosure4D

/-!
# Analytic closure for the minimal canonical physical scalar PDE package

The canonical boundary theory is now reduced to one first-jet energy estimate,
one normal elliptic regularity theorem, and six tangential Euler coefficient
bounds.  This file carries that boundary package through the actual-adjoint,
Lax--Milgram and compact-resolvent machinery.

The only further analytic inputs are:

* smooth approximation of Hilbert adjoint pairs in the operator graph;
* coercivity of one shifted canonical form;
* a compact approximation of the physical `H¹ -> L²` inclusion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalPDEAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Full analytic data over the minimal canonical boundary package. -/
structure CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
    (massSquared : Real) where
  boundary :
    CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
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

namespace CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData

/-- Conversion to the canonical final analytic package. -/
def toCanonicalFinalPDEAnalyticData
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalFinalPDEAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toCanonicalFinalPDEData period hPeriod
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness of the selected physical realization. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toCanonicalFinalPDEAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toCanonicalFinalPDEAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toCanonicalFinalPDEAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toCanonicalFinalPDEAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toCanonicalFinalPDEAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Minimal canonical analytic certificate. -/
theorem certificate
    (analytic :
      CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          (analytic.boundary.geometric.greenCore period hPeriod).core
          ((analytic.boundary.completedInputs period hPeriod).traceBound
            period hPeriod
            (analytic.boundary.geometric.greenCore period hPeriod))) ∧
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
  ⟨(analytic.boundary.certificate period hPeriod).2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticClosure4D
end JanusFormal
