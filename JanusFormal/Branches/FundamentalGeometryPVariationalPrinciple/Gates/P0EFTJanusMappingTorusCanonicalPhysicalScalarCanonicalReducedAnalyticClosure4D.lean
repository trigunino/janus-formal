import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticClosure4D

/-!
# Analytic closure over the reduced canonical PDE package

The boundary theory is reduced to natural geometric identities and bounded
operators.  The final analytic layer adds only:

* smooth approximation of Hilbert adjoint graph pairs;
* coercivity of one shifted Lagrangian form;
* compact approximation of the physical `H¹ -> L²` inclusion.

All density, trace-surjectivity, self-adjointness, compact-resolvent and spectral
conclusions are derived.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Full analytic data over the reduced canonical physical boundary package. -/
structure CanonicalPhysicalScalarCanonicalReducedAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalReducedPDEData
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

namespace CanonicalPhysicalScalarCanonicalReducedAnalyticData

/-- Conversion to the bounded-coefficient analytic package. -/
def toWaveBoundedCoefficientAnalyticData
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toWaveExactEnergyPDEData.toWaveBoundedCoefficientPDEData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toWaveBoundedCoefficientAnalyticData
    period hPeriod).actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toWaveBoundedCoefficientAnalyticData
    period hPeriod).compactResolvent period hPeriod

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toWaveBoundedCoefficientAnalyticData
    period hPeriod).fredholmAlternative
      period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toWaveBoundedCoefficientAnalyticData
    period hPeriod).finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toWaveBoundedCoefficientAnalyticData
    period hPeriod).eigenvalue_ge_referenceParameter
      period hPeriod eigenvalue hEigenvalue

/-- Reduced canonical analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarCanonicalReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.geometric.greenCore.core
          (analytic.boundary.completedInputs.traceBound
            analytic.boundary.geometric.greenCore)) ∧
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
  ⟨analytic.boundary.certificate.2.2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedAnalyticClosure4D
end JanusFormal
