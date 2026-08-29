import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveBoundedCoefficientPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticClosure4D

/-!
# Analytic closure over bounded Euler coefficient operators

Six continuous boundary operators generate all six coefficient estimates of the
explicit Cauchy lift.  Together with wave naturality, one energy estimate and
normal elliptic regularity they construct the completed physical boundary
triple.

The final spectral inputs remain adjoint graph approximation, shifted-form
coercivity and Rellich compactness.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveBoundedCoefficientPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticClosure4D
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

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Full analytic data over the bounded-coefficient physical boundary package. -/
structure CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientPDEData
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

namespace CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData

/-- Conversion to the established wave-natural analytic package. -/
def toWaveAutomaticSixCoefficientAnalyticData
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toWaveAutomaticSixCoefficientPDEData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toWaveAutomaticSixCoefficientAnalyticData
    period hPeriod).actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toWaveAutomaticSixCoefficientAnalyticData
    period hPeriod).compactResolvent period hPeriod

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toWaveAutomaticSixCoefficientAnalyticData
    period hPeriod).fredholmAlternative
      period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toWaveAutomaticSixCoefficientAnalyticData
    period hPeriod).finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toWaveAutomaticSixCoefficientAnalyticData
    period hPeriod).eigenvalue_ge_referenceParameter
      period hPeriod eigenvalue hEigenvalue

/-- Bounded-coefficient analytic certificate. -/
theorem certificate
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
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
  ⟨analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveBoundedCoefficientAnalyticClosure4D
end JanusFormal
