import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticClosure4D

/-!
# Analytic closure over the wave-natural canonical PDE package

The geometric physical operator is now specified by scalar-wave naturality and
the global divergence identity.  Boundary density, physical measure full
support and all completion machinery are theorems.

The final analytic inputs remain smooth approximation of adjoint graph pairs,
coercivity of one shifted form and Rellich compactness.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticClosure4D
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

/-- Full analytic data over the wave-natural minimal physical boundary package. -/
structure CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
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

namespace CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData

/-- Conversion to the established canonical analytic package. -/
def toCanonicalInteriorAutomaticSixCoefficientAnalyticData
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toCanonicalInteriorAutomaticSixCoefficientPDEData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toCanonicalInteriorAutomaticSixCoefficientAnalyticData
    period hPeriod).actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toCanonicalInteriorAutomaticSixCoefficientAnalyticData
    period hPeriod).compactResolvent period hPeriod

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toCanonicalInteriorAutomaticSixCoefficientAnalyticData
    period hPeriod).fredholmAlternative
      period hPeriod spectralParameter hParameter

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toCanonicalInteriorAutomaticSixCoefficientAnalyticData
    period hPeriod).finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound generated by shifted coercivity. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toCanonicalInteriorAutomaticSixCoefficientAnalyticData
    period hPeriod).eigenvalue_ge_referenceParameter
      period hPeriod eigenvalue hEigenvalue

/-- Wave-natural minimal analytic certificate. -/
theorem certificate
    (analytic :
      CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData
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

end CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientAnalyticClosure4D
end JanusFormal
