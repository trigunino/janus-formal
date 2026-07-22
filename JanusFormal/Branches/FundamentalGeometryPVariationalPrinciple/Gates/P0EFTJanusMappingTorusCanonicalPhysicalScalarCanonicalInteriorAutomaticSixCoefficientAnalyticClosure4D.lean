import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticClosure4D

/-!
# Analytic closure over the open-fundamental-strip canonical package

The physical full-support route is now completely concrete: round `S³` times
the interior of one period has open-positive source measure, preserves the
physical Lorentz volume and has dense physical image.

Together with the minimal PDE package, the final analytic inputs are smooth
adjoint approximation, shifted coercivity and Rellich compactness.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticClosure4D
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

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Full analytic data over the canonical minimal physical boundary package. -/
structure CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
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

namespace CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData

/-- Conversion to the generic dense-parametrized analytic package. -/
def toDenseParametrizedAutomaticSixCoefficientAnalyticData
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
      period hPeriod
      (CanonicalLorentzInteriorParameter period)
      (canonicalLorentzInteriorMeasure period)
      massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toDenseParametrizedAutomaticSixCoefficientPDEData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness of the selected physical realization. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Open-fundamental-strip minimal analytic certificate. -/
theorem certificate
    (analytic :
      CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData
        period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) ∧
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).IsOpenPosMeasure ∧
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
  ⟨canonicalLorentzInteriorPhysicalMap_denseRange period hPeriod,
    analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData.certificate.1,
    analytic.toDenseParametrizedAutomaticSixCoefficientAnalyticData.certificate.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientAnalyticClosure4D
end JanusFormal
