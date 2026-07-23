import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticClosure4D

/-!
# Minimal analytic closure with canonical `L²` coefficient operators

This endpoint combines the smallest canonical-`L²`-operator PDE package with
direct shifted coercivity and finite-coordinate Rellich approximation.  The
former external positive decomposition remains as a sufficient compatibility
interface.

The full analytic input no longer contains pointwise coefficient functions,
`MemLp` proofs, coefficient constants, residual integrability, normal trace
regularity, adjoint regularity or finite-range proofs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Smallest canonical-`L²` analytic input with coercivity supplied directly. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData

/-- Conversion to the direct-coercive normal/tangential analytic core. -/
def toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
      period hPeriod massSquared where
  boundary :=
    analytic.boundary.toCanonicalNormalRieszScalarEnergyPDEData period hPeriod
      |>.toNormalTangentialRieszScalarEnergyPDEData period hPeriod
      |>.toNormalTangentialRieszPDEData period hPeriod
  condition := analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  finiteCoordinateRellich := analytic.finiteCoordinateRellich

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).boundedResolvent period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).compactResolvent period hPeriod

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).fredholmAlternative
      period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).eigenvalue_ge_referenceParameter
      period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness. -/
theorem spectral_complete
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    period hPeriod).spectral_complete period hPeriod

/-- Canonical-`L²` direct-coercive analytic certificate. -/
theorem certificate
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    (∀ index boundary,
      MemLp
        (analytic.boundary.eulerCoefficientOperators.coefficient
          period hPeriod index boundary)
        (2 : ENNReal)
        (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
          period)) ∧
      Function.Surjective analytic.boundary.completedBoundaryTrace ∧
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
  ⟨analytic.boundary.eulerCoefficientOperators.coefficient_memLp period hPeriod,
    (analytic.boundary.certificate period hPeriod).2.2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.finiteCoordinateRellich.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData

/-- Smallest current full analytic input with canonical `L²` coefficients. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  boundary : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedExternalPositiveDecompositionData
      condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData

/-- The positive-decomposition package factors through direct coercivity. -/
def toDirectCoerciveMinimalAnalyticData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
      period hPeriod massSquared where
  boundary := analytic.boundary
  condition := analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive :=
    analytic.shiftedPositiveDecomposition.toShiftedFormCoerciveData
      analytic.boundary.triple analytic.condition analytic.referenceParameter
  finiteCoordinateRellich := analytic.finiteCoordinateRellich

/-- Conversion to the former smallest analytic package. -/
def toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy where
  boundary := analytic.boundary.toCanonicalNormalRieszScalarEnergyPDEData
  condition := analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedPositiveDecomposition := analytic.shiftedPositiveDecomposition
  finiteCoordinateRellich := analytic.finiteCoordinateRellich

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).boundedResolvent period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).compactResolvent period hPeriod

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).fredholmAlternative
      period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).eigenvalue_ge_referenceParameter
      period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    period hPeriod).spectral_complete period hPeriod

/-- Canonical-`L²`-operator analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (∀ index boundary,
      MemLp
        (analytic.boundary.eulerCoefficientOperators.coefficient
          period hPeriod index boundary)
        (2 : ENNReal)
        (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
          period)) ∧
      Function.Surjective analytic.boundary.completedBoundaryTrace ∧
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
  ⟨analytic.boundary.eulerCoefficientOperators.coefficient_memLp period hPeriod,
    (analytic.boundary.certificate period hPeriod).2.2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.finiteCoordinateRellich.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D
end JanusFormal
