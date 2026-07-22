import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D

/-!
# Compact spectral closure of the smallest physical scalar PDE package

The tangential divergence is induced by subtraction from one normal component.
The first-jet lower-order term is scalar, the shifted positive part takes values
in an arbitrary energy space, and Rellich is presented by finite coordinate
factorizations.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Smallest current full analytic data package. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  boundary : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedExternalPositiveDecompositionData
      condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData

/-- Conversion to the established scalar-energy minimal analytic package. -/
def toNormalTangentialScalarEnergyMinimalAnalyticData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy where
  boundary := analytic.boundary.toNormalTangentialRieszScalarEnergyPDEData
  condition := analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedPositiveDecomposition := analytic.shiftedPositiveDecomposition
  finiteCoordinateRellich := analytic.finiteCoordinateRellich

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.boundedResolvent period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toNormalTangentialScalarEnergyMinimalAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Smallest analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (∀ field test,
      Integrable
        (analytic.boundary.geometric.tangentialDensity field test)
        (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
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
  ⟨analytic.boundary.geometric.toCanonicalNormalSplitData
      |>.tangentialDensity_integrable,
    analytic.boundary.toNormalTangentialRieszScalarEnergyPDEData.toNormalTangentialRieszPDEData.rieszBoundaryData
      |>.boundedSmoothExtension.rieszBoundaryTrace_surjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.finiteCoordinateRellich.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticClosure4D
end JanusFormal
