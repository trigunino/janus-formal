import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D

/-!
# Minimal analytic closure with scalar lower-order energy

This endpoint combines the scalar-remainder energy identity with the external
positive shifted form and finite-coordinate Rellich approximation.

Its complete inputs are:

* intrinsic scalar wave and normal/tangential Green decomposition;
* one scalar energy identity `E₁ = σ <Au,u> + c ‖u‖²`;
* six bounded Cauchy-lift coefficient operators;
* one closed Lagrangian condition;
* one positive decomposition into an arbitrary energy space;
* finite-coordinate Rellich approximants.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Smallest current physical scalar analytic data package. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  boundary : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedExternalPositiveDecompositionData
      condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData

/-- Conversion to the general minimal analytic package. -/
def toMinimalAnalyticData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy where
  boundary := analytic.boundary.toNormalTangentialRieszPDEData
  condition := analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedPositiveDecomposition := analytic.shiftedPositiveDecomposition
  finiteCoordinateRellich := analytic.finiteCoordinateRellich

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.boundedResolvent period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toMinimalAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Scalar-energy minimal analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (∀ field :
      P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
        period hPeriod Real,
      P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D.canonicalPhysicalScalarFirstJetComponentEnergy
          period hPeriod field =
        analytic.boundary.energyIdentity.pairingSign *
            inner Real (analytic.boundary.geometric.greenCore.core.operator field)
              (analytic.boundary.geometric.greenCore.core.inclusion field) +
          analytic.boundary.energyIdentity.zerothCoefficient *
            ‖analytic.boundary.geometric.greenCore.core.inclusion field‖ ^ 2) ∧
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
  ⟨analytic.boundary.energyIdentity.energy_identity,
    ((analytic.boundary.toNormalTangentialRieszPDEData period hPeriod).certificate
      period hPeriod).2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.finiteCoordinateRellich.rellich,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D
end JanusFormal
