import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D

/-!
# Compact spectral closure from the normal/tangential Riesz package

The local geometric input is the intrinsic wave together with a
normal/tangential divergence split.  The completed Cauchy trace is reconstructed
by Riesz duality from the bounded Cauchy extension.

One positive shifted-form decomposition and one finite-rank Rellich scheme then
give actual self-adjointness, compact resolvent, Fredholm alternative, finite
multiplicity, orthogonality, spectral completeness and the lower spectral bound.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final analytic data over the normal/tangential Riesz boundary package. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      condition referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData

/-- Conversion to the generic intrinsic-wave Riesz resolvent endpoint. -/
def toIntrinsicWaveRieszResolventData
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared where
  boundary := data.boundary.toIntrinsicWaveRieszReducedPDEData
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :
    data.boundary.triple.actualAdjointDomain data.condition =
      data.boundary.triple.realizationDomain data.condition :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.boundary.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.boundary.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ data.referenceParameter) :
    FiniteDimensional Real
      (data.boundary.triple.lagrangianOperatorEigenspace
        data.condition eigenvalue) :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Eigenfields with distinct eigenvalues are orthogonal in physical bulk
`L²`. -/
theorem eigenfields_orthogonal
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (first : data.boundary.triple.lagrangianOperatorEigenspace
      data.condition firstEigenvalue)
    (second : data.boundary.triple.lagrangianOperatorEigenspace
      data.condition secondEigenvalue) :
    inner Real
        (data.boundary.triple.lagrangianInclusion data.condition first.1)
        (data.boundary.triple.lagrangianInclusion data.condition second.1) = 0 :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.eigenfields_orthogonal period hPeriod
      firstEigenvalue secondEigenvalue hDistinct first second

/-- Every eigenvalue lies above the positive-decomposition reference. -/
theorem eigenvalue_ge_referenceParameter
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : data.boundary.triple.LagrangianHasEigenvalue
      data.condition eigenvalue) :
    data.referenceParameter ≤ eigenvalue :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness of the compact ambient resolvent. -/
theorem spectral_complete
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((data.compactResolvent period hPeriod).bounded.ambientResolvent
          (data.boundary.triple period hPeriod)
          data.condition data.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (data.toIntrinsicWaveRieszResolventData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Normal/tangential Riesz spectral certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :
    (∀ field test,
      (∫ parameter,
        data.boundary.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
      Function.Surjective data.boundary.completedBoundaryTrace ∧
      data.boundary.triple.actualAdjointDomain data.condition =
        data.boundary.triple.realizationDomain data.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.boundary.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.boundary.triple.LagrangianResolventPoint
              data.condition spectralParameter) :=
  ⟨data.boundary.geometric.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    (data.boundary.certificate period hPeriod).2.2.2.1,
    data.actualAdjointDomain_eq period hPeriod,
    data.finiteRankRellich.rellich period hPeriod,
    data.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D
end JanusFormal
