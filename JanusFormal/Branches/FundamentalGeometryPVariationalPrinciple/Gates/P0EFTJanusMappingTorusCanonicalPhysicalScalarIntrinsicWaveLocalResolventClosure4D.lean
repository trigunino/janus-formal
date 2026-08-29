import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D

/-!
# Adjoint-free spectral closure from intrinsic wave and local Green data

This endpoint carries the intrinsic-wave/local-divergence PDE package to the
complete resolvent-based spectral theory.  The geometric operator input is a
global wave representative; the Green input is a local product/collar identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalResolventClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final analytic data over the intrinsic-wave local PDE package. -/
structure CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
    period hPeriod massSquared (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      condition referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveLocalResolventData

/-- Conversion to the local-divergence resolvent package. -/
def toCanonicalLocalDivergenceResolventData
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D.CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := data.boundary.toCanonicalLocalDivergenceReducedPDEData
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    data.boundary.triple.actualAdjointDomain data.condition =
      data.boundary.triple.realizationDomain data.condition :=
  (data.toCanonicalLocalDivergenceResolventData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalLocalDivergenceResolventData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.boundary.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.boundary.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  (data.toCanonicalLocalDivergenceResolventData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ data.referenceParameter) :
    FiniteDimensional Real
      (data.boundary.triple.lagrangianOperatorEigenspace
        data.condition eigenvalue) :=
  (data.toCanonicalLocalDivergenceResolventData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : data.boundary.triple.LagrangianHasEigenvalue
      data.condition eigenvalue) :
    data.referenceParameter ≤ eigenvalue :=
  (data.toCanonicalLocalDivergenceResolventData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Intrinsic-wave local spectral certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    data.boundary.triple.actualAdjointDomain data.condition =
        data.boundary.triple.realizationDomain data.condition ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.boundary.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.boundary.triple.LagrangianResolventPoint
              data.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        eigenvalue ≠ data.referenceParameter →
          FiniteDimensional Real
            (data.boundary.triple.lagrangianOperatorEigenspace
              data.condition eigenvalue)) :=
  ⟨data.actualAdjointDomain_eq period hPeriod,
    data.fredholmAlternative period hPeriod,
    data.finiteDimensional_operatorEigenspace period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveLocalResolventData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalResolventClosure4D
end JanusFormal
