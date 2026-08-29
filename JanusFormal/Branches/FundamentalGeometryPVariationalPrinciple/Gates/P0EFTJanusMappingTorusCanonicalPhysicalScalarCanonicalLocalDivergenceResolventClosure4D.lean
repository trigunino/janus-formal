import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D

/-!
# Adjoint-free spectral closure from the local divergence bridge

This endpoint combines the smallest current Green/PDE interface with the
resolvent-based final analytic theory.

Its geometric input mentions only the canonical local divergence and the
positive half-collar coordinate integral.  Its analytic input contains one
closed Lagrangian condition, one positive shifted-form decomposition and one
finite-rank Rellich approximation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
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

/-- Final spectral data over the local-divergence boundary package. -/
structure CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
    period hPeriod massSquared (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      condition referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData

/-- Conversion to the preferred adjoint-free analytic package. -/
def toResolventReducedAnalyticData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := data.boundary.toCanonicalReducedPDEData
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    data.boundary.triple.actualAdjointDomain data.condition =
      data.boundary.triple.realizationDomain data.condition :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.boundary.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.boundary.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ data.referenceParameter) :
    FiniteDimensional Real
      (data.boundary.triple.lagrangianOperatorEigenspace
        data.condition eigenvalue) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound. -/
theorem eigenvalue_ge_referenceParameter
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : data.boundary.triple.LagrangianHasEigenvalue
      data.condition eigenvalue) :
    data.referenceParameter ≤ eigenvalue :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Spectral completeness. -/
theorem spectral_complete
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((data.compactResolvent period hPeriod).bounded.ambientResolvent
          data.boundary.triple data.condition
            data.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.spectral_complete period hPeriod

/-- Local-divergence spectral certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
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
              data.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        eigenvalue ≠ data.referenceParameter →
          FiniteDimensional Real
            (data.boundary.triple.lagrangianOperatorEigenspace
              data.condition eigenvalue)) :=
  ⟨data.actualAdjointDomain_eq period hPeriod,
    data.finiteRankRellich.rellich,
    data.fredholmAlternative period hPeriod,
    data.finiteDimensional_operatorEigenspace period hPeriod⟩

end CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D
end JanusFormal
