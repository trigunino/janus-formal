import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9PointwiseCohomologyIndex4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusGaugeGhostBlockD9SymbolBridge4D
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9PointwiseShortSequence4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeShortSequence4D
open P0EFTJanusGaugeGhostBlockD9PointwiseDichotomy4D
open P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-- Dimension dichotomy of the actual pointwise cohomology term (the
cokernel of the block symbol). -/
theorem d9GaugeGhostBlock_pointwise_cokernel_finrank_dichotomy
    (covector : TangentVector3) :
    (covector = zeroTangent ∧
      Module.finrank Real (D9GaugeGhostBlockCokernel covector) =
        Module.finrank Real D9GaugeGhostLinearCoordinate) ∨
    (covector ≠ zeroTangent ∧
      Module.finrank Real (D9GaugeGhostBlockCokernel covector) = 0) := by
  by_cases hCovector : covector = zeroTangent
  · left
    subst covector
    exact ⟨rfl,
      P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D.d9GaugeGhostBlock_zero_cokernel_finrank⟩
  · right
    exact ⟨hCovector, d9GaugeGhostBlock_nonzero_cokernel_finrank covector hCovector⟩

/-- Pointwise index of the single block symbol.  This is not an index of a
global differential operator. -/
def d9GaugeGhostBlockPointwiseIndex (covector : TangentVector3) : Int :=
  (Module.finrank Real (LinearMap.ker (d9GaugeGhostBlockLinearSymbol covector)) : Int) -
    (Module.finrank Real (D9GaugeGhostBlockCokernel covector) : Int)

theorem d9GaugeGhostBlock_pointwise_index_zero (covector : TangentVector3) :
    d9GaugeGhostBlockPointwiseIndex covector = 0 := by
  by_cases hCovector : covector = zeroTangent
  · subst covector
    rw [d9GaugeGhostBlockPointwiseIndex, d9GaugeGhostBlock_zero_ker_finrank,
      P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D.d9GaugeGhostBlock_zero_cokernel_finrank]
    omega
  · rw [d9GaugeGhostBlockPointwiseIndex,
      d9GaugeGhostBlock_nonzero_ker_finrank covector hCovector,
      d9GaugeGhostBlock_nonzero_cokernel_finrank covector hCovector]
    rfl

/-- The middle homology condition of the pointwise short sequence is exact,
and its pointwise index vanishes. -/
theorem d9GaugeGhostBlock_pointwise_homology_index_certificate
    (covector : TangentVector3) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
        LinearMap.ker (d9GaugeGhostBlockCokernelProjection covector) ∧
      d9GaugeGhostBlockPointwiseIndex covector = 0 :=
  ⟨d9GaugeGhostBlock_pointwise_exact_at_coordinate covector,
    d9GaugeGhostBlock_pointwise_index_zero covector⟩

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

variable (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber)
  (ghost : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber)

theorem fullGaugeGhostD9Reading_pointwise_index_and_regime
    (covector : TangentVector3) (sector : Sector) (column : Fin 2)
    (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9GaugeGhostBlockPointwiseIndex covector = 0 ∧
      ((covector = zeroTangent ∧
        d9GaugeGhostBlockZeroCokernelSection
            (d9GaugeGhostBlockCokernelProjection zeroTangent
              (packGaugeGhostCoordinate
                (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point))) =
          packGaugeGhostCoordinate
            (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)) ∨
       (covector ≠ zeroTangent ∧
        d9GaugeGhostBlockCokernelProjection covector
            (packGaugeGhostCoordinate
              (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)) = 0)) := by
  refine ⟨d9GaugeGhostBlock_pointwise_index_zero covector, ?_⟩
  by_cases hCovector : covector = zeroTangent
  · left
    exact ⟨hCovector, fullGaugeGhostD9Reading_zeroCokernel_representative period hPeriod
      gauge ghost sector column geometricGhost point⟩
  · right
    exact ⟨hCovector, fullGaugeGhostD9Reading_cokernel_nonzero period hPeriod gauge ghost
      covector hCovector sector column geometricGhost point⟩

end
end P0EFTJanusGaugeGhostBlockD9PointwiseCohomologyIndex4D
end JanusFormal
