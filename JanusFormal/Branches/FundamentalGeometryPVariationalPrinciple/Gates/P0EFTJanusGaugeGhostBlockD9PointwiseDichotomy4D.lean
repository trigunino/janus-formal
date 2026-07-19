import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9ZeroModeShortSequence4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9PointwiseDichotomy4D
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
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

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

/-- For every fixed covector, the full gauge+ghost reading lies in exactly
one of the two already certified pointwise regimes. -/
theorem fullGaugeGhostD9Reading_pointwise_dichotomy
    (covector : TangentVector3) (sector : Sector) (column : Fin 2)
    (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (covector = zeroTangent ∧
      LinearMap.range (d9GaugeGhostBlockLinearSymbol zeroTangent) =
        LinearMap.ker (d9GaugeGhostBlockCokernelProjection zeroTangent) ∧
      d9GaugeGhostBlockZeroCokernelSection
          (d9GaugeGhostBlockCokernelProjection zeroTangent
            (packGaugeGhostCoordinate
              (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point))) =
        packGaugeGhostCoordinate
          (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)) ∨
    (covector ≠ zeroTangent ∧
      (d9GaugeGhostBlockLinearSymbolInverse covector).comp
          (d9GaugeGhostBlockLinearSymbol covector) = LinearMap.id ∧
      (d9GaugeGhostBlockLinearSymbol covector).comp
          (d9GaugeGhostBlockLinearSymbolInverse covector) = LinearMap.id ∧
      d9GaugeGhostBlockCokernelProjection covector
          (packGaugeGhostCoordinate
            (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)) = 0) := by
  by_cases hCovector : covector = zeroTangent
  · left
    subst covector
    exact ⟨rfl, d9GaugeGhostBlock_zero_exact_at_coordinate,
      fullGaugeGhostD9Reading_zero_section_recovers period hPeriod gauge ghost sector column
        geometricGhost point⟩
  · right
    exact ⟨hCovector,
      d9GaugeGhostBlockLinearSymbolInverse_left covector hCovector,
      d9GaugeGhostBlockLinearSymbolInverse_right covector hCovector,
      fullGaugeGhostD9Reading_cokernel_nonzero period hPeriod gauge ghost covector hCovector
        sector column geometricGhost point⟩

/-- Dimension consequence confined to the isolated zero-mode quotient: its
pointwise cokernel has exactly the dimension of the full linear coordinate
space. -/
theorem d9GaugeGhostBlock_zero_cokernel_finrank :
    Module.finrank Real (D9GaugeGhostBlockCokernel zeroTangent) =
      Module.finrank Real D9GaugeGhostLinearCoordinate :=
  (d9GaugeGhostZeroCokernelEquiv).finrank_eq.symm

end
end P0EFTJanusGaugeGhostBlockD9PointwiseDichotomy4D
end JanusFormal
