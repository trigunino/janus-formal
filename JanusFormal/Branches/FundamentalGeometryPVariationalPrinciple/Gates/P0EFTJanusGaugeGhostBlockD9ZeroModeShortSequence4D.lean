import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9PointwiseShortSequence4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeShortSequence4D
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
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-- At zero covector, the identity inclusion has range equal to the total
kernel of the zero symbol. -/
theorem d9GaugeGhostBlock_zero_exact_at_source :
    LinearMap.range (LinearMap.id :
      D9GaugeGhostLinearCoordinate →ₗ[Real] D9GaugeGhostLinearCoordinate) =
      LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent) := by
  rw [LinearMap.range_id, d9GaugeGhostBlockLinearSymbol_ker_zero]

/-- At the next term, the zero symbol image equals the kernel of the
canonical cokernel projection. -/
theorem d9GaugeGhostBlock_zero_exact_at_coordinate :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol zeroTangent) =
      LinearMap.ker (d9GaugeGhostBlockCokernelProjection zeroTangent) :=
  d9GaugeGhostBlock_pointwise_exact_at_coordinate zeroTangent

/-- The quotient projection is onto the zero-mode cokernel. -/
theorem d9GaugeGhostBlock_zero_exact_at_cokernel :
    LinearMap.range (d9GaugeGhostBlockCokernelProjection zeroTangent) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (d9GaugeGhostBlock_pointwise_quotient_surjective zeroTangent)

/-- Canonical section of the zero-mode quotient, supplied by the previously
constructed linear equivalence. -/
def d9GaugeGhostBlockZeroCokernelSection :
    D9GaugeGhostBlockCokernel zeroTangent →ₗ[Real] D9GaugeGhostLinearCoordinate :=
  (d9GaugeGhostZeroCokernelEquiv).symm.toLinearMap

theorem d9GaugeGhostBlockZeroCokernelSection_right :
    (d9GaugeGhostBlockCokernelProjection zeroTangent).comp
        d9GaugeGhostBlockZeroCokernelSection = LinearMap.id := by
  apply LinearMap.ext
  intro c
  exact (d9GaugeGhostZeroCokernelEquiv).right_inv c

theorem d9GaugeGhostBlockZeroCokernelSection_left :
    d9GaugeGhostBlockZeroCokernelSection.comp
        (d9GaugeGhostBlockCokernelProjection zeroTangent) = LinearMap.id := by
  apply LinearMap.ext
  intro coordinate
  exact (d9GaugeGhostZeroCokernelEquiv).left_inv coordinate

/-- Complete exact/split certificate for this isolated zero-covector
four-term pointwise sequence. -/
theorem d9GaugeGhostBlock_zero_short_sequence_certificate :
    LinearMap.range (LinearMap.id :
        D9GaugeGhostLinearCoordinate →ₗ[Real] D9GaugeGhostLinearCoordinate) =
        LinearMap.ker (d9GaugeGhostBlockLinearSymbol zeroTangent) ∧
      LinearMap.range (d9GaugeGhostBlockLinearSymbol zeroTangent) =
        LinearMap.ker (d9GaugeGhostBlockCokernelProjection zeroTangent) ∧
      LinearMap.range (d9GaugeGhostBlockCokernelProjection zeroTangent) = ⊤ ∧
      (d9GaugeGhostBlockCokernelProjection zeroTangent).comp
          d9GaugeGhostBlockZeroCokernelSection = LinearMap.id ∧
      d9GaugeGhostBlockZeroCokernelSection.comp
          (d9GaugeGhostBlockCokernelProjection zeroTangent) = LinearMap.id :=
  ⟨d9GaugeGhostBlock_zero_exact_at_source,
    d9GaugeGhostBlock_zero_exact_at_coordinate,
    d9GaugeGhostBlock_zero_exact_at_cokernel,
    d9GaugeGhostBlockZeroCokernelSection_right,
    d9GaugeGhostBlockZeroCokernelSection_left⟩

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

theorem fullGaugeGhostD9Reading_zero_section_recovers
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9GaugeGhostBlockZeroCokernelSection
        (d9GaugeGhostBlockCokernelProjection zeroTangent
          (packGaugeGhostCoordinate
            (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point))) =
      packGaugeGhostCoordinate
        (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point) := by
  exact congrArg (fun f => f
    (packGaugeGhostCoordinate
      (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)))
    d9GaugeGhostBlockZeroCokernelSection_left

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeShortSequence4D
end JanusFormal
