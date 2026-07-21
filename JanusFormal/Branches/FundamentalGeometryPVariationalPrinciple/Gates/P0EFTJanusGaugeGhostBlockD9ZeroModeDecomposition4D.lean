import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9PointwiseEuler4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9ZeroModeDecomposition4D
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
open P0EFTJanusGaugeGhostBlockD9ZeroModeShortSequence4D
open P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
open P0EFTJanusGaugeGhostBlockD9PointwiseEuler4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-- The zero-mode cokernel dimension splits additively into its three gauge
coordinates and five paired ghost coordinates. -/
theorem d9GaugeGhostBlock_zero_cokernel_finrank_decomposition :
    Module.finrank Real (D9GaugeGhostBlockCokernel zeroTangent) =
      Module.finrank Real (Real × Real × Real) +
        Module.finrank Real D9PairedGhostCoordinateSpace := by
  rw [d9GaugeGhostBlock_zero_cokernel_finrank]
  exact Module.finrank_prod

/-- Accordingly, the Euler value of the uncompleted three-term zero-mode
sequence is the sum of the gauge and ghost coordinate dimensions. -/
theorem d9GaugeGhostBlock_zero_pointwiseEuler_decomposition :
    d9GaugeGhostBlockPointwiseEuler zeroTangent =
      (Module.finrank Real (Real × Real × Real) : Int) +
        Module.finrank Real D9PairedGhostCoordinateSpace := by
  rw [d9GaugeGhostBlock_zero_pointwiseEuler]
  norm_cast
  exact Module.finrank_prod

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

/-- Projecting the zero-mode section recovery onto the gauge block returns
the exact packed D9 gauge reading. -/
theorem fullGaugeGhostD9Reading_zero_section_gauge
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9GaugeGhostBlockZeroCokernelSection
        (d9GaugeGhostBlockCokernelProjection zeroTangent
          (packGaugeGhostCoordinate
            (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)))).1 =
      (let reading := (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column
        geometricGhost point).1
       (reading.x, reading.y, reading.z)) := by
  have h := fullGaugeGhostD9Reading_zero_section_recovers period hPeriod gauge ghost sector column
    geometricGhost point
  exact congrArg Prod.fst h

/-- Projecting the same recovery onto the ghost block returns the exact
paired D9 ghost coordinate supplied by `ghostFullDirection`. -/
theorem fullGaugeGhostD9Reading_zero_section_ghost
    (sector : Sector) (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9GaugeGhostBlockZeroCokernelSection
        (d9GaugeGhostBlockCokernelProjection zeroTangent
          (packGaugeGhostCoordinate
            (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point)))).2 =
      (fullGaugeGhostD9Reading period hPeriod gauge ghost sector column geometricGhost point).2 := by
  have h := fullGaugeGhostD9Reading_zero_section_recovers period hPeriod gauge ghost sector column
    geometricGhost point
  exact congrArg Prod.snd h

end
end P0EFTJanusGaugeGhostBlockD9ZeroModeDecomposition4D
end JanusFormal
