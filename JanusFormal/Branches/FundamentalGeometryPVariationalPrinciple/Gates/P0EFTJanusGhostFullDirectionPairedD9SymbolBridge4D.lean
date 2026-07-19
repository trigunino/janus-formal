import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9PairedGhostSymbolCohomology4D

namespace JanusFormal
namespace P0EFTJanusGhostFullDirectionPairedD9SymbolBridge4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusCommonGhostD9Variation4D
open P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D
open P0EFTJanusD9PairedGhostSymbolCohomology4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

variable (ghost : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber)

/-- Exact D9 scalar ghost reading of the full ghost direction. -/
theorem ghostFullDirection_d9U1Ghost
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    d9U1Ghost period hPeriod
        (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
        sector column point =
      throatTrace period hPeriod GhostFiber
        (match sector with | .plus => ghost.1 | .minus => ghost.2) point column := by
  rw [fullVariation_ghostFullDirection]
  exact d9U1Ghost_ghostOnlyIndependentVariation period hPeriod ghost sector column point

/-- The full direction supplies exactly the two traced scalar ghosts and the
independently constructed pointwise throat-diffeomorphism ghost. -/
theorem ghostFullDirection_pairedD9Coordinate
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedProgramGhostCoordinateFull period hPeriod
        (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
        column geometricGhost point =
      (throatTrace period hPeriod GhostFiber ghost.1 point column,
        (throatTrace period hPeriod GhostFiber ghost.2 point column,
          d9DiffeomorphismGhostCoordinates period hPeriod geometricGhost point)) := by
  rw [fullVariation_ghostFullDirection]
  rfl

/-- Pointwise paired principal symbol on the coordinate supplied by the full
ghost direction.  This is only a symbol-level statement. -/
theorem ghostFullDirection_pairedD9Symbol
    (covector : TangentVector3) (column : Fin 2)
    (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostPrincipalSymbol covector
        (d9PairedProgramGhostCoordinateFull period hPeriod
          (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
          column geometricGhost point) =
      normSquared covector •
        (throatTrace period hPeriod GhostFiber ghost.1 point column,
          (throatTrace period hPeriod GhostFiber ghost.2 point column,
            d9DiffeomorphismGhostCoordinates period hPeriod geometricGhost point)) := by
  rw [d9PairedGhostPrincipalSymbol_apply,
    ghostFullDirection_pairedD9Coordinate period hPeriod ghost column geometricGhost point]

/-- At a nonzero covector, the pointwise paired symbol vanishes exactly when
both traced scalar ghost readings and the geometric throat ghost vanish. -/
theorem ghostFullDirection_pairedD9Symbol_eq_zero_iff
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostPrincipalSymbol covector
        (d9PairedProgramGhostCoordinateFull period hPeriod
          (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
          column geometricGhost point) = 0 ↔
      throatTrace period hPeriod GhostFiber ghost.1 point column = 0 ∧
      throatTrace period hPeriod GhostFiber ghost.2 point column = 0 ∧
      geometricGhost point = 0 := by
  rw [d9PairedProgramGhostPrincipalSymbol_eq_zero_iff period hPeriod covector hCovector]
  simp only [ghostFullDirection_d9U1Ghost]

/-- At the zero covector, the pointwise paired symbol vanishes. -/
theorem ghostFullDirection_pairedD9Symbol_zero
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostPrincipalSymbol zeroTangent
        (d9PairedProgramGhostCoordinateFull period hPeriod
          (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
          column geometricGhost point) = 0 := by
  simp [d9PairedGhostPrincipalSymbol, zeroTangent, normSquared, tangentDot]

/-- Since the incoming range at zero covector is zero, the canonical
cohomology equivalence returns the original paired coordinate. -/
theorem ghostFullDirection_zeroModeClass_representative
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (d9PairedGhostZeroModeCohomologyEquiv).symm
        (d9PairedGhostZeroModeCohomologyProjection
          (d9PairedProgramGhostCoordinateFull period hPeriod
            (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
            column geometricGhost point)) =
      d9PairedProgramGhostCoordinateFull period hPeriod
        (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
        column geometricGhost point := by
  exact (d9PairedGhostZeroModeCohomologyEquiv).left_inv _

/-- The pointwise zero-mode class vanishes exactly when its two scalar traces
and its geometric throat-ghost value vanish. -/
theorem ghostFullDirection_zeroModeClass_eq_zero_iff
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostZeroModeCohomologyProjection
        (d9PairedProgramGhostCoordinateFull period hPeriod
          (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
          column geometricGhost point) = 0 ↔
      throatTrace period hPeriod GhostFiber ghost.1 point column = 0 ∧
      throatTrace period hPeriod GhostFiber ghost.2 point column = 0 ∧
      geometricGhost point = 0 := by
  rw [← map_zero d9PairedGhostZeroModeCohomologyProjection]
  rw [d9PairedGhostZeroModeCohomologyProjection_injective.eq_iff]
  rw [ghostFullDirection_pairedD9Coordinate period hPeriod ghost column geometricGhost point]
  simp [d9DiffeomorphismGhostCoordinates_eq_zero_iff]

/-- At a nonzero covector, the explicit inverse recovers the paired coordinate
supplied by the full ghost direction. -/
theorem ghostFullDirection_pairedD9SymbolInverse_recovers
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostPrincipalSymbolInverse covector
        (d9PairedGhostPrincipalSymbol covector
          (d9PairedProgramGhostCoordinateFull period hPeriod
            (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
            column geometricGhost point)) =
      d9PairedProgramGhostCoordinateFull period hPeriod
        (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
        column geometricGhost point :=
  d9PairedGhostPrincipalSymbolInverse_left covector hCovector _

/-- The paired coordinate from `ghostFullDirection` lies in the pointwise
symbol image, with the explicit inverse as a preimage. -/
theorem ghostFullDirection_pairedD9Coordinate_mem_range
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedProgramGhostCoordinateFull period hPeriod
        (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
        column geometricGhost point ∈
      LinearMap.range (d9PairedGhostPrincipalSymbol covector) := by
  refine ⟨d9PairedGhostPrincipalSymbolInverse covector
    (d9PairedProgramGhostCoordinateFull period hPeriod
      (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
      column geometricGhost point), ?_⟩
  exact d9PairedGhostPrincipalSymbolInverse_right covector hCovector _

/-- Consequently its class in the nonzero-covector pointwise cokernel is
zero. -/
theorem ghostFullDirection_pairedD9CokernelClass_zero
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (column : Fin 2) (geometricGhost : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostSymbolCohomologyProjection covector
        (d9PairedProgramGhostCoordinateFull period hPeriod
          (fullMatterRobinLLVariation period hPeriod (ghostFullDirection period hPeriod ghost)).1
          column geometricGhost point) = 0 :=
  d9PairedGhostSymbolCohomologyProjection_eq_zero covector hCovector _

end
end P0EFTJanusGhostFullDirectionPairedD9SymbolBridge4D
end JanusFormal
