import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGhostD9Variation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D

/-! # Common Program-P packet for the paired D9 ghosts -/

namespace JanusFormal
namespace P0EFTJanusCommonPairedD9GhostPacket4D

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
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusCommonGhostD9Variation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- One typed packet containing both true global `U(1)` ghost directions and
the true smooth D8 diffeomorphism ghost. -/
structure CommonPairedD9GhostPacket where
  u1Direction : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber
  diffeomorphismGhost : CInfinityThroatGhost period hPeriod

def CommonPairedD9GhostPacket.independentVariation
    (packet : CommonPairedD9GhostPacket period hPeriod) :
    IndependentFieldVariation period hPeriod :=
  ghostOnlyIndependentVariation period hPeriod packet.u1Direction

theorem commonPairedD9GhostPacket_injective :
    Function.Injective (fun packet : CommonPairedD9GhostPacket period hPeriod =>
      (packet.independentVariation period hPeriod,
        packet.diffeomorphismGhost)) := by
  intro first second hEqual
  have hU1 : first.u1Direction = second.u1Direction :=
    ghostOnlyIndependentVariation_injective period hPeriod
      (congrArg Prod.fst hEqual)
  have hDiff : first.diffeomorphismGhost = second.diffeomorphismGhost :=
    congrArg Prod.snd hEqual
  cases first
  cases second
  simp_all

def commonPairedD9GhostCoordinate
    (packet : CommonPairedD9GhostPacket period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) : D9PairedGhostCoordinateSpace :=
  d9PairedProgramGhostCoordinateFull period hPeriod
    (packet.independentVariation period hPeriod) column
    packet.diffeomorphismGhost point

theorem commonPairedD9GhostCoordinate_firstU1
    (packet : CommonPairedD9GhostPacket period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostFirstU1
        (commonPairedD9GhostCoordinate period hPeriod packet column point) =
      throatTrace period hPeriod GhostFiber packet.u1Direction.1 point column := by
  exact d9U1Ghost_ghostOnlyIndependentVariation period hPeriod
    packet.u1Direction .plus column point

theorem commonPairedD9GhostCoordinate_secondU1
    (packet : CommonPairedD9GhostPacket period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostSecondU1
        (commonPairedD9GhostCoordinate period hPeriod packet column point) =
      throatTrace period hPeriod GhostFiber packet.u1Direction.2 point column := by
  exact d9U1Ghost_ghostOnlyIndependentVariation period hPeriod
    packet.u1Direction .minus column point

theorem commonPairedD9GhostCoordinate_diffeomorphism
    (packet : CommonPairedD9GhostPacket period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    d9PairedGhostDiffeomorphism
        (commonPairedD9GhostCoordinate period hPeriod packet column point) =
      d9DiffeomorphismGhostCoordinates period hPeriod
        packet.diffeomorphismGhost point := by
  rfl

end
end P0EFTJanusCommonPairedD9GhostPacket4D
end JanusFormal
