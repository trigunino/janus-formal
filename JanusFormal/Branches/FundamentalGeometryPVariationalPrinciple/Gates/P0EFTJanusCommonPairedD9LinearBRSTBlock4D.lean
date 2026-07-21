import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9GhostPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeBRST4D

/-! # Linear BRST block on the common paired D9 ghost packet -/

namespace JanusFormal
namespace P0EFTJanusCommonPairedD9LinearBRSTBlock4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusCommonPairedD9GhostPacket4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private def zeroThroatGhost : CInfinityThroatGhost period hPeriod where
  toFun := fun _ => 0
  contMDiff_toFun := Bundle.contMDiff_zeroSection Real _

/-- Direct block of the two genuine abelian gauge BRST states and the
linearized diffeomorphism-ghost slot.  The latter obeys `s c = 0`; no nonlinear
ordinary-ghost BRST differential is claimed. -/
@[ext]
structure CommonPairedD9LinearBRSTBlock where
  firstU1 : AbelianBRSTState period hPeriod
  secondU1 : AbelianBRSTState period hPeriod
  diffeomorphismGhost : CInfinityThroatGhost period hPeriod

def zeroCommonPairedD9LinearBRSTBlock :
    CommonPairedD9LinearBRSTBlock period hPeriod where
  firstU1 := zeroBRSTState period hPeriod
  secondU1 := zeroBRSTState period hPeriod
  diffeomorphismGhost := zeroThroatGhost period hPeriod

/-- Componentwise linear BRST differential. -/
def commonPairedD9LinearBRSTDifferential
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    CommonPairedD9LinearBRSTBlock period hPeriod where
  firstU1 := brstDifferential period hPeriod state.firstU1
  secondU1 := brstDifferential period hPeriod state.secondU1
  diffeomorphismGhost := zeroThroatGhost period hPeriod

theorem commonPairedD9LinearBRSTDifferential_square_zero
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    commonPairedD9LinearBRSTDifferential period hPeriod
        (commonPairedD9LinearBRSTDifferential period hPeriod state) =
      zeroCommonPairedD9LinearBRSTBlock period hPeriod := by
  apply CommonPairedD9LinearBRSTBlock.ext
  · exact brstDifferential_square_zero period hPeriod state.firstU1
  · exact brstDifferential_square_zero period hPeriod state.secondU1
  · rfl

/-- Forget potentials and retain exactly the three ghost slots consumed by
the common D9 coordinate bridge. -/
def CommonPairedD9LinearBRSTBlock.toGhostPacket
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    CommonPairedD9GhostPacket period hPeriod where
  u1Direction := (state.firstU1.ghost, state.secondU1.ghost)
  diffeomorphismGhost := state.diffeomorphismGhost

/-- A common packet is faithfully lifted by choosing zero gauge potentials. -/
def CommonPairedD9GhostPacket.toLinearBRSTBlock
    (packet : CommonPairedD9GhostPacket period hPeriod) :
    CommonPairedD9LinearBRSTBlock period hPeriod where
  firstU1 := { potential := 0, ghost := packet.u1Direction.1 }
  secondU1 := { potential := 0, ghost := packet.u1Direction.2 }
  diffeomorphismGhost := packet.diffeomorphismGhost

@[simp]
theorem toLinearBRSTBlock_toGhostPacket
    (packet : CommonPairedD9GhostPacket period hPeriod) :
    (CommonPairedD9GhostPacket.toLinearBRSTBlock period hPeriod packet).toGhostPacket
        period hPeriod =
      packet := by
  cases packet
  rfl

/-- After one linear BRST step all D9 ghost coordinates vanish: the two
abelian ghost differentials and the linearized diffeomorphism-ghost
differential are zero on their ghost slots. -/
theorem commonPairedD9LinearBRSTDifferential_d9Coordinate
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) :
    commonPairedD9GhostCoordinate period hPeriod
        ((commonPairedD9LinearBRSTDifferential period hPeriod state).toGhostPacket
          period hPeriod) column point = 0 := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

end
end P0EFTJanusCommonPairedD9LinearBRSTBlock4D
end JanusFormal
