import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9GhostPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGradedDiffeomorphismGhostTensor4D

/-! # Separate graded D8 ghost packet -/

namespace JanusFormal
namespace P0EFTJanusCommonD8GradedGhostPacket4D

set_option autoImplicit false
noncomputable section

open scoped TensorProduct
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedDiffeomorphismGhostTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The common two U(1) directions together with the genuinely graded global
D8 diffeomorphism ghost.  This is deliberately distinct from the ordinary
fixed-throat `CInfinityThroatGhost` packet. -/
@[ext]
structure CommonD8GradedGhostPacket where
  u1Direction : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber
  diffeomorphismGhost : GradedDiffeomorphismGhostModule period hPeriod

/-- Coefficient BRST differential on the graded slot; the abelian U(1) ghost
slots have zero differential. -/
def commonD8GradedGhostDifferential
    (packet : CommonD8GradedGhostPacket period hPeriod) :
    CommonD8GradedGhostPacket period hPeriod where
  u1Direction := 0
  diffeomorphismGhost :=
    gradedGhostCoefficientDifferential period hPeriod
      packet.diffeomorphismGhost

theorem commonD8GradedGhostDifferential_square_zero
    (packet : CommonD8GradedGhostPacket period hPeriod) :
    commonD8GradedGhostDifferential period hPeriod
        (commonD8GradedGhostDifferential period hPeriod packet) =
      { u1Direction := 0, diffeomorphismGhost := 0 } := by
  apply CommonD8GradedGhostPacket.ext
  · rfl
  · exact gradedGhostCoefficientDifferential_sq period hPeriod
      packet.diffeomorphismGhost

/-- Packet containing the already-constructed quadratic graded Lie-bracket
term for two genuine global smooth D8 tangent ghosts. -/
def commonD8GradedQuadraticGhostPacket
    (u1Direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    CommonD8GradedGhostPacket period hPeriod where
  u1Direction := u1Direction
  diffeomorphismGhost :=
    gradedQuadraticGhostBracketTerm period hPeriod first second

@[simp]
theorem commonD8GradedQuadraticGhostPacket_diffeomorphism
    (u1Direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    (commonD8GradedQuadraticGhostPacket period hPeriod u1Direction
      first second).diffeomorphismGhost =
        gradedQuadraticGhostBracketTerm period hPeriod first second := rfl

/-- Nilpotence applies in particular to the genuine quadratic graded term. -/
theorem commonD8GradedQuadraticGhostPacket_square_zero
    (u1Direction : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    commonD8GradedGhostDifferential period hPeriod
        (commonD8GradedGhostDifferential period hPeriod
          (commonD8GradedQuadraticGhostPacket period hPeriod u1Direction
            first second)) =
      { u1Direction := 0, diffeomorphismGhost := 0 } :=
  commonD8GradedGhostDifferential_square_zero period hPeriod _

end
end P0EFTJanusCommonD8GradedGhostPacket4D
end JanusFormal
