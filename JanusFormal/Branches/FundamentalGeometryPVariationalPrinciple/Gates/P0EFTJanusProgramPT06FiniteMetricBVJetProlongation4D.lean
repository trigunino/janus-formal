import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

/-!
# Finite physical metric-BV prolongation on the T06 spatial jet tower

The existing nonzero square-zero BV differential for the finite positive
throat-metric phase is prolonged coefficientwise to every genuine spatial
Finsupp jet.  The prolongation commutes definitionally with truncation and
formal total derivatives and remains parity odd and square-zero.

This is a physical finite metric-BV submodel.  It does not define a BRST/BV
action on the complete eleven-component T02 physical value carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FiniteMetricBVJetProlongation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

/-- Genuine spatial jets valued in the already constructed finite physical
metric-BV phase. -/
abbrev ProgramPT06FiniteMetricBVSpatialJet (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet FiniteMetricBVPhase order

/-- Coefficientwise prolongation of the finite physical metric-BV
differential to every spatial jet order. -/
def programPT06FiniteMetricBVJetBRST (order : Nat) :
    ProgramPT06FiniteMetricBVSpatialJet order →ₗ[Real]
      ProgramPT06FiniteMetricBVSpatialJet order :=
  LinearMap.pi fun index => finiteMetricBVBRST.comp (LinearMap.proj index)

@[simp]
theorem programPT06FiniteMetricBVJetBRST_apply
    (order : Nat) (jet : ProgramPT06FiniteMetricBVSpatialJet order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06FiniteMetricBVJetBRST order jet index =
      finiteMetricBVBRST (jet index) :=
  rfl

/-- Nilpotence survives at every finite jet order. -/
theorem programPT06FiniteMetricBVJetBRST_square_zero
    (order : Nat) (jet : ProgramPT06FiniteMetricBVSpatialJet order) :
    programPT06FiniteMetricBVJetBRST order
        (programPT06FiniteMetricBVJetBRST order jet) = 0 := by
  funext index
  exact finiteMetricBVBRST_square_zero (jet index)

/-- The prolonged BV differential is natural under jet truncation. -/
theorem programPT06FiniteMetricBVJetBRST_commutes_truncation
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : ProgramPT06FiniteMetricBVSpatialJet higher) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06FiniteMetricBVJetBRST higher jet) =
      programPT06FiniteMetricBVJetBRST lower
        (truncateThroatSpatialMultiindexJet hOrder jet) := by
  rfl

/-- The prolonged BV differential commutes with every formal spatial total
derivative. -/
theorem programPT06FiniteMetricBVJetBRST_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (jet : ProgramPT06FiniteMetricBVSpatialJet (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06FiniteMetricBVJetBRST (order + 1) jet) =
      programPT06FiniteMetricBVJetBRST order
        (throatSpatialTotalDerivative direction jet) := by
  rfl

/-- In particular, the physical BV action on `J⁴` restricts exactly to its
action on the `J²` carrier used by the second-order Euler calculation. -/
theorem programPT06FiniteMetricBVJetBRST_J4_to_J2
    (jet : ProgramPT06FiniteMetricBVSpatialJet 4) :
    truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4)
        (programPT06FiniteMetricBVJetBRST 4 jet) =
      programPT06FiniteMetricBVJetBRST 2
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) := by
  exact programPT06FiniteMetricBVJetBRST_commutes_truncation (by omega) jet

/-- Coefficientwise BV parity on spatial jets. -/
def programPT06FiniteMetricBVJetParity (order : Nat)
    (jet : ProgramPT06FiniteMetricBVSpatialJet order) :
    ProgramPT06FiniteMetricBVSpatialJet order :=
  fun index => finiteMetricBVParity (jet index)

/-- Coefficientwise BV parity remains involutive. -/
theorem programPT06FiniteMetricBVJetParity_involutive
    (order : Nat) (jet : ProgramPT06FiniteMetricBVSpatialJet order) :
    programPT06FiniteMetricBVJetParity order
        (programPT06FiniteMetricBVJetParity order jet) = jet := by
  funext index
  exact finiteMetricBVParity_involutive (jet index)

/-- The prolonged jet differential retains the odd parity of the physical
finite metric-BV differential. -/
theorem programPT06FiniteMetricBVJetBRST_parity_odd
    (order : Nat) (jet : ProgramPT06FiniteMetricBVSpatialJet order) :
    programPT06FiniteMetricBVJetParity order
        (programPT06FiniteMetricBVJetBRST order jet) =
      -programPT06FiniteMetricBVJetBRST order
        (programPT06FiniteMetricBVJetParity order jet) := by
  funext index
  exact finiteMetricBVBRST_parity_odd (jet index)

end
end P0EFTJanusProgramPT06FiniteMetricBVJetProlongation4D
end JanusFormal
