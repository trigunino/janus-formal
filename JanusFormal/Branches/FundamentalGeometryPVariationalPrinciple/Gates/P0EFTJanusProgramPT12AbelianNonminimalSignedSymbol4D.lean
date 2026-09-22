import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D

/-! An invertible signed coordinate change for Maxwell plus nonminimal Abelian
BRST at the principal symbol. The auxiliary coordinate has order zero.
This does not identify the global H11 Hessian or an unbounded L2 domain. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D
open P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D
open scoped BigOperators

def abelianSignedCoordinates (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Fin 6 → Real :=
  ![state.potential.x, state.potential.y, state.potential.z,
    state.nakanishiLautrup.coefficient - divergenceSymbol covector state.potential,
    state.antighost.coefficient + state.ghost.coefficient,
    state.antighost.coefficient - state.ghost.coefficient]

def abelianSignedReconstruct (covector : TangentVector3)
    (coordinates : Fin 6 → Real) : D9AbelianNonminimalBRSTState where
  potential := ⟨coordinates 0, coordinates 1, coordinates 2⟩
  ghost := ⟨(coordinates 4 - coordinates 5) / 2⟩
  antighost := ⟨(coordinates 4 + coordinates 5) / 2⟩
  nakanishiLautrup := ⟨coordinates 3 +
    divergenceSymbol covector ⟨coordinates 0, coordinates 1, coordinates 2⟩⟩

theorem abelianSignedReconstruct_coordinates (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    abelianSignedReconstruct covector (abelianSignedCoordinates covector state) =
      state := by
  ext <;> simp [abelianSignedReconstruct, abelianSignedCoordinates,
    divergenceSymbol, tangentDot]

theorem abelianSignedCoordinates_reconstruct (covector : TangentVector3)
    (coordinates : Fin 6 → Real) :
    abelianSignedCoordinates covector (abelianSignedReconstruct covector coordinates) =
      coordinates := by
  funext index
  fin_cases index <;>
    simp [abelianSignedReconstruct, abelianSignedCoordinates] <;> ring

/-- All six coefficients, including independent ghost, antighost and B,
are retained. No quotient or elimination is involved. -/
def abelianSignedCoordinateEquiv (covector : TangentVector3) :
    D9AbelianNonminimalBRSTState ≃ (Fin 6 → Real) where
  toFun := abelianSignedCoordinates covector
  invFun := abelianSignedReconstruct covector
  left_inv := abelianSignedReconstruct_coordinates covector
  right_inv := abelianSignedCoordinates_reconstruct covector

theorem abelianSignedCoordinates_add (covector : TangentVector3)
    (first second : D9AbelianNonminimalBRSTState) :
    abelianSignedCoordinates covector (addD9AbelianNonminimalBRSTState first second) =
      abelianSignedCoordinates covector first + abelianSignedCoordinates covector second := by
  funext index
  fin_cases index <;>
    simp [abelianSignedCoordinates, addD9AbelianNonminimalBRSTState,
      addTangent, divergenceSymbol, tangentDot] <;> ring

theorem abelianSignedCoordinates_scale (covector : TangentVector3)
    (scalar : Real) (state : D9AbelianNonminimalBRSTState) :
    abelianSignedCoordinates covector (scaleD9AbelianNonminimalBRSTState scalar state) =
      scalar • abelianSignedCoordinates covector state := by
  funext index
  fin_cases index <;>
    simp [abelianSignedCoordinates, scaleD9AbelianNonminimalBRSTState,
      scaleTangent, divergenceSymbol, tangentDot] <;> ring

/-- Three Maxwell weights, the order-zero auxiliary weight, and two signed
ghost weights. The ghosts are unnormalized sum/difference coordinates. -/
def abelianNonminimalSignedWeight (covector : TangentVector3) : Fin 6 → Real :=
  ![normSquared covector, normSquared covector, normSquared covector,
    -1, normSquared covector / 2, -(normSquared covector / 2)]

def abelianMaxwellBRSTSymbolPairing (covector : TangentVector3)
    (first second : D9AbelianNonminimalBRSTState) : Real :=
  -tangentDot (crossProduct covector (crossProduct covector first.potential))
      second.potential + d9AbelianGaugeFermionHessian covector first second

/-- Exact congruence of the physical Maxwell symbol plus the full off-shell
BRST symbol to the mixed-order signed diagonal form. -/
theorem abelianMaxwellBRSTSymbolPairing_signed (covector : TangentVector3)
    (first second : D9AbelianNonminimalBRSTState) :
    abelianMaxwellBRSTSymbolPairing covector first second =
      ∑ index : Fin 6, abelianNonminimalSignedWeight covector index *
        abelianSignedCoordinates covector first index *
        abelianSignedCoordinates covector second index := by
  simp [abelianMaxwellBRSTSymbolPairing, d9AbelianGaugeFermionHessian,
    abelianNonminimalSignedWeight, abelianSignedCoordinates,
    Fin.sum_univ_succ, P0EFTJanusGaugeFixedPrincipalSymbols.crossProduct,
    tangentDot, divergenceSymbol, normSquared]
  ring

end
end P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D
end JanusFormal
