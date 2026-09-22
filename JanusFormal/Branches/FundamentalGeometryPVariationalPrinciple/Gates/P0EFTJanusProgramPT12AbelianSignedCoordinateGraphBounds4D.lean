import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D

/-! The signed symbol shear is uniformly controlled with the longitudinal
graph norm. It is not uniformly bounded in the unweighted coefficient norm.
These are modewise estimates, not a geometric Fourier realization. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianSignedCoordinateGraphBounds4D

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D
open P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D

def abelianRawSizeSq (state : D9AbelianNonminimalBRSTState) : Real :=
  tangentDot state.potential state.potential + state.nakanishiLautrup.coefficient ^ 2 +
    state.ghost.coefficient ^ 2 + state.antighost.coefficient ^ 2

def abelianLongitudinalGraphSizeSq (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Real :=
  abelianRawSizeSq state + (divergenceSymbol covector state.potential) ^ 2

def abelianSignedGraphSizeSq (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Real :=
  (∑ index : Fin 6, (abelianSignedCoordinates covector state index) ^ 2) +
    (divergenceSymbol covector state.potential) ^ 2

private theorem coordinate_size (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    (∑ index : Fin 6, (abelianSignedCoordinates covector state index) ^ 2) =
      tangentDot state.potential state.potential +
        (state.nakanishiLautrup.coefficient - divergenceSymbol covector state.potential) ^ 2 +
        2 * state.ghost.coefficient ^ 2 + 2 * state.antighost.coefficient ^ 2 := by
  simp [abelianSignedCoordinates, Fin.sum_univ_succ, tangentDot]
  ring

private theorem potential_size_nonneg (state : D9AbelianNonminimalBRSTState) :
    0 ≤ tangentDot state.potential state.potential := by
  unfold tangentDot
  nlinarith [sq_nonneg state.potential.x, sq_nonneg state.potential.y,
    sq_nonneg state.potential.z]

theorem abelianSignedCoordinates_graph_bound (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    abelianSignedGraphSizeSq covector state ≤
      3 * abelianLongitudinalGraphSizeSq covector state := by
  unfold abelianSignedGraphSizeSq abelianLongitudinalGraphSizeSq abelianRawSizeSq
  rw [coordinate_size]
  nlinarith [potential_size_nonneg state,
    sq_nonneg state.nakanishiLautrup.coefficient, sq_nonneg state.ghost.coefficient,
    sq_nonneg state.antighost.coefficient,
    sq_nonneg (state.nakanishiLautrup.coefficient + divergenceSymbol covector state.potential)]

theorem abelianSignedCoordinates_inverse_graph_bound (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    abelianLongitudinalGraphSizeSq covector state ≤
      3 * abelianSignedGraphSizeSq covector state := by
  unfold abelianSignedGraphSizeSq abelianLongitudinalGraphSizeSq abelianRawSizeSq
  rw [coordinate_size]
  nlinarith [potential_size_nonneg state,
    sq_nonneg state.ghost.coefficient, sq_nonneg state.antighost.coefficient,
    sq_nonneg (state.nakanishiLautrup.coefficient - divergenceSymbol covector state.potential),
    sq_nonneg (state.nakanishiLautrup.coefficient - 2 * divergenceSymbol covector state.potential)]

def unitLongitudinalAbelianState : D9AbelianNonminimalBRSTState where
  potential := ⟨1, 0, 0⟩
  ghost := ⟨0⟩
  antighost := ⟨0⟩
  nakanishiLautrup := ⟨0⟩

/-- A unit input at frequency n acquires an auxiliary coordinate -n. -/
theorem abelianSignedCoordinates_unit_growth (frequency : Nat) :
    abelianRawSizeSq unitLongitudinalAbelianState = 1 ∧
      (∑ index : Fin 6,
        (abelianSignedCoordinates ⟨frequency, 0, 0⟩ unitLongitudinalAbelianState index) ^ 2) =
        1 + (frequency : Real) ^ 2 := by
  constructor
  · norm_num [abelianRawSizeSq, unitLongitudinalAbelianState, tangentDot]
  · rw [coordinate_size]
    simp [unitLongitudinalAbelianState, tangentDot, divergenceSymbol]

/-- Hence finite-symbol invertibility cannot be extended by claiming a
uniform bound on the bare L2 coefficient norm. -/
theorem abelianSignedCoordinates_no_uniform_raw_bound :
    ¬ ∃ bound : Real, ∀ (frequency : Nat) (state : D9AbelianNonminimalBRSTState),
      (∑ index : Fin 6,
        (abelianSignedCoordinates ⟨frequency, 0, 0⟩ state index) ^ 2) ≤
        bound * abelianRawSizeSq state := by
  rintro ⟨bound, hBound⟩
  obtain ⟨frequency, hFrequency⟩ := exists_nat_gt (max bound 1)
  have hTest := hBound frequency unitLongitudinalAbelianState
  rcases abelianSignedCoordinates_unit_growth frequency with ⟨hRaw, hSigned⟩
  rw [hRaw, hSigned, mul_one] at hTest
  have hLarge : bound < (frequency : Real) := lt_of_le_of_lt (le_max_left _ _) hFrequency
  have hOne : (1 : Real) < frequency := lt_of_le_of_lt (le_max_right _ _) hFrequency
  nlinarith

end
end P0EFTJanusProgramPT12AbelianSignedCoordinateGraphBounds4D
end JanusFormal
