import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.MeanInequalities
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

/-!
# Nuclear expansion of a square-summable diagonal sandwich

A right operator diagonal in a Hilbert basis has a nuclear sandwich
`L B R` as soon as its diagonal coefficients and the images `L (B e_i)` are
square summable.  The expansion uses one rank-one term per basis vector and
the nuclear estimate is the `l2 * l2 -> l1` Holder inequality.

The separate Parseval estimate which derives square summability of
`L (B e_i)` from diagonal square summability of `L` can be supplied without
changing this reusable construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSquareSummableDiagonalSandwichNuclearExpansion4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The exact weighted `l1` condition produces an explicit nuclear rank-one
expansion of `L B R`. -/
def summableWeightedDiagonalSandwichExpansion
    {Index : Type u}
    (left middle right : E →L[Real] E)
    (basis : HilbertBasis Index Real E)
    (coefficient : Index → Real)
    (right_on_basis : ∀ index,
      right (basis index) = coefficient index • basis index)
    (weighted_nuclearSummable : Summable (fun index =>
      |coefficient index| * ‖left (middle (basis index))‖)) :
    SummableRankOneOperatorExpansion
      (left.comp (middle.comp right)) := by
  let component : Index → E →L[Real] E := fun index =>
    coefficient index •
      InnerProductSpace.rankOne Real
        (left (middle (basis index))) (basis index)
  have hNuclear : Summable (fun index =>
      |coefficient index| * ‖left (middle (basis index))‖ *
        ‖basis index‖) := by
    apply weighted_nuclearSummable.congr
    intro index
    rw [(HilbertBasis.orthonormal basis).1 index, mul_one]
  have hComponentNorm : Summable (fun index => ‖component index‖) := by
    apply hNuclear.congr
    intro index
    simp only [component, norm_smul, InnerProductSpace.norm_rankOne,
      Real.norm_eq_abs]
    ring
  have hComponent : Summable component :=
    Summable.of_norm hComponentNorm
  have hOperator :
      left.comp (middle.comp right) = ∑' index, component index := by
    apply ContinuousLinearMap.ext
    intro vector
    have hMapped :=
      (basis.hasSum_repr vector).mapL (left.comp (middle.comp right))
    have hSeries : HasSum
        (fun index => component index vector)
        (left.comp (middle.comp right) vector) := by
      apply hMapped.congr
      intro index
      simp [component, ContinuousLinearMap.comp_apply,
        right_on_basis, basis.repr_apply_apply,
        InnerProductSpace.rankOne_apply, smul_smul, mul_comm]
    rw [show
        (∑' index, component index) vector =
          ∑' index, component index vector by
      simpa only [ContinuousLinearMap.apply_apply] using
        (ContinuousLinearMap.apply Real E vector).map_tsum hComponent]
    exact hSeries.tsum_eq.symm
  refine
    { Index := Index
      coefficient := coefficient
      leftVector := fun index => left (middle (basis index))
      rightVector := basis
      summable_nuclearNorm := hNuclear
      trace_summable := ?_
      operator_eq_tsum := ?_ }
  · apply Summable.of_norm_bounded hNuclear
    intro index
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |coefficient index| *
            ‖inner Real (left (middle (basis index))) (basis index)‖ ≤
          |coefficient index| *
            (‖left (middle (basis index))‖ * ‖basis index‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = |coefficient index| * ‖left (middle (basis index))‖ *
          ‖basis index‖ := by ring
  · simpa only [component] using hOperator

/-- A square-summable diagonal right factor and a square-summable family of
left images satisfy the weighted nuclear criterion. -/
def squareSummableDiagonalSandwichExpansion
    {Index : Type u}
    (left middle right : E →L[Real] E)
    (basis : HilbertBasis Index Real E)
    (coefficient : Index → Real)
    (right_on_basis : ∀ index,
      right (basis index) = coefficient index • basis index)
    (coefficient_squareSummable :
      Summable (fun index => |coefficient index| ^ 2))
    (left_image_squareSummable :
      Summable (fun index => ‖left (middle (basis index))‖ ^ 2)) :
    SummableRankOneOperatorExpansion
      (left.comp (middle.comp right)) := by
  have hCoefficientRpow :
      Summable (fun index => |coefficient index| ^ (2 : Real)) := by
    simpa only [Real.rpow_two] using coefficient_squareSummable
  have hImageRpow :
      Summable (fun index => ‖left (middle (basis index))‖ ^ (2 : Real)) := by
    simpa only [Real.rpow_two] using left_image_squareSummable
  have hWeighted : Summable (fun index =>
      |coefficient index| * ‖left (middle (basis index))‖) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg
      (p := (2 : Real)) (q := (2 : Real))
      (f := fun index => |coefficient index|)
      (g := fun index => ‖left (middle (basis index))‖)
      Real.HolderConjugate.two_two
      (fun index => abs_nonneg (coefficient index))
      (fun index => norm_nonneg (left (middle (basis index))))
      hCoefficientRpow hImageRpow
  exact summableWeightedDiagonalSandwichExpansion
    left middle right basis coefficient right_on_basis hWeighted

/-- Public checkpoint for the exact weighted nuclear criterion. -/
theorem summableWeightedDiagonalSandwich_nuclear_gate
    {Index : Type u}
    (left middle right : E →L[Real] E)
    (basis : HilbertBasis Index Real E)
    (coefficient : Index → Real)
    (right_on_basis : ∀ index,
      right (basis index) = coefficient index • basis index)
    (weighted_nuclearSummable : Summable (fun index =>
      |coefficient index| * ‖left (middle (basis index))‖)) :
    Nonempty
      (SummableRankOneOperatorExpansion.{u, v}
        (left.comp (middle.comp right))) :=
  ⟨summableWeightedDiagonalSandwichExpansion
    left middle right basis coefficient right_on_basis
      weighted_nuclearSummable⟩

/-- Public checkpoint for the square-summable diagonal sandwich
construction. -/
theorem squareSummableDiagonalSandwich_nuclear_gate
    {Index : Type u}
    (left middle right : E →L[Real] E)
    (basis : HilbertBasis Index Real E)
    (coefficient : Index → Real)
    (right_on_basis : ∀ index,
      right (basis index) = coefficient index • basis index)
    (coefficient_squareSummable :
      Summable (fun index => |coefficient index| ^ 2))
    (left_image_squareSummable :
      Summable (fun index => ‖left (middle (basis index))‖ ^ 2)) :
    Nonempty
      (SummableRankOneOperatorExpansion.{u, v}
        (left.comp (middle.comp right))) :=
  ⟨squareSummableDiagonalSandwichExpansion (E := E) (Index := Index)
    left middle right basis coefficient right_on_basis
      coefficient_squareSummable left_image_squareSummable⟩

end
end P0EFTJanusProgramPSquareSummableDiagonalSandwichNuclearExpansion4D
end JanusFormal
