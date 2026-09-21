import Mathlib.Analysis.InnerProductSpace.l2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D

/-!
# Nuclear rank-one trace uniqueness from a Hilbert basis

Absolute nuclear summability permits a Fubini argument against any fixed
Hilbert basis.  Every rank-one presentation therefore computes the same
basis-diagonal sum, which gives presentation-independent nuclear trace data
on an arbitrary complete real Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPHilbertBasisNuclearRankOneTraceUniqueness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D

universe u v w

variable {E : Type u} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]
variable {BasisIndex : Type w}

/-- A norm-summable rank-one presentation computes the diagonal sum in any
fixed Hilbert basis. -/
theorem expansionTrace_eq_hilbertBasisDiagonal
    (basis : HilbertBasis BasisIndex Real E)
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{v} operator) :
    expansion.expansionTrace =
      ∑' index, inner Real (basis index) (operator (basis index)) := by
  let term : expansion.Index × BasisIndex → Real := fun pair ↦
    expansion.coefficient pair.1 *
      inner Real (expansion.rightVector pair.1) (basis pair.2) *
      inner Real (basis pair.2) (expansion.leftVector pair.1)
  have hHolder (index : expansion.Index) :
      Summable (fun basisIndex ↦
        ‖basis.repr (expansion.rightVector index) basisIndex‖ *
          ‖basis.repr (expansion.leftVector index) basisIndex‖) ∧
        (∑' basisIndex,
          ‖basis.repr (expansion.rightVector index) basisIndex‖ *
            ‖basis.repr (expansion.leftVector index) basisIndex‖) ≤
          ‖basis.repr (expansion.rightVector index)‖ *
            ‖basis.repr (expansion.leftVector index)‖ :=
    lp.tsum_mul_le_mul_norm
      (by simpa using Real.HolderConjugate.two_two)
      (basis.repr (expansion.rightVector index))
      (basis.repr (expansion.leftVector index))
  have hAbsoluteRow (index : expansion.Index) :
      Summable (fun basisIndex ↦ |term (index, basisIndex)|) := by
    have hScaled := (hHolder index).1.mul_left
      |expansion.coefficient index|
    apply hScaled.congr
    intro basisIndex
    simp only [term, HilbertBasis.repr_apply_apply, abs_mul,
      Real.norm_eq_abs]
    rw [real_inner_comm (basis basisIndex)
      (expansion.rightVector index)]
    ring
  have hAbsoluteRowBound (index : expansion.Index) :
      (∑' basisIndex, |term (index, basisIndex)|) ≤
        |expansion.coefficient index| *
          ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖ := by
    calc
      (∑' basisIndex, |term (index, basisIndex)|) =
          ∑' basisIndex, |expansion.coefficient index| *
            (‖basis.repr (expansion.rightVector index) basisIndex‖ *
              ‖basis.repr (expansion.leftVector index) basisIndex‖) := by
        apply tsum_congr
        intro basisIndex
        simp only [term, HilbertBasis.repr_apply_apply, abs_mul,
          Real.norm_eq_abs]
        rw [real_inner_comm (expansion.rightVector index)
          (basis basisIndex)]
        ring
      _ =
          |expansion.coefficient index| *
            (∑' basisIndex,
              ‖basis.repr (expansion.rightVector index) basisIndex‖ *
                ‖basis.repr (expansion.leftVector index) basisIndex‖) :=
        tsum_mul_left
      _ ≤ |expansion.coefficient index| *
          (‖basis.repr (expansion.rightVector index)‖ *
            ‖basis.repr (expansion.leftVector index)‖) := by
        exact mul_le_mul_of_nonneg_left (hHolder index).2 (abs_nonneg _)
      _ = |expansion.coefficient index| *
          ‖expansion.leftVector index‖ *
          ‖expansion.rightVector index‖ := by
        simp only [LinearIsometryEquiv.norm_map]
        ring
  have hAbsoluteOuter :
      Summable (fun index ↦ ∑' basisIndex, |term (index, basisIndex)|) :=
    expansion.summable_nuclearNorm.of_nonneg_of_le
      (fun index ↦ tsum_nonneg fun _ ↦ abs_nonneg _)
      hAbsoluteRowBound
  have hAbsoluteDouble :
      Summable (fun pair : expansion.Index × BasisIndex ↦ |term pair|) := by
    apply (summable_prod_of_nonneg fun _ ↦ abs_nonneg _).2
    exact ⟨hAbsoluteRow, hAbsoluteOuter⟩
  have hDouble : Summable term := by
    apply Summable.of_norm_bounded hAbsoluteDouble
    intro pair
    simp only [Real.norm_eq_abs, le_refl]
  have hRow (index : expansion.Index) :
      (∑' basisIndex, term (index, basisIndex)) =
        expansion.coefficient index *
          inner Real (expansion.leftVector index)
            (expansion.rightVector index) := by
    calc
      (∑' basisIndex, term (index, basisIndex)) =
          ∑' basisIndex, expansion.coefficient index *
            (inner Real (expansion.rightVector index) (basis basisIndex) *
              inner Real (basis basisIndex)
                (expansion.leftVector index)) := by
        apply tsum_congr
        intro basisIndex
        simp [term, mul_assoc]
      _ = expansion.coefficient index *
          (∑' basisIndex,
            inner Real (expansion.rightVector index) (basis basisIndex) *
              inner Real (basis basisIndex)
                (expansion.leftVector index)) := tsum_mul_left
      _ = expansion.coefficient index *
          inner Real (expansion.rightVector index)
            (expansion.leftVector index) := by
        rw [basis.tsum_inner_mul_inner]
      _ = expansion.coefficient index *
          inner Real (expansion.leftVector index)
            (expansion.rightVector index) := by
        rw [real_inner_comm]
  have hComponents : Summable expansion.component :=
    Summable.of_norm expansion.component_norm_summable
  have hOperator : operator = ∑' index, expansion.component index := by
    simpa [SummableRankOneOperatorExpansion.component] using
      expansion.operator_eq_tsum
  have hColumn (basisIndex : BasisIndex) :
      (∑' index, term (index, basisIndex)) =
        inner Real (basis basisIndex) (operator (basis basisIndex)) := by
    let diagonalFunctional : (E →L[Real] E) →L[Real] Real :=
      (innerSL Real (basis basisIndex)).comp
        (ContinuousLinearMap.apply Real E (basis basisIndex))
    have hMapped := diagonalFunctional.map_tsum hComponents
    calc
      (∑' index, term (index, basisIndex)) =
          ∑' index, diagonalFunctional (expansion.component index) := by
        apply tsum_congr
        intro index
        simp [term, diagonalFunctional,
          SummableRankOneOperatorExpansion.component,
          InnerProductSpace.rankOne_apply, mul_assoc]
      _ = diagonalFunctional (∑' index, expansion.component index) :=
        hMapped.symm
      _ = diagonalFunctional operator := by rw [← hOperator]
      _ = inner Real (basis basisIndex) (operator (basis basisIndex)) := by
        simp [diagonalFunctional]
  unfold SummableRankOneOperatorExpansion.expansionTrace
  calc
    (∑' index, expansion.coefficient index *
        inner Real (expansion.leftVector index)
          (expansion.rightVector index)) =
        ∑' index, ∑' basisIndex, term (index, basisIndex) := by
      apply tsum_congr
      intro index
      exact (hRow index).symm
    _ = ∑' basisIndex, ∑' index, term (index, basisIndex) := by
      have hSwapped : Summable
          (fun pair : BasisIndex × expansion.Index ↦ term pair.swap) :=
        hDouble.prod_symm
      exact Summable.tsum_comm hSwapped
    _ = ∑' basisIndex,
        inner Real (basis basisIndex) (operator (basis basisIndex)) := by
      apply tsum_congr
      exact hColumn

/-- Every complete real Hilbert space with a Hilbert basis has canonical
uniqueness of absolutely norm-summable rank-one traces. -/
def hilbertBasisNuclearRankOneTraceUniquenessData
    (basis : HilbertBasis BasisIndex Real E) :
    NuclearRankOneTraceUniquenessData.{u, v} (E := E) where
  expansionTrace_eq := by
    intro operator first second
    rw [expansionTrace_eq_hilbertBasisDiagonal basis first,
      expansionTrace_eq_hilbertBasisDiagonal basis second]

end
end P0EFTJanusProgramPHilbertBasisNuclearRankOneTraceUniqueness4D
end JanusFormal
