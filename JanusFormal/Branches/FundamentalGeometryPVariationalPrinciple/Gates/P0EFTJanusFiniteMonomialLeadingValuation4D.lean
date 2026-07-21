import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSignedMonomialMatrixValuationCriterion4D

/-! # Leading valuation of a finite signed monomial sum -/

namespace JanusFormal
namespace P0EFTJanusFiniteMonomialLeadingValuation4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

variable {ι : Type*}

def finiteMonomialSum (tail : Finset ι) (leadingCoefficient : Real)
    (leadingOrder : Nat) (coefficient : ι → Real) (order : ι → Nat)
    (t : Real) : Real :=
  leadingCoefficient * t ^ leadingOrder +
    ∑ index ∈ tail, coefficient index * t ^ order index

def normalizedFiniteMonomialSum (tail : Finset ι) (leadingCoefficient : Real)
    (leadingOrder : Nat) (coefficient : ι → Real) (order : ι → Nat)
    (t : Real) : Real :=
  leadingCoefficient +
    ∑ index ∈ tail, coefficient index * t ^ (order index - leadingOrder)

theorem finiteMonomialSum_div_leadingPower
    (tail : Finset ι) (leadingCoefficient : Real) (leadingOrder : Nat)
    (coefficient : ι → Real) (order : ι → Nat)
    (hOrder : ∀ index ∈ tail, leadingOrder ≤ order index)
    {t : Real} (ht : t ≠ 0) :
    finiteMonomialSum tail leadingCoefficient leadingOrder coefficient order t /
        t ^ leadingOrder =
      normalizedFiniteMonomialSum tail leadingCoefficient leadingOrder
        coefficient order t := by
  rw [finiteMonomialSum, normalizedFiniteMonomialSum, add_div]
  rw [mul_div_cancel_right₀ leadingCoefficient (pow_ne_zero _ ht)]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro index hIndex
  simp [div_eq_mul_inv, pow_sub₀ t ht (hOrder index hIndex)]
  ring

private theorem finiteHigherTail_tendsto_zero
    (tail : Finset ι) (leadingOrder : Nat)
    (coefficient : ι → Real) (order : ι → Nat)
    (hOrder : ∀ index ∈ tail, leadingOrder < order index) :
    Tendsto (fun t : Real =>
      ∑ index ∈ tail, coefficient index * t ^ (order index - leadingOrder))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hSum := tendsto_finsetSum tail (fun index hIndex =>
    (positivePower_tendsto_zero
      (Nat.sub_pos_of_lt (hOrder index hIndex))).const_mul (coefficient index))
  simpa using hSum

/-- Exact dominant-term statement: after division by the minimal power, every
higher finite monomial vanishes and only the aggregated leading coefficient
remains. -/
theorem normalizedFiniteMonomialSum_tendsto_leadingCoefficient
    (tail : Finset ι) (leadingCoefficient : Real) (leadingOrder : Nat)
    (coefficient : ι → Real) (order : ι → Nat)
    (hOrder : ∀ index ∈ tail, leadingOrder < order index) :
    Tendsto
      (normalizedFiniteMonomialSum tail leadingCoefficient leadingOrder
        coefficient order)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds leadingCoefficient) := by
  convert tendsto_const_nhds.add
    (finiteHigherTail_tendsto_zero tail leadingOrder coefficient order hOrder) using 1
  · rfl
  · simp

theorem finiteMonomialSum_ratio_tendsto_leadingCoefficient
    (tail : Finset ι) (leadingCoefficient : Real) (leadingOrder : Nat)
    (coefficient : ι → Real) (order : ι → Nat)
    (hOrder : ∀ index ∈ tail, leadingOrder < order index) :
    Tendsto (fun t : Real =>
      finiteMonomialSum tail leadingCoefficient leadingOrder coefficient order t /
        t ^ leadingOrder)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds leadingCoefficient) := by
  apply (normalizedFiniteMonomialSum_tendsto_leadingCoefficient
    tail leadingCoefficient leadingOrder coefficient order hOrder).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (finiteMonomialSum_div_leadingPower tail leadingCoefficient leadingOrder
    coefficient order (fun index hIndex => (hOrder index hIndex).le) ht.ne').symm

end
end P0EFTJanusFiniteMonomialLeadingValuation4D
end JanusFormal
