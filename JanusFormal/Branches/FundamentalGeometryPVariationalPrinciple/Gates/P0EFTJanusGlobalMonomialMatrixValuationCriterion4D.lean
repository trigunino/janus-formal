import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMultiExponentDiagonalSimilarity4D

/-! # Global finite matrix criterion for monomial diagonal frames -/

namespace JanusFormal
namespace P0EFTJanusGlobalMonomialMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusMultiExponentDiagonalSimilarity4D

abbrev Matrix4 := P0EFTJanusMultiExponentDiagonalSimilarity4D.Matrix4

structure NonnegativeMonomialMatrixData where
  coefficient : Fin 4 → Fin 4 → Real
  order : Fin 4 → Fin 4 → Nat
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

def transportedMatrix (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  fun i j => transportedMonomialEntry (frameExponent i) (frameExponent j)
    (data.order i j) (data.coefficient i j) t

def ActiveValuationsNonnegative (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) : Prop :=
  ∀ i j, data.coefficient i j ≠ 0 →
    frameExponent j ≤ frameExponent i + data.order i j

def valuationLimit (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) : Matrix4 :=
  fun i j => if frameExponent j = frameExponent i + data.order i j then
    data.coefficient i j else 0

theorem transportedMatrix_tendsto_of_activeValuationsNonnegative
    (data : NonnegativeMonomialMatrixData) (frameExponent : Fin 4 → Nat)
    (hValuation : ActiveValuationsNonnegative data frameExponent) :
    Tendsto (transportedMatrix data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (valuationLimit data frameExponent)) := by
  have hEntries : ∀ i j, Tendsto
      (fun t => transportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (valuationLimit data frameExponent i j)) := by
    intro i j
    by_cases hc : data.coefficient i j = 0
    · simp [transportedMatrix, transportedMonomialEntry, valuationLimit, hc]
    · have hle := hValuation i j hc
      by_cases heq : frameExponent j = frameExponent i + data.order i j
      · simpa [transportedMatrix, valuationLimit, heq] using
          transportedMonomialEntry_tendsto_coefficient heq
            (data.coefficient i j)
      · have hlt : frameExponent j < frameExponent i + data.order i j :=
          lt_of_le_of_ne hle heq
        simpa [transportedMatrix, valuationLimit, heq] using
          transportedMonomialEntry_tendsto_zero hlt (data.coefficient i j)
  have hPi : Tendsto
      (fun t i j => transportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fun i j => valuationLimit data frameExponent i j)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    exact hEntries i
  exact hPi

theorem transportedMatrix_no_finite_limit_of_negative_activeValuation
    (data : NonnegativeMonomialMatrixData) (frameExponent : Fin 4 → Nat)
    {i j : Fin 4} (hCoefficient : data.coefficient i j ≠ 0)
    (hNegative : frameExponent i + data.order i j < frameExponent j)
    (candidate : Matrix4) :
    ¬ Tendsto (transportedMatrix data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  intro hMatrix
  have hPositive : 0 < data.coefficient i j :=
    lt_of_le_of_ne (data.coefficient_nonneg i j) (Ne.symm hCoefficient)
  have hDiverges := transportedMonomialEntry_tendsto_atTop hNegative hPositive
  have hEntry := (continuous_id.matrix_elem i j).tendsto candidate
  have hFinite : Tendsto
      (fun t => transportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (candidate i j)) := hEntry.comp hMatrix
  exact not_tendsto_atTop_of_tendsto_nhds hFinite hDiverges

theorem activeValuationsNonnegative_iff_exists_finite_limit
    (data : NonnegativeMonomialMatrixData) (frameExponent : Fin 4 → Nat) :
    ActiveValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4, Tendsto (transportedMatrix data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  constructor
  · intro h
    exact ⟨valuationLimit data frameExponent,
      transportedMatrix_tendsto_of_activeValuationsNonnegative data frameExponent h⟩
  · rintro ⟨candidate, hCandidate⟩ i j hCoefficient
    by_contra hle
    exact transportedMatrix_no_finite_limit_of_negative_activeValuation
      data frameExponent hCoefficient (Nat.lt_of_not_ge hle) candidate hCandidate

end
end P0EFTJanusGlobalMonomialMatrixValuationCriterion4D
end JanusFormal
