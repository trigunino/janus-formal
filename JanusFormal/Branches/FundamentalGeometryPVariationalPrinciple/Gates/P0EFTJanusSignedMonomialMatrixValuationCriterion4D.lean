import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMonomialMatrixValuationCriterion4D

/-! # Signed monomial matrix valuation criterion -/

namespace JanusFormal
namespace P0EFTJanusSignedMonomialMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusMultiExponentDiagonalSimilarity4D

abbrev Matrix4 := P0EFTJanusMultiExponentDiagonalSimilarity4D.Matrix4

theorem transportedMonomialEntry_tendsto_atBot
    {rowExponent columnExponent order : Nat}
    (h : rowExponent + order < columnExponent) {coefficient : Real}
    (hCoefficient : coefficient < 0) :
    Tendsto (transportedMonomialEntry rowExponent columnExponent order coefficient)
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
  have hPositive := transportedMonomialEntry_tendsto_atTop h (neg_pos.mpr hCoefficient)
  have hNeg := tendsto_neg_atTop_atBot.comp hPositive
  apply hNeg.congr'
  filter_upwards with t
  simp [transportedMonomialEntry]

structure SignedMonomialMatrixData where
  coefficient : Fin 4 → Fin 4 → Real
  order : Fin 4 → Fin 4 → Nat

def signedTransportedMatrix (data : SignedMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  fun i j => transportedMonomialEntry (frameExponent i) (frameExponent j)
    (data.order i j) (data.coefficient i j) t

def SignedActiveValuationsNonnegative (data : SignedMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) : Prop :=
  ∀ i j, data.coefficient i j ≠ 0 →
    frameExponent j ≤ frameExponent i + data.order i j

def signedValuationLimit (data : SignedMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) : Matrix4 :=
  fun i j => if frameExponent j = frameExponent i + data.order i j then
    data.coefficient i j else 0

theorem signedTransportedMatrix_tendsto
    (data : SignedMonomialMatrixData) (frameExponent : Fin 4 → Nat)
    (hValuation : SignedActiveValuationsNonnegative data frameExponent) :
    Tendsto (signedTransportedMatrix data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (signedValuationLimit data frameExponent)) := by
  have hEntries : ∀ i j, Tendsto
      (fun t => signedTransportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (signedValuationLimit data frameExponent i j)) := by
    intro i j
    by_cases hc : data.coefficient i j = 0
    · simp [signedTransportedMatrix, transportedMonomialEntry,
        signedValuationLimit, hc]
    · have hle := hValuation i j hc
      by_cases heq : frameExponent j = frameExponent i + data.order i j
      · simpa [signedTransportedMatrix, signedValuationLimit, heq] using
          transportedMonomialEntry_tendsto_coefficient heq (data.coefficient i j)
      · have hlt := lt_of_le_of_ne hle heq
        simpa [signedTransportedMatrix, signedValuationLimit, heq] using
          transportedMonomialEntry_tendsto_zero hlt (data.coefficient i j)
  have hPi : Tendsto
      (fun t i j => signedTransportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fun i j => signedValuationLimit data frameExponent i j)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    exact hEntries i
  exact hPi

theorem signedTransportedMatrix_no_finite_limit_of_negativeValuation
    (data : SignedMonomialMatrixData) (frameExponent : Fin 4 → Nat)
    {i j : Fin 4} (hc : data.coefficient i j ≠ 0)
    (hNegative : frameExponent i + data.order i j < frameExponent j)
    (candidate : Matrix4) :
    ¬ Tendsto (signedTransportedMatrix data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  intro hMatrix
  have hEntry := (continuous_id.matrix_elem i j).tendsto candidate
  have hFinite : Tendsto
      (fun t => signedTransportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (candidate i j)) := hEntry.comp hMatrix
  rcases lt_or_gt_of_ne hc with hNeg | hPos
  · exact not_tendsto_atBot_of_tendsto_nhds hFinite
      (transportedMonomialEntry_tendsto_atBot hNegative hNeg)
  · exact not_tendsto_atTop_of_tendsto_nhds hFinite
      (transportedMonomialEntry_tendsto_atTop hNegative hPos)

theorem signedActiveValuationsNonnegative_iff_exists_finite_limit
    (data : SignedMonomialMatrixData) (frameExponent : Fin 4 → Nat) :
    SignedActiveValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4, Tendsto (signedTransportedMatrix data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  constructor
  · intro h
    exact ⟨signedValuationLimit data frameExponent,
      signedTransportedMatrix_tendsto data frameExponent h⟩
  · rintro ⟨candidate, hCandidate⟩ i j hc
    by_contra hle
    exact signedTransportedMatrix_no_finite_limit_of_negativeValuation
      data frameExponent hc (Nat.lt_of_not_ge hle) candidate hCandidate

end
end P0EFTJanusSignedMonomialMatrixValuationCriterion4D
end JanusFormal
