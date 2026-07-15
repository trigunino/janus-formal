import Mathlib.Analysis.SpecificLimits.Normed
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusD2HeatCountertermBridge

namespace JanusFormal
namespace P0EFTJanusHeatRemainderConvergence

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusRenormalizedSpectralDeterminant
open P0EFTJanusD2HeatCountertermBridge

noncomputable section

def cutoffRemainder (data : ProductThroatSpectralData)
    (coefficients : HeatCountertermCoefficients) (holonomy : ℝ) (N : ℕ) : ℝ :=
  finiteCutoffLogDeterminant data N holonomy - heatCounterterm coefficients N

def cutoffIncrement (data : ProductThroatSpectralData)
    (coefficients : HeatCountertermCoefficients) (holonomy : ℝ) (N : ℕ) : ℝ :=
  cutoffRemainder data coefficients holonomy (N + 1) -
    cutoffRemainder data coefficients holonomy N

theorem cutoff_remainder_telescope (data : ProductThroatSpectralData)
    (coefficients : HeatCountertermCoefficients) (holonomy : ℝ) (N : ℕ) :
    cutoffRemainder data coefficients holonomy N =
      cutoffRemainder data coefficients holonomy 0 +
        ∑ n ∈ Finset.range N, cutoffIncrement data coefficients holonomy n := by
  induction N with
  | zero => simp
  | succ N hN =>
      rw [Finset.sum_range_succ, ← add_assoc, ← hN]
      unfold cutoffIncrement
      ring

theorem cutoff_remainder_converges_of_summable_increments
    (data : ProductThroatSpectralData)
    (coefficients : HeatCountertermCoefficients) (holonomy : ℝ)
    (hSummable : Summable (cutoffIncrement data coefficients holonomy)) :
    Filter.Tendsto (cutoffRemainder data coefficients holonomy) Filter.atTop
      (nhds (cutoffRemainder data coefficients holonomy 0 +
        ∑' n, cutoffIncrement data coefficients holonomy n)) := by
  have hPartial := hSummable.hasSum.tendsto_sum_nat
  rw [show cutoffRemainder data coefficients holonomy =
      (fun N => cutoffRemainder data coefficients holonomy 0 +
        ∑ n ∈ Finset.range N, cutoffIncrement data coefficients holonomy n) by
    funext N
    exact cutoff_remainder_telescope data coefficients holonomy N]
  exact tendsto_const_nhds.add hPartial

/-- Uniform geometric decay of cutoff-shell increments. -/
structure HeatRemainderGeometricBound
    (data : ProductThroatSpectralData)
    (coefficients : HeatCountertermCoefficients) where
  amplitude : ℝ
  ratio : ℝ
  amplitudeNonnegative : 0 ≤ amplitude
  ratioNonnegative : 0 ≤ ratio
  ratioLessThanOne : ratio < 1
  incrementBound : ∀ holonomy : ℝ, ∀ N : ℕ,
    |cutoffIncrement data coefficients holonomy N| ≤ amplitude * ratio ^ N

theorem increments_summable_of_geometric_bound
    {data : ProductThroatSpectralData}
    {coefficients : HeatCountertermCoefficients}
    (bound : HeatRemainderGeometricBound data coefficients)
    (holonomy : ℝ) :
    Summable (cutoffIncrement data coefficients holonomy) := by
  apply Summable.of_norm_bounded
    (Summable.mul_left bound.amplitude
      (summable_geometric_of_lt_one bound.ratioNonnegative bound.ratioLessThanOne))
  intro N
  simpa [Real.norm_eq_abs] using bound.incrementBound holonomy N

noncomputable def heatFamilyOfGeometricBound
    {data : ProductThroatSpectralData}
    {coefficients : HeatCountertermCoefficients}
    (bound : HeatRemainderGeometricBound data coefficients) :
    HeatRenormalizedHolonomyFamily data where
  coefficients := coefficients
  renormalizedLog := fun holonomy =>
    cutoffRemainder data coefficients holonomy 0 +
      ∑' N, cutoffIncrement data coefficients holonomy N
  remainderConverges := fun holonomy =>
    cutoff_remainder_converges_of_summable_increments data coefficients holonomy
      (increments_summable_of_geometric_bound bound holonomy)

theorem geometric_heat_bound_closes_d2_determinant
    {data : ProductThroatSpectralData}
    {coefficients : HeatCountertermCoefficients}
    (bound : HeatRemainderGeometricBound data coefficients) :
    RenormalizedDeterminantClosureCertificate data :=
  heat_family_closes_d2_determinant data (heatFamilyOfGeometricBound bound)

end

end P0EFTJanusHeatRemainderConvergence
end JanusFormal
