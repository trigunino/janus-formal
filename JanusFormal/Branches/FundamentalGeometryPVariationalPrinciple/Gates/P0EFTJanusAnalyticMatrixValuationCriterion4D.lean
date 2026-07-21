import Mathlib.Analysis.Analytic.IsolatedZeros
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAsymptoticMatrixValuationCriterion4D

/-! # Matrix valuation criterion for analytic entries -/

namespace JanusFormal
namespace P0EFTJanusAnalyticMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter Function
open scoped Topology
open P0EFTJanusAsymptoticMatrixValuationCriterion4D

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

/-- A matrix whose entries have nonzero convergent power-series germs at zero. -/
structure AnalyticMatrixData where
  entry : Fin 4 → Fin 4 → Real → Real
  series : Fin 4 → Fin 4 → FormalMultilinearSeries Real Real Real
  hasSeries : ∀ i j, HasFPowerSeriesAt (entry i j) (series i j) 0
  series_ne_zero : ∀ i j, series i j ≠ 0

def residual (data : AnalyticMatrixData) (i j : Fin 4) : Real → Real :=
  (swap dslope 0)^[(data.series i j).order] (data.entry i j)

/-- Analytic factorization supplies the certified leading asymptotics. -/
def AnalyticMatrixData.toAsymptoticMatrixData
    (data : AnalyticMatrixData) : AsymptoticMatrixData where
  entry := data.entry
  leadingCoefficient i j := residual data i j 0
  leadingOrder i j := (data.series i j).order
  leading_nonzero i j := by
    simpa [residual] using
      (data.hasSeries i j).iterate_dslope_fslope_ne_zero (data.series_ne_zero i j)
  normalized_tendsto i j := by
    have hp := data.hasSeries i j
    have hcont :=
      (hp.has_fpower_series_iterate_dslope_fslope (data.series i j).order).continuousAt
    have hres : Tendsto (residual data i j) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (residual data i j 0)) := by
      exact hcont.tendsto.mono_left inf_le_left
    apply hres.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    rw [hp.eq_pow_order_mul_iterate_dslope t]
    simp only [residual, sub_zero, smul_eq_mul]
    field_simp [pow_ne_zero _ ht0]

/-- For analytic nonzero entries, entrywise valuations are exactly the obstruction
to a finite transported matrix limit. -/
theorem valuationsNonnegative_iff_exists_finite_limit
    (data : AnalyticMatrixData) (frameExponent : Fin 4 → Nat) :
    ValuationsNonnegative data.toAsymptoticMatrixData frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto (transportedMatrix data.toAsymptoticMatrixData frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) :=
  P0EFTJanusAsymptoticMatrixValuationCriterion4D.valuationsNonnegative_iff_exists_finite_limit _ _

end
end P0EFTJanusAnalyticMatrixValuationCriterion4D
end JanusFormal
