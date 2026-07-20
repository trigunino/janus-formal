import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAnalyticMatrixValuationCriterion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D

/-! # Analytic matrix valuation criterion allowing zero entries -/

namespace JanusFormal
namespace P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter Function
open scoped Topology

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4
abbrev ActiveAsymptoticMatrixData :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.ActiveAsymptoticMatrixData

/-- Analytic matrix entries; the zero formal series marks an inactive entry. -/
structure AnalyticMatrixData where
  entry : Fin 4 → Fin 4 → Real → Real
  series : Fin 4 → Fin 4 → FormalMultilinearSeries Real Real Real
  hasSeries : ∀ i j, HasFPowerSeriesAt (entry i j) (series i j) 0

def residual (data : AnalyticMatrixData) (i j : Fin 4) : Real → Real :=
  (swap dslope 0)^[(data.series i j).order] (data.entry i j)

private theorem normalized_tendsto (data : AnalyticMatrixData) (i j : Fin 4) :
    Tendsto (fun t => data.entry i j t * (t ^ (data.series i j).order)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (residual data i j 0)) := by
  have hp := data.hasSeries i j
  have hcont :=
    (hp.has_fpower_series_iterate_dslope_fslope (data.series i j).order).continuousAt
  have hres : Tendsto (residual data i j) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (residual data i j 0)) := hcont.tendsto.mono_left inf_le_left
  apply hres.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  simp only [residual]
  rw [hp.eq_pow_order_mul_iterate_dslope t]
  simp only [sub_zero, smul_eq_mul]
  field_simp [pow_ne_zero _ ht0]

/-- Analytic factorization instantiates the generic active-asymptotic data. -/
def AnalyticMatrixData.toActiveAsymptoticMatrixData
    (data : AnalyticMatrixData) : ActiveAsymptoticMatrixData where
  entry := data.entry
  active i j := data.series i j ≠ 0
  leadingCoefficient i j := residual data i j 0
  leadingOrder i j := (data.series i j).order
  leading_nonzero i j hActive := by
    simpa [residual] using
      (data.hasSeries i j).iterate_dslope_fslope_ne_zero hActive
  normalized_tendsto i j _ := normalized_tendsto data i j
  inactive_eventually_zero i j hInactive := by
    have hzero : data.series i j = 0 := not_ne_iff.mp hInactive
    exact ((data.hasSeries i j).locally_zero_iff.mpr hzero).filter_mono
      nhdsWithin_le_nhds

def transportedMatrix (data : AnalyticMatrixData) (frameExponent : Fin 4 → Nat) :
    Real → Matrix4 :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.transportedMatrix
    data.toActiveAsymptoticMatrixData frameExponent

def valuationLimit (data : AnalyticMatrixData) (frameExponent : Fin 4 → Nat) : Matrix4 :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.valuationLimit
    data.toActiveAsymptoticMatrixData frameExponent

def ActiveValuationsNonnegative (data : AnalyticMatrixData)
    (frameExponent : Fin 4 → Nat) : Prop :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.ActiveValuationsNonnegative
    data.toActiveAsymptoticMatrixData frameExponent

theorem transportedMatrix_tendsto (data : AnalyticMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation : ActiveValuationsNonnegative data frameExponent) :
    Tendsto (transportedMatrix data frameExponent) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (valuationLimit data frameExponent)) :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.transportedMatrix_tendsto
    data.toActiveAsymptoticMatrixData frameExponent hValuation

theorem transportedMatrix_no_finite_limit_of_negative_active_entry
    (data : AnalyticMatrixData) (frameExponent : Fin 4 → Nat) {i j : Fin 4}
    (hActive : data.series i j ≠ 0)
    (hNegative : frameExponent i + (data.series i j).order < frameExponent j)
    (candidate : Matrix4) :
    ¬ Tendsto (transportedMatrix data frameExponent) (nhdsWithin 0 (Set.Ioi 0))
      (nhds candidate) :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.transportedMatrix_no_finite_limit_of_negative_active_entry
      data.toActiveAsymptoticMatrixData frameExponent hActive hNegative candidate

/-- Zero analytic entries impose no valuation constraint; every active entry
imposes exactly the usual nonnegative valuation condition. -/
theorem activeValuationsNonnegative_iff_exists_finite_limit
    (data : AnalyticMatrixData) (frameExponent : Fin 4 → Nat) :
    ActiveValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto (transportedMatrix data frameExponent) (nhdsWithin 0 (Set.Ioi 0))
          (nhds candidate) :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.activeValuationsNonnegative_iff_exists_finite_limit _ _

end
end P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D
end JanusFormal
