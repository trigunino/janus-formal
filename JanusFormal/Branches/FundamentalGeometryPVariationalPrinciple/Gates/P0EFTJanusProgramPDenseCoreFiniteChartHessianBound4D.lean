import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDenseCoreChartBilinearBound4D

/-!
# A finite sum of chart Hessians bounded by one graph-core estimate

The Candidate-A physical remainder is a finite sum of action Hessians.  Once
all of them are evaluated through the same smooth-core map into the physical
chart, one graph-norm bound controls the whole sum.  The common constant is the
sum of the operator norms of the chart Hessians times the square of the chart
map constant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable {Core Hilbert Chart Block : Type*}
  [AddCommGroup Core] [Module Real Core]
  [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]
  [NormedAddCommGroup Chart] [NormedSpace Real Chart]
  [Fintype Block] [DecidableEq Block]

/-- Sum of a finite family of true chart Hessians pulled back to the smooth
core. -/
def denseCoreFiniteChartHessianSum
    (chartMap : Core →ₗ[Real] Chart)
    (form : Block → Chart →L[Real] Chart →L[Real] Real) :
    Core →ₗ[Real] Core →ₗ[Real] Real :=
  ∑ block : Block, denseCoreChartBilinearPullback chartMap (form block)

@[simp]
theorem denseCoreFiniteChartHessianSum_apply
    (chartMap : Core →ₗ[Real] Chart)
    (form : Block → Chart →L[Real] Chart →L[Real] Real)
    (first second : Core) :
    denseCoreFiniteChartHessianSum chartMap form first second =
      ∑ block : Block, form block (chartMap first) (chartMap second) := by
  simp [denseCoreFiniteChartHessianSum]

/-- The single graph-core estimate controls the complete finite Hessian sum. -/
theorem denseCoreFiniteChartHessianSum_bound
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Block → Chart →L[Real] Chart →L[Real] Real)
    (first second : Core) :
    ‖denseCoreFiniteChartHessianSum chartMap form first second‖ ≤
      ((∑ block : Block, ‖form block‖) * bound.constant ^ 2) *
        ‖embedding first‖ * ‖embedding second‖ := by
  rw [denseCoreFiniteChartHessianSum_apply]
  calc
    ‖∑ block : Block, form block (chartMap first) (chartMap second)‖ ≤
        ∑ block : Block,
          ‖form block (chartMap first) (chartMap second)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ block : Block,
        (‖form block‖ * bound.constant ^ 2) *
          ‖embedding first‖ * ‖embedding second‖ := by
      exact Finset.sum_le_sum fun block _ =>
        denseCoreChartBilinearPullback_bound embedding chartMap bound
          (form block) first second
    _ = ((∑ block : Block, ‖form block‖) * bound.constant ^ 2) *
          ‖embedding first‖ * ‖embedding second‖ := by
      simp only [Finset.sum_mul]

/-- The finite sum constant is nonnegative. -/
theorem denseCoreFiniteChartHessianSum_constant_nonneg
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Block → Chart →L[Real] Chart →L[Real] Real) :
    0 ≤ (∑ block : Block, ‖form block‖) * bound.constant ^ 2 := by
  exact mul_nonneg (Finset.sum_nonneg fun block _ => norm_nonneg (form block))
    (sq_nonneg bound.constant)

/-- Public finite physical-chart bound checkpoint. -/
theorem dense_core_finite_chart_hessian_bound_gate
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Block → Chart →L[Real] Chart →L[Real] Real) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ first second : Core,
        ‖denseCoreFiniteChartHessianSum chartMap form first second‖ ≤
          constant * ‖embedding first‖ * ‖embedding second‖ := by
  refine ⟨(∑ block : Block, ‖form block‖) * bound.constant ^ 2,
    denseCoreFiniteChartHessianSum_constant_nonneg embedding chartMap bound form, ?_⟩
  exact denseCoreFiniteChartHessianSum_bound embedding chartMap bound form

end
end P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
end JanusFormal
