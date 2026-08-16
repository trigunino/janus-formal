import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bounded pullback of a chart Hessian along a dense smooth core

A smooth physical chart generally does not receive a bounded map from the
whole graph-Hilbert completion.  The mathematically natural direction is the
opposite one: the smooth core maps to the chart, and this core map is estimated
by the graph norm.

For a continuous bilinear chart Hessian `B` and a core map `T`, the single
estimate

`||T x|| <= C ||i x||`

implies

`||B(Tx,Ty)|| <= ||B|| C^2 ||i x|| ||i y||`.

This is precisely the product bound required by the existing two-variable
dense extension machinery.  No smoothing map from the completion back to the
smooth chart is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDenseCoreChartBilinearBound4D

set_option autoImplicit false
noncomputable section

variable {Core Hilbert Chart : Type*}
  [NormedAddCommGroup Core] [NormedSpace Real Core]
  [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]
  [NormedAddCommGroup Chart] [NormedSpace Real Chart]

/-- One graph-norm estimate for the true smooth-core map into a physical
chart. -/
structure DenseCoreChartMapBound
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  estimate : ∀ core, ‖chartMap core‖ ≤ constant * ‖embedding core‖

/-- Algebraic pullback of a continuous chart Hessian to the smooth core. -/
def denseCoreChartBilinearPullback
    (chartMap : Core →ₗ[Real] Chart)
    (form : Chart →L[Real] Chart →L[Real] Real) :
    Core →ₗ[Real] Core →ₗ[Real] Real where
  toFun first :=
    { toFun := fun second => form (chartMap first) (chartMap second)
      map_add' := by
        intro second third
        simp
      map_smul' := by
        intro scalar second
        simp }
  map_add' := by
    intro first second
    ext third
    simp
  map_smul' := by
    intro scalar first
    ext second
    simp

@[simp]
theorem denseCoreChartBilinearPullback_apply
    (chartMap : Core →ₗ[Real] Chart)
    (form : Chart →L[Real] Chart →L[Real] Real)
    (first second : Core) :
    denseCoreChartBilinearPullback chartMap form first second =
      form (chartMap first) (chartMap second) :=
  rfl

/-- The chart-map estimate yields the exact bilinear product bound required by
completion. -/
theorem denseCoreChartBilinearPullback_bound
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Chart →L[Real] Chart →L[Real] Real)
    (first second : Core) :
    ‖denseCoreChartBilinearPullback chartMap form first second‖ ≤
      (‖form‖ * bound.constant ^ 2) * ‖embedding first‖ *
        ‖embedding second‖ := by
  have hSecond :
      ‖form (chartMap first) (chartMap second)‖ ≤
        ‖form (chartMap first)‖ * ‖chartMap second‖ :=
    (form (chartMap first)).le_opNorm (chartMap second)
  have hFirst :
      ‖form (chartMap first)‖ ≤ ‖form‖ * ‖chartMap first‖ :=
    form.le_opNorm (chartMap first)
  calc
    ‖denseCoreChartBilinearPullback chartMap form first second‖ =
        ‖form (chartMap first) (chartMap second)‖ := rfl
    _ ≤ ‖form (chartMap first)‖ * ‖chartMap second‖ := hSecond
    _ ≤ (‖form‖ * ‖chartMap first‖) * ‖chartMap second‖ := by
      exact mul_le_mul_of_nonneg_right hFirst (norm_nonneg _)
    _ ≤ (‖form‖ * (bound.constant * ‖embedding first‖)) *
          (bound.constant * ‖embedding second‖) := by
      gcongr
      · exact mul_nonneg (norm_nonneg form)
          (mul_nonneg bound.constant_nonneg (norm_nonneg (embedding first)))
      · exact bound.estimate first
      · exact bound.estimate second
    _ = (‖form‖ * bound.constant ^ 2) * ‖embedding first‖ *
          ‖embedding second‖ := by
      ring

/-- Public dense-core chart checkpoint. -/
theorem dense_core_chart_bilinear_bound_gate
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Chart →L[Real] Chart →L[Real] Real) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ first second : Core,
        ‖denseCoreChartBilinearPullback chartMap form first second‖ ≤
          constant * ‖embedding first‖ * ‖embedding second‖ := by
  refine ⟨‖form‖ * bound.constant ^ 2, ?_, ?_⟩
  · positivity
  · exact denseCoreChartBilinearPullback_bound embedding chartMap bound form

end
end P0EFTJanusProgramPDenseCoreChartBilinearBound4D
end JanusFormal
