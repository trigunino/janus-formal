import Mathlib.Analysis.Calculus.ContDiff.Basic
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorBundleDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorSmoothDescent

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open P0EFTJanusRieszShapeOperatorBundleDescent

universe u v w

variable {Chart : Type u} {Base : Type v} {Fiber : Type w}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- If one chart is valid globally, the abstract descended value is exactly that
chart's representative. -/
theorem descendedValue_eq_globalChart
    (data : LocalDescentData Chart Base Fiber)
    (chart : Chart)
    (hGlobal : ∀ base, data.valid chart base) :
    descendedValue data = data.localValue chart := by
  funext base
  exact (localValue_eq_descendedValue data chart base (hGlobal base)).symm

/-- Smoothness descends immediately when a global smooth trivialization exists.

This theorem deliberately does not claim that an arbitrary local atlas admits a
global chart. It isolates the easy global-trivialization case and leaves the
true local smooth-gluing theorem as a separate geometric/topological lock. -/
theorem descendedValue_contDiff_of_globalChart
    (data : LocalDescentData Chart Base Fiber)
    (chart : Chart)
    (hGlobal : ∀ base, data.valid chart base)
    (hSmooth : ContDiff ℝ ∞ (data.localValue chart)) :
    ContDiff ℝ ∞ (descendedValue data) := by
  rw [descendedValue_eq_globalChart data chart hGlobal]
  exact hSmooth

/-- A globally realized equivariant Riesz family therefore gives a smooth global
operator whenever its representative in that global metric frame is smooth. -/
theorem smooth_global_representative_gives_smooth_descent
    (data : LocalDescentData Chart Base Fiber)
    (chart : Chart)
    (hGlobal : ∀ base, data.valid chart base)
    (hSmooth : ContDiff ℝ ∞ (data.localValue chart)) :
    ∃ global : Base → Fiber,
      ContDiff ℝ ∞ global ∧
      ∀ base, global base = data.localValue chart base := by
  refine ⟨descendedValue data, ?_, ?_⟩
  · exact descendedValue_contDiff_of_globalChart data chart hGlobal hSmooth
  · intro base
    exact localValue_eq_descendedValue data chart base (hGlobal base) |>.symm

/-- Exact boundary after the global-trivialization smoothness theorem. -/
structure RieszSmoothDescentStatus where
  abstractGlobalDescentConstructed : Prop
  globalTrivializationSmoothnessTransferred : Prop
  localSmoothAtlasConstructed : Prop
  localContDiffGluingProved : Prop
  actualJanusMetricFrameAtlasInstantiated : Prop

/-- Full closure of smooth Riesz descent. -/
def rieszSmoothDescentClosed (s : RieszSmoothDescentStatus) : Prop :=
  s.abstractGlobalDescentConstructed ∧
  s.globalTrivializationSmoothnessTransferred ∧
  s.localSmoothAtlasConstructed ∧
  s.localContDiffGluingProved ∧
  s.actualJanusMetricFrameAtlasInstantiated

/-- The global-chart theorem does not replace local smooth gluing. -/
theorem missing_local_gluing_blocks_smooth_riesz_descent
    (s : RieszSmoothDescentStatus)
    (hMissing : Not s.localContDiffGluingProved) :
    Not (rieszSmoothDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorSmoothDescent
end JanusFormal
