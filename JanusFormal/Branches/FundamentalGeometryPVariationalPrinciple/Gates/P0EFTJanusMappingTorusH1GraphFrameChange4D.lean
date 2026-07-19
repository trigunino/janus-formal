import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphFrameChange4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

universe u

variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- A smooth matrix expressing every vector of `target` in `source`, together
with one uniform operator-norm bound for that matrix. -/
structure UniformSmoothFrameChange
    (source target : SmoothD8Frame period hPeriod) where
  coefficient : EffectiveQuotient period hPeriod →
    Fin target.count → Fin source.count → Real
  coefficient_smooth : ∀ j i,
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => coefficient point j i)
  vector_eq : ∀ point j,
    target.vectorAt point j =
      ∑ i, coefficient point j i • source.vectorAt point i
  bound : Real
  one_le_bound : 1 ≤ bound
  matrix_bound : ∀ point (values : Fin source.count → Fiber),
    ‖fun j => ∑ i, coefficient point j i • values i‖ ≤ bound * ‖values‖

theorem frameDerivative_eq_matrix
    (source target : SmoothD8Frame period hPeriod)
    (change : UniformSmoothFrameChange period hPeriod Fiber source target)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    frameDerivative period hPeriod Fiber target field point =
      fun j => ∑ i, change.coefficient point j i •
        frameDerivative period hPeriod Fiber source field point i := by
  funext j
  rw [frameDerivative_eq_mfderiv, change.vector_eq point j, map_sum]
  simp only [map_smul, frameDerivative_eq_mfderiv]

theorem smoothFirstJet_norm_le
    (source target : SmoothD8Frame period hPeriod)
    (change : UniformSmoothFrameChange period hPeriod Fiber source target)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Fiber target field point‖ ≤
      change.bound * ‖smoothFirstJet period hPeriod Fiber source field point‖ := by
  change max ‖field point‖
      ‖frameDerivative period hPeriod Fiber target field point‖ ≤
    change.bound * max ‖field point‖
      ‖frameDerivative period hPeriod Fiber source field point‖
  apply max_le
  · exact (le_max_left _ _).trans
      (le_mul_of_one_le_left
        ((norm_nonneg _).trans (le_max_left _ _)) change.one_le_bound)
  · rw [frameDerivative_eq_matrix period hPeriod Fiber source target change field point]
    exact (change.matrix_bound point _).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _)
        (zero_le_one.trans change.one_le_bound))

theorem smoothToH1Graph_norm_le
    (source target : SmoothD8Frame period hPeriod)
    (change : UniformSmoothFrameChange period hPeriod Fiber source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    ‖smoothToH1GraphLinearMap period hPeriod Fiber target mu field‖ ≤
      change.bound *
        ‖smoothToH1GraphLinearMap period hPeriod Fiber source mu field‖ := by
  change ‖smoothFirstJetToL2 period hPeriod Fiber target mu field‖ ≤
    change.bound * ‖smoothFirstJetToL2 period hPeriod Fiber source mu field‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards
    [(smoothFirstJet_memLp period hPeriod Fiber target mu field).coeFn_toLp,
      (smoothFirstJet_memLp period hPeriod Fiber source mu field).coeFn_toLp]
    with point hTarget hSource
  change
    ‖(smoothFirstJetToL2 period hPeriod Fiber target mu field :
      EffectiveQuotient period hPeriod → _) point‖ ≤ _
  rw [show (smoothFirstJetToL2 period hPeriod Fiber target mu field :
      EffectiveQuotient period hPeriod → _) point =
        smoothFirstJet period hPeriod Fiber target field point by
      simpa only [smoothFirstJetToL2] using hTarget,
    show (smoothFirstJetToL2 period hPeriod Fiber source mu field :
      EffectiveQuotient period hPeriod → _) point =
        smoothFirstJet period hPeriod Fiber source field point by
      simpa only [smoothFirstJetToL2] using hSource]
  exact smoothFirstJet_norm_le period hPeriod Fiber source target change field point

/-- Two uniformly bounded smooth frame changes induce the canonical
bicontinuous identity equivalence of the two graph completions. -/
def h1GraphFrameChangeEquiv
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (forward : UniformSmoothFrameChange period hPeriod Fiber source target)
    (backward : UniformSmoothFrameChange period hPeriod Fiber target source)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    H1GraphSpace period hPeriod Fiber source mu ≃L[Real]
      H1GraphSpace period hPeriod Fiber target mu := by
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber source mu) :=
    h1GraphCompleteSpace period hPeriod Fiber source mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber target mu) :=
    h1GraphCompleteSpace period hPeriod Fiber target mu
  exact (LinearEquiv.refl Real
    (SmoothQuotientField period hPeriod Fiber)).extend
      (smoothToH1GraphLinearMap period hPeriod Fiber source mu)
      (smoothToH1GraphLinearMap period hPeriod Fiber target mu)
      (smoothToH1Graph_denseRange period hPeriod Fiber source mu)
      ⟨forward.bound, smoothToH1Graph_norm_le period hPeriod Fiber
        source target forward mu⟩
      (smoothToH1Graph_denseRange period hPeriod Fiber target mu)
      ⟨backward.bound, smoothToH1Graph_norm_le period hPeriod Fiber
        target source backward mu⟩

@[simp] theorem h1GraphFrameChangeEquiv_smooth
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (forward : UniformSmoothFrameChange period hPeriod Fiber source target)
    (backward : UniformSmoothFrameChange period hPeriod Fiber target source)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    h1GraphFrameChangeEquiv period hPeriod Fiber source target forward backward mu
        (smoothToH1GraphLinearMap period hPeriod Fiber source mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber target mu field := by
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber source mu) :=
    h1GraphCompleteSpace period hPeriod Fiber source mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber target mu) :=
    h1GraphCompleteSpace period hPeriod Fiber target mu
  apply LinearEquiv.extend_eq

end
end P0EFTJanusMappingTorusH1GraphFrameChange4D
end JanusFormal
