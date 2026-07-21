import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphFrameChange4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphFrameChangeCoherence4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusH1GraphFrameChange4D

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
  [CompleteSpace Fiber]

/-- Frame-change equivalences compose canonically: both sides are the unique
continuous extension of the identity on the common smooth core. -/
theorem h1GraphFrameChangeEquiv_trans
    (first second third : SmoothD8Frame period hPeriod)
    (firstSecond : UniformSmoothFrameChange period hPeriod Fiber first second)
    (secondFirst : UniformSmoothFrameChange period hPeriod Fiber second first)
    (secondThird : UniformSmoothFrameChange period hPeriod Fiber second third)
    (thirdSecond : UniformSmoothFrameChange period hPeriod Fiber third second)
    (firstThird : UniformSmoothFrameChange period hPeriod Fiber first third)
    (thirdFirst : UniformSmoothFrameChange period hPeriod Fiber third first)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    (h1GraphFrameChangeEquiv period hPeriod Fiber first second
        firstSecond secondFirst mu).trans
      (h1GraphFrameChangeEquiv period hPeriod Fiber second third
        secondThird thirdSecond mu) =
    h1GraphFrameChangeEquiv period hPeriod Fiber first third
      firstThird thirdFirst mu := by
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber first mu) :=
    h1GraphCompleteSpace period hPeriod Fiber first mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber second mu) :=
    h1GraphCompleteSpace period hPeriod Fiber second mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber third mu) :=
    h1GraphCompleteSpace period hPeriod Fiber third mu
  apply ContinuousLinearEquiv.ext
  funext value
  have hFunctions :=
    (smoothToH1Graph_denseRange period hPeriod Fiber first mu).equalizer
      (g := fun x => ((h1GraphFrameChangeEquiv period hPeriod Fiber first second
        firstSecond secondFirst mu).trans
          (h1GraphFrameChangeEquiv period hPeriod Fiber second third
            secondThird thirdSecond mu)) x)
      (h := fun x => h1GraphFrameChangeEquiv period hPeriod Fiber first third
        firstThird thirdFirst mu x)
      (by fun_prop) (by fun_prop) (by
        funext field
        simp)
  exact congrFun hFunctions value

/-- Reversing the two bounded frame changes gives exactly the inverse
continuous equivalence, not merely an abstract isomorphic completion. -/
theorem h1GraphFrameChangeEquiv_symm
    (first second : SmoothD8Frame period hPeriod)
    (forward : UniformSmoothFrameChange period hPeriod Fiber first second)
    (backward : UniformSmoothFrameChange period hPeriod Fiber second first)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    (h1GraphFrameChangeEquiv period hPeriod Fiber first second
      forward backward mu).symm =
    h1GraphFrameChangeEquiv period hPeriod Fiber second first
      backward forward mu := by
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber first mu) :=
    h1GraphCompleteSpace period hPeriod Fiber first mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber second mu) :=
    h1GraphCompleteSpace period hPeriod Fiber second mu
  apply ContinuousLinearEquiv.ext
  funext value
  have hFunctions :=
    (smoothToH1Graph_denseRange period hPeriod Fiber second mu).equalizer
      (g := fun x => (h1GraphFrameChangeEquiv period hPeriod Fiber first second
        forward backward mu).symm x)
      (h := fun x => h1GraphFrameChangeEquiv period hPeriod Fiber second first
        backward forward mu x)
      (by fun_prop) (by fun_prop) (by
        funext field
        simp only [Function.comp_apply]
        rw [h1GraphFrameChangeEquiv_smooth period hPeriod Fiber second first
          backward forward mu field]
        apply (h1GraphFrameChangeEquiv period hPeriod Fiber first second
          forward backward mu).injective
        simp)
  exact congrFun hFunctions value

end
end P0EFTJanusMappingTorusH1GraphFrameChangeCoherence4D
end JanusFormal
