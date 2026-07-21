import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphRedundantFrame4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphFiniteZeroRedundancy4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusH1GraphRedundantFrame4D

variable (period : ℝ) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

/-- Iteratively append any finite number of identically-zero generators. -/
def appendZeroGenerators (frame : SmoothD8Frame period hPeriod) :
    Nat → SmoothD8Frame period hPeriod
  | 0 => frame
  | k + 1 => appendZeroSmoothD8Frame period hPeriod
      (appendZeroGenerators frame k)

@[simp] theorem appendZeroGenerators_zero (frame : SmoothD8Frame period hPeriod) :
    appendZeroGenerators period hPeriod frame 0 = frame := rfl

@[simp] theorem appendZeroGenerators_succ (frame : SmoothD8Frame period hPeriod) (k : Nat) :
    appendZeroGenerators period hPeriod frame (k + 1) =
      appendZeroSmoothD8Frame period hPeriod
        (appendZeroGenerators period hPeriod frame k) := rfl

theorem appendZeroGenerators_add (frame : SmoothD8Frame period hPeriod) (k l : Nat) :
    appendZeroGenerators period hPeriod frame (k + l) =
      appendZeroGenerators period hPeriod
        (appendZeroGenerators period hPeriod frame k) l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [Nat.add_succ, appendZeroGenerators_succ, ih]

universe u
variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- Canonical H1 equivalence after finitely many zero-generator additions. -/
def appendZeroGeneratorsH1GraphEquiv [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    (k : Nat) → H1GraphSpace period hPeriod Fiber frame mu ≃L[ℝ]
      H1GraphSpace period hPeriod Fiber
        (appendZeroGenerators period hPeriod frame k) mu
  | 0 => ContinuousLinearEquiv.refl ℝ _
  | k + 1 =>
      (appendZeroGeneratorsH1GraphEquiv frame mu k).trans
        (appendZeroH1GraphEquiv period hPeriod Fiber
          (appendZeroGenerators period hPeriod frame k) mu)

@[simp] theorem appendZeroGeneratorsH1GraphEquiv_smooth [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) (k : Nat) :
    appendZeroGeneratorsH1GraphEquiv period hPeriod Fiber frame mu k
        (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber
        (appendZeroGenerators period hPeriod frame k) mu field := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change appendZeroH1GraphEquiv period hPeriod Fiber
          (appendZeroGenerators period hPeriod frame k) mu
          (appendZeroGeneratorsH1GraphEquiv period hPeriod Fiber frame mu k
            (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field)) = _
      rw [ih, appendZeroH1GraphEquiv_smooth]
      rfl

/-- Adding `k` then `l` zero generators has the same action on every smooth
field as adding `k+l` at once. -/
theorem appendZeroGeneratorsH1GraphEquiv_coherent_smooth [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) (k l : Nat) :
    HEq
      (appendZeroGeneratorsH1GraphEquiv period hPeriod Fiber frame mu (k + l)
        (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field))
      (appendZeroGeneratorsH1GraphEquiv period hPeriod Fiber
        (appendZeroGenerators period hPeriod frame k) mu l
        (appendZeroGeneratorsH1GraphEquiv period hPeriod Fiber frame mu k
          (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field))) := by
  rw [appendZeroGeneratorsH1GraphEquiv_smooth,
    appendZeroGeneratorsH1GraphEquiv_smooth,
    appendZeroGeneratorsH1GraphEquiv_smooth]
  rw [appendZeroGenerators_add]

end
end P0EFTJanusMappingTorusH1GraphFiniteZeroRedundancy4D
end JanusFormal
