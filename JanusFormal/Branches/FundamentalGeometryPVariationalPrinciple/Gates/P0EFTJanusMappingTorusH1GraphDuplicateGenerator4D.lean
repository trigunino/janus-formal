import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphFiniteZeroRedundancy4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphDuplicateGenerator4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusH1GraphFrameChange4D

variable (period : ℝ) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

/-- Append a second copy of one explicitly selected generator. -/
def duplicateGeneratorFrame (frame : SmoothD8Frame period hPeriod)
    (chosen : Fin frame.count) : SmoothD8Frame period hPeriod where
  count := frame.count + 1
  vectorAt point j := match finSumFinEquiv.symm j with
    | Sum.inl i => frame.vectorAt point i
    | Sum.inr _ => frame.vectorAt point chosen
  spansAt point := by
    apply top_unique
    rw [← frame.spansAt point]
    apply Submodule.span_mono
    rintro vector ⟨i, rfl⟩
    exact ⟨finSumFinEquiv (Sum.inl i), by simp⟩
  contMDiff_vector j := by
    change ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun point => (⟨point, match finSumFinEquiv.symm j with
        | Sum.inl i => frame.vectorAt point i
        | Sum.inr _ => frame.vectorAt point chosen⟩ :
          TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod)))
    cases h : finSumFinEquiv.symm j with
    | inl i => simpa only [h] using frame.contMDiff_vector i
    | inr i => simpa only [h] using frame.contMDiff_vector chosen

universe u
variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

def duplicateGeneratorForward (frame : SmoothD8Frame period hPeriod)
    (chosen : Fin frame.count) :
    UniformSmoothFrameChange period hPeriod Fiber frame
      (duplicateGeneratorFrame period hPeriod frame chosen) where
  coefficient _ j i := match finSumFinEquiv.symm j with
    | Sum.inl k => if i = k then 1 else 0
    | Sum.inr _ => if i = chosen then 1 else 0
  coefficient_smooth _ _ := contMDiff_const
  vector_eq point j := by
    cases h : finSumFinEquiv.symm j <;> simp [duplicateGeneratorFrame, h]
  bound := 1
  one_le_bound := le_rfl
  matrix_bound point values := by
    simp only [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg values)).2
    intro j
    cases h : finSumFinEquiv.symm j with
    | inl k => simpa using (pi_norm_le_iff_of_nonneg (norm_nonneg values)).1 le_rfl k
    | inr k => simpa using
        (pi_norm_le_iff_of_nonneg (norm_nonneg values)).1 le_rfl chosen

def duplicateGeneratorBack (frame : SmoothD8Frame period hPeriod)
    (chosen : Fin frame.count) :
    UniformSmoothFrameChange period hPeriod Fiber
      (duplicateGeneratorFrame period hPeriod frame chosen) frame where
  coefficient _ j i := if i = finSumFinEquiv (Sum.inl j) then 1 else 0
  coefficient_smooth _ _ := contMDiff_const
  vector_eq point j := by simp [duplicateGeneratorFrame]
  bound := 1
  one_le_bound := le_rfl
  matrix_bound point values := by
    simp only [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg values)).2
    intro j
    have h := (pi_norm_le_iff_of_nonneg (norm_nonneg values)).1 le_rfl
      (finSumFinEquiv (Sum.inl j))
    simpa using h

def duplicateGeneratorH1GraphEquiv [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod) (chosen : Fin frame.count)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  h1GraphFrameChangeEquiv period hPeriod Fiber frame
    (duplicateGeneratorFrame period hPeriod frame chosen)
    (duplicateGeneratorForward period hPeriod Fiber frame chosen)
    (duplicateGeneratorBack period hPeriod Fiber frame chosen) mu

@[simp] theorem duplicateGeneratorH1GraphEquiv_smooth [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod) (chosen : Fin frame.count)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    duplicateGeneratorH1GraphEquiv period hPeriod Fiber frame chosen mu
        (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber
        (duplicateGeneratorFrame period hPeriod frame chosen) mu field := by
  apply h1GraphFrameChangeEquiv_smooth

end
end P0EFTJanusMappingTorusH1GraphDuplicateGenerator4D
end JanusFormal
