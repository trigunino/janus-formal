import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeometricBismutFreedPathComparison4D

/-!
# Multidimensional families-index curvature comparison

A one-parameter path determines the pullback of the Bismut--Freed connection but
cannot determine its curvature on a higher-dimensional parameter base.  The
families-index theorem is therefore recorded as a genuinely separate geometric
comparison: the curvature two-form of the determinant connection equals the
local families-index two-form.

No circle holonomy statement is used to manufacture this two-dimensional data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D

universe u v w x

variable {E : Type u} {Base : Type w} {Tangent : Type x}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Concrete curvature comparison on an arbitrary geometric parameter base. -/
structure GeometricFamiliesIndexCurvatureData (Base Tangent : Type*) where
  bismutFreedCurvature : Base → Tangent → Tangent → Complex
  localFamiliesIndexCurvature : Base → Tangent → Tangent → Complex
  bismutFreedCurvature_antisymm : ∀ base first second,
    bismutFreedCurvature base first second =
      -bismutFreedCurvature base second first
  curvature_agreement : ∀ base first second,
    bismutFreedCurvature base first second =
      localFamiliesIndexCurvature base first second

/-- One geometric/operator path comparison together with the independent
higher-dimensional local families-index curvature theorem. -/
structure GeometricBismutFreedFamiliesIndexComparisonData
    (actual reference : Real → E →L[Real] E)
    (Base : Type w) (Tangent : Type x) where
  pathComparison : GeometricOperatorBismutFreedPathComparisonData.{u, v, w, x}
    actual reference Base Tangent
  curvature : GeometricFamiliesIndexCurvatureData Base Tangent

namespace GeometricBismutFreedFamiliesIndexComparisonData

/-- The local families-index curvature is automatically antisymmetric once it
is identified with the geometric Bismut--Freed curvature. -/
theorem localFamiliesIndexCurvature_antisymm
    {actual reference : Real → E →L[Real] E}
    (data : GeometricBismutFreedFamiliesIndexComparisonData.{u, v, w, x}
      actual reference Base Tangent)
    (base : Base) (first second : Tangent) :
    data.curvature.localFamiliesIndexCurvature base first second =
      -data.curvature.localFamiliesIndexCurvature base second first := by
  rw [← data.curvature.curvature_agreement base first second]
  rw [← data.curvature.curvature_agreement base second first]
  exact data.curvature.bismutFreedCurvature_antisymm base first second

/-- Public multidimensional Bismut--Freed/families-index checkpoint. -/
theorem geometric_bismut_freed_families_index_comparison_gate
    {actual reference : Real → E →L[Real] E}
    (data : GeometricBismutFreedFamiliesIndexComparisonData.{u, v, w, x}
      actual reference Base Tangent) :
    (∀ parameter value derivative,
      data.pathComparison.geometricConnectionAt parameter value derivative =
        data.pathComparison.operatorFamily.connectionAt parameter value derivative) ∧
    (∀ base first second,
      data.curvature.bismutFreedCurvature base first second =
        data.curvature.localFamiliesIndexCurvature base first second) ∧
    (∀ base first second,
      data.curvature.localFamiliesIndexCurvature base first second =
        -data.curvature.localFamiliesIndexCurvature base second first) :=
  ⟨data.pathComparison.geometricConnectionAt_eq_operator,
    data.curvature.curvature_agreement,
    data.localFamiliesIndexCurvature_antisymm⟩

end GeometricBismutFreedFamiliesIndexComparisonData

end
end P0EFTJanusProgramPGeometricBismutFreedFamiliesIndexCurvature4D
end JanusFormal
