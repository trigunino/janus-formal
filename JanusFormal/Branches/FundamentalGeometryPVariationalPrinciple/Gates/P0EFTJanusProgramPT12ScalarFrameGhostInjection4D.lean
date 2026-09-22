import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

/-! Scalar fields inject into a finite family of genuine smooth ghosts.
Only the existing spanning tangent family is used; no global basis is assumed. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12ScalarFrameGhostInjection4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

def scalarFrameGhostLinearMap (frame : SmoothD8Frame period hPeriod) :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      (Fin frame.count → GlobalDiffeomorphismGhostField period hPeriod) where
  toFun field index := ⟨{
    toFun := fun point => field point • frame.vectorAt point index
    contMDiff_toFun := (field.contMDiff_toFun.of_le (by simp)).smul_section
      (frame.contMDiff_vector index) }⟩
  map_add' first second := by
    funext index
    apply GlobalDiffeomorphismGhostField.ext
    apply ContMDiffSection.ext
    intro point
    exact add_smul (first point) (second point) (frame.vectorAt point index)
  map_smul' scalar field := by
    funext index
    apply GlobalDiffeomorphismGhostField.ext
    apply ContMDiffSection.ext
    intro point
    exact mul_smul scalar (field point) (frame.vectorAt point index)

theorem scalarFrameGhostLinearMap_injective (frame : SmoothD8Frame period hPeriod) :
    Function.Injective (scalarFrameGhostLinearMap period hPeriod frame) := by
  intro first second hEqual
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  letI : Nontrivial (TangentSpace coverModelWithCorners point) := by
    change Nontrivial CoverCoordinates
    infer_instance
  have hExists : ∃ index, frame.vectorAt point index ≠ 0 := by
    by_contra h
    push Not at h
    have hSpan : Submodule.span Real (Set.range (frame.vectorAt point)) = ⊥ := by
      apply Submodule.span_eq_bot.mpr
      rintro vector ⟨index, rfl⟩
      exact h index
    exact bot_ne_top (hSpan.symm.trans (frame.spansAt point))
  obtain ⟨index, hNonzero⟩ := hExists
  have hValue := congrArg
    (fun family : Fin frame.count → GlobalDiffeomorphismGhostField period hPeriod =>
      (family index).field point) hEqual
  exact (smul_left_injective Real hNonzero) hValue

/-- Finite-dimensional ghosts would force finite-dimensional scalar fields. -/
theorem finiteDimensional_scalar_of_ghost
    [FiniteDimensional Real (GlobalDiffeomorphismGhostField period hPeriod)] :
    FiniteDimensional Real (SmoothQuotientField period hPeriod Real) :=
  FiniteDimensional.of_injective
    (scalarFrameGhostLinearMap period hPeriod (finiteSmoothTangentFrame period hPeriod))
    (scalarFrameGhostLinearMap_injective period hPeriod (finiteSmoothTangentFrame period hPeriod))

end
end P0EFTJanusProgramPT12ScalarFrameGhostInjection4D
end JanusFormal
