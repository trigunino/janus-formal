import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphSmoothGLFrame4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusTangentZeroSectionSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold

variable (period : ℝ) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def zeroInputBundle (point : EffectiveQuotient period hPeriod) :
    TangentBundle (𝓘(ℝ, ℝ).prod coverModelWithCorners)
      (ℝ × EffectiveQuotient period hPeriod) :=
  (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ coverModelWithCorners
      (EffectiveQuotient period hPeriod)).symm
    (⟨0, 0⟩, ⟨point, 0⟩)

private theorem zeroInputBundle_contMDiff :
    ContMDiff coverModelWithCorners
      (𝓘(ℝ, ℝ).prod coverModelWithCorners).tangent ∞
      (zeroInputBundle period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, ℝ)) (I' := coverModelWithCorners)
    (M := ℝ) (M' := EffectiveQuotient period hPeriod)).comp
  exact contMDiff_const.prodMk
    (Bundle.contMDiff_zeroSection (n := ∞) ℝ
      (TangentSpace coverModelWithCorners :
        EffectiveQuotient period hPeriod → Type _))

private def tangentZeroBundle (point : EffectiveQuotient period hPeriod) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  tangentMap (𝓘(ℝ, ℝ).prod coverModelWithCorners) coverModelWithCorners
    Prod.snd (zeroInputBundle period hPeriod point)

private theorem tangentZeroBundle_contMDiff :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (tangentZeroBundle period hPeriod) :=
  (((contMDiff_snd (n := ∞)).contMDiff_tangentMap (m := ∞) (by simp)).comp
    (zeroInputBundle_contMDiff period hPeriod))

@[simp] private theorem tangentZeroBundle_eq (point : EffectiveQuotient period hPeriod) :
    tangentZeroBundle period hPeriod point = ⟨point, 0⟩ := by
  apply Bundle.TotalSpace.ext
  · rfl
  · dsimp [tangentZeroBundle, zeroInputBundle, tangentMap]
    rw [mfderiv_snd]
    rfl

/-- The zero vector field is smooth for the intrinsic tangent-bundle model. -/
theorem tangentZeroSection_contMDiff :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun point : EffectiveQuotient period hPeriod =>
        (⟨point, (0 : TangentSpace coverModelWithCorners point)⟩ :
          TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod))) := by
  exact (tangentZeroBundle_contMDiff period hPeriod).congr
    (fun point => (tangentZeroBundle_eq period hPeriod point).symm)

end
end P0EFTJanusMappingTorusTangentZeroSectionSmooth4D
end JanusFormal
