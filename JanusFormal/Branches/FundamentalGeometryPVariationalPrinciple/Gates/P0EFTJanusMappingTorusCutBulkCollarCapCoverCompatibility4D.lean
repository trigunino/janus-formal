import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D

/-!
# Smooth collar--cap transition on the covers

Restricting the existing equatorial tubular diffeomorphism to `0 < normal < 1`
gives the smooth transition between the collar and cap fiber charts.  The
inverse smoothness is inherited from the already-proved tubular inverse.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D

/-- The strict collar overlap `0 < normal < 1` inside the tubular parameter
space. -/
def positiveUnitTubularParameterOpen :
    TopologicalSpace.Opens
      (EquatorialTwoSphere × equatorialTubularNormalOpen) :=
  ⟨{parameter | 0 < parameter.2.1 ∧ parameter.2.1 < 1}, by
    have hNormal : Continuous
        (fun parameter : EquatorialTwoSphere × equatorialTubularNormalOpen =>
          parameter.2.1) :=
      continuous_subtype_val.comp continuous_snd
    exact (isOpen_lt continuous_const hNormal).inter
      (isOpen_lt hNormal continuous_const)⟩

/-- Tubular latitude map restricted to the strict collar overlap. -/
def positiveUnitTubularMap :
    positiveUnitTubularParameterOpen → equatorialSphericalBandOpen :=
  fun parameter => equatorialTubularSmoothMap parameter.1

theorem positiveUnitTubularMap_isOpenEmbedding :
    IsOpenEmbedding positiveUnitTubularMap := by
  exact equatorialTubularDiffeomorph.toHomeomorph.isOpenEmbedding.comp
    positiveUnitTubularParameterOpen.2.isOpenEmbedding_subtypeVal

/-- Image of the strict collar overlap in the positive latitude band. -/
def positiveUnitLatitudeBandOpen :
    TopologicalSpace.Opens equatorialSphericalBandOpen :=
  ⟨Set.range positiveUnitTubularMap,
    positiveUnitTubularMap_isOpenEmbedding.isOpen_range⟩

/-- Canonical homeomorphism onto the strict latitude-band image. -/
def positiveUnitTubularHomeomorph :
    positiveUnitTubularParameterOpen ≃ₜ positiveUnitLatitudeBandOpen :=
  positiveUnitTubularMap_isOpenEmbedding.isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr rfl)

theorem positiveUnitTubularHomeomorph_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      positiveUnitTubularHomeomorph := by
  rw [← ContMDiff.subtypeVal_comp_iff positiveUnitLatitudeBandOpen]
  have hIn :
      ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
        ((𝓡 2).prod 𝓘(Real, Real)) ∞
        (Subtype.val : positiveUnitTubularParameterOpen →
          EquatorialTwoSphere × equatorialTubularNormalOpen) :=
    contMDiff_subtype_val
  have h := equatorialTubularSmoothMap_contMDiff.comp hIn
  exact h.congr fun _ => rfl

theorem positiveUnitTubularHomeomorph_symm_contMDiff :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(Real, Real)) ∞
      positiveUnitTubularHomeomorph.symm := by
  rw [← ContMDiff.subtypeVal_comp_iff positiveUnitTubularParameterOpen]
  have hIn : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : positiveUnitLatitudeBandOpen →
        equatorialSphericalBandOpen) :=
    contMDiff_subtype_val
  have h := equatorialTubularSmoothInverse_contMDiff.comp hIn
  apply h.congr
  intro point
  apply equatorialTubularDiffeomorph.injective
  change equatorialTubularSmoothMap
      (positiveUnitTubularHomeomorph.symm point).1 =
    equatorialTubularSmoothMap (equatorialTubularSmoothInverse point.1)
  rw [equatorialTubularSmoothMap_inverse]
  exact congrArg Subtype.val
    (positiveUnitTubularHomeomorph.apply_symm_apply point)

/-- Smooth cover-level transition on the collar--cap overlap. -/
def positiveUnitTubularDiffeomorph :
    positiveUnitTubularParameterOpen ≃ₘ^∞⟮
      (𝓡 2).prod 𝓘(Real, Real), 𝓡 3⟯ positiveUnitLatitudeBandOpen where
  toEquiv := positiveUnitTubularHomeomorph.toEquiv
  contMDiff_toFun := positiveUnitTubularHomeomorph_contMDiff
  contMDiff_invFun := positiveUnitTubularHomeomorph_symm_contMDiff

end
end P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
end JanusFormal
