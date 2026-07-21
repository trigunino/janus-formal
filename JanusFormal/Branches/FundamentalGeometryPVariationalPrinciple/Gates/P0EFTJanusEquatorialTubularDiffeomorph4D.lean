import Mathlib.Geometry.Manifold.Diffeomorph
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularTailSphereJointSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularDiffeomorph4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff
open TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularTailSphereJointSmooth4D

def equatorialTubularNormalOpen : Opens Real :=
  ⟨Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), isOpen_Ioo⟩

def equatorialTubularNormalSmooth
    (point : equatorialSphericalBandOpen) : equatorialTubularNormalOpen :=
  ⟨(equatorialTubularAmbientInverse point).2,
    Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp point.2).1,
    Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp point.2).2⟩

theorem equatorialTubularNormalSmooth_eq_bandNormal
    (point : equatorialSphericalBandOpen) :
    equatorialTubularNormalSmooth point = equatorialBandNormal point.1 point.2 := by
  apply Subtype.ext
  change (equatorialTubularAmbientInverse point).2 = Real.arcsin (point.1.1 0)
  rw [equatorialTubularAmbientInverse_eq]
  rfl

theorem equatorialTubularNormalSmooth_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ equatorialTubularNormalSmooth := by
  rw [← ContMDiff.subtypeVal_comp_iff equatorialTubularNormalOpen]
  exact contMDiff_snd.comp equatorialTubularAmbientInverse_contMDiff

def equatorialTubularSmoothInverse
    (point : equatorialSphericalBandOpen) :
    EquatorialTwoSphere × equatorialTubularNormalOpen :=
  (equatorialTubularTailEquatorial point, equatorialTubularNormalSmooth point)

theorem equatorialTubularSmoothInverse_contMDiff :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(Real, Real)) ∞
      equatorialTubularSmoothInverse :=
  equatorialTubularTailEquatorial_contMDiff.prodMk
    equatorialTubularNormalSmooth_contMDiff

def equatorialTubularSmoothMap
    (parameter : EquatorialTwoSphere × equatorialTubularNormalOpen) :
    equatorialSphericalBandOpen :=
  ⟨equatorialLatitude parameter.1 parameter.2.1, by
    change |Real.sin parameter.2.1| < 1
    rw [abs_lt]
    have hCos := Real.cos_pos_of_mem_Ioo parameter.2.2
    have hCosSq : 0 < Real.cos parameter.2.1 ^ 2 := sq_pos_of_pos hCos
    constructor <;> nlinarith [Real.sin_sq_add_cos_sq parameter.2.1]⟩

theorem equatorialTubularSmoothMap_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      equatorialTubularSmoothMap := by
  have hNormal : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (Subtype.val : equatorialTubularNormalOpen → Real) :=
    contMDiff_subtype_val
  have hInput : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (fun parameter : EquatorialTwoSphere × equatorialTubularNormalOpen =>
        (parameter.1, parameter.2.1)) :=
    contMDiff_fst.prodMk (hNormal.comp contMDiff_snd)
  have hLatitude := equatorialLatitude_joint_contMDiff.comp hInput
  rw [← ContMDiff.subtypeVal_comp_iff equatorialSphericalBandOpen]
  exact hLatitude

theorem equatorialTubularSmoothMap_inverse
    (point : equatorialSphericalBandOpen) :
    equatorialTubularSmoothMap (equatorialTubularSmoothInverse point) = point := by
  apply Subtype.ext
  rw [equatorialTubularSmoothMap, equatorialTubularSmoothInverse,
    equatorialTubularTailEquatorial_eq_bandBase,
    equatorialTubularNormalSmooth_eq_bandNormal]
  exact equatorialTubularMap_equatorialBandParameter point.1 point.2

theorem equatorialTubularSmoothInverse_map
    (parameter : EquatorialTwoSphere × equatorialTubularNormalOpen) :
    equatorialTubularSmoothInverse (equatorialTubularSmoothMap parameter) = parameter := by
  apply equatorialTubularMap_injective
  exact congrArg Subtype.val
    (equatorialTubularSmoothMap_inverse (equatorialTubularSmoothMap parameter))

def equatorialTubularDiffeomorph :
    (EquatorialTwoSphere × equatorialTubularNormalOpen) ≃ₘ^∞⟮
      (𝓡 2).prod 𝓘(Real, Real), 𝓡 3⟯ equatorialSphericalBandOpen where
  toFun := equatorialTubularSmoothMap
  invFun := equatorialTubularSmoothInverse
  left_inv := equatorialTubularSmoothInverse_map
  right_inv := equatorialTubularSmoothMap_inverse
  contMDiff_toFun := equatorialTubularSmoothMap_contMDiff
  contMDiff_invFun := equatorialTubularSmoothInverse_contMDiff

end
end P0EFTJanusEquatorialTubularDiffeomorph4D
end JanusFormal
