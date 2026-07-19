import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularTailSphereJointSmooth4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D

local instance : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

def equatorialTubularTailEuclidean
    (point : equatorialSphericalBandOpen) : EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm
    (equatorialTubularAmbientInverse point).1

theorem equatorialTubularTailEuclidean_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, EuclideanR3) ∞
      equatorialTubularTailEuclidean := by
  exact (EuclideanSpace.equiv (Fin 3) Real).symm.contDiff.contMDiff.comp
    (contMDiff_fst.comp equatorialTubularAmbientInverse_contMDiff)

theorem equatorialTubularTailEuclidean_eq_equatorialBase
    (point : equatorialSphericalBandOpen) :
    equatorialTubularTailEuclidean point =
      (equatorialTwoSphereHomeomorph
        (equatorialBandBase point.1 point.2)).1 := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  rfl

theorem equatorialTubularTailEuclidean_mem_sphere
    (point : equatorialSphericalBandOpen) :
    equatorialTubularTailEuclidean point ∈
      Metric.sphere (0 : EuclideanR3) 1 := by
  rw [equatorialTubularTailEuclidean_eq_equatorialBase]
  exact (equatorialTwoSphereHomeomorph
    (equatorialBandBase point.1 point.2)).2

def equatorialTubularTailSphere
    (point : equatorialSphericalBandOpen) : StandardEquatorialTwoSphere :=
  ⟨equatorialTubularTailEuclidean point,
    equatorialTubularTailEuclidean_mem_sphere point⟩

theorem equatorialTubularTailSphere_contMDiff :
    ContMDiff (𝓡 3) (𝓡 2) ∞ equatorialTubularTailSphere := by
  exact equatorialTubularTailEuclidean_contMDiff.codRestrict_sphere
    equatorialTubularTailEuclidean_mem_sphere

def equatorialTubularTailEquatorial
    (point : equatorialSphericalBandOpen) : EquatorialTwoSphere :=
  equatorialTwoSphereHomeomorph.symm (equatorialTubularTailSphere point)

theorem equatorialTubularTailEquatorial_contMDiff :
    ContMDiff (𝓡 3) (𝓡 2) ∞ equatorialTubularTailEquatorial := by
  exact (chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
    equatorialTwoSphereHomeomorph).comp equatorialTubularTailSphere_contMDiff

theorem equatorialTubularTailEquatorial_eq_bandBase
    (point : equatorialSphericalBandOpen) :
    equatorialTubularTailEquatorial point = equatorialBandBase point.1 point.2 := by
  apply equatorialTwoSphereHomeomorph.injective
  apply Subtype.ext
  exact equatorialTubularTailEuclidean_eq_equatorialBase point

end
end P0EFTJanusEquatorialTubularTailSphereJointSmooth4D
end JanusFormal
