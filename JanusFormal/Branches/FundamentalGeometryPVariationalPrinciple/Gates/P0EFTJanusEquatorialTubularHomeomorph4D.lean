import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularRangeEquiv4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularHomeomorph4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularRangeEquiv4D

instance : TopologicalSpace EquatorialTubularParameter :=
  inferInstanceAs (TopologicalSpace
    (EquatorialTwoSphere × Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))

theorem equatorialTubularMap_continuous :
    Continuous equatorialTubularMap := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro index
  refine Fin.cases ?_ (fun tail => ?_) index
  · exact Real.continuous_sin.comp
      (continuous_subtype_val.comp continuous_snd)
  · exact (Real.continuous_cos.comp
      (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply tail.succ).comp
          (continuous_subtype_val.comp continuous_fst))

theorem equatorialTubularMapToImage_continuous :
    Continuous equatorialTubularMapToImage :=
  equatorialTubularMap_continuous.subtype_mk _

theorem equatorialTubularTailInverse_continuousOnImage :
    Continuous (fun point : EquatorialTubularImage =>
      equatorialTubularTailInverse point.1) := by
  apply (EuclideanSpace.equiv (Fin 3) Real).symm.continuous.comp
  apply continuous_pi
  intro index
  have hNumerator : Continuous (fun point : EquatorialTubularImage =>
      point.1.1 index.succ) :=
    (continuous_apply index.succ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hDenominator : Continuous (fun point : EquatorialTubularImage =>
      Real.cos (equatorialTubularNormalInverse point.1)) :=
    Real.continuous_cos.comp
      (equatorialTubularNormalInverse_continuous.comp continuous_subtype_val)
  exact hNumerator.div hDenominator fun point => by
    rcases point.2 with ⟨parameter, hParameter⟩
    rw [← hParameter, equatorialTubularNormalInverse_map]
    exact (Real.cos_pos_of_mem_Ioo parameter.2.2).ne'

theorem equatorialTubularEquivImage_symm_first_continuous :
    Continuous (fun point : EquatorialTubularImage =>
      (equatorialTubularEquivImage.symm point).1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro index
  refine Fin.cases ?_ (fun tail => ?_) index
  · convert continuous_const using 1
    funext point
    exact (equatorialTubularEquivImage.symm point).1.2.2
  · have hTail := (continuous_apply tail).comp
      ((EuclideanSpace.equiv (Fin 3) Real).continuous.comp
        equatorialTubularTailInverse_continuousOnImage)
    convert hTail using 1
    funext point
    have h := equatorialTubularEquivImage_symm_tail point
    simpa using
      (congrFun (congrArg (EuclideanSpace.equiv (Fin 3) Real) h) tail).symm

theorem equatorialTubularEquivImage_symm_continuous :
    Continuous equatorialTubularEquivImage.symm := by
  apply equatorialTubularEquivImage_symm_first_continuous.prodMk
  apply Continuous.subtype_mk
  convert equatorialTubularNormalInverse_continuous.comp continuous_subtype_val using 1
  funext point
  exact equatorialTubularEquivImage_symm_normal point

def equatorialTubularHomeomorphImage :
    EquatorialTubularParameter ≃ₜ EquatorialTubularImage where
  toEquiv := equatorialTubularEquivImage
  continuous_toFun := equatorialTubularMapToImage_continuous
  continuous_invFun := equatorialTubularEquivImage_symm_continuous

end
end P0EFTJanusEquatorialTubularHomeomorph4D
end JanusFormal
