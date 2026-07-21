import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularRawInverseSmooth4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularRangeEquiv4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D

def EquatorialTubularImage : Set UnitThreeSphere :=
  Set.range equatorialTubularMap

def equatorialTubularMapToImage
    (parameter : EquatorialTubularParameter) : EquatorialTubularImage :=
  ⟨equatorialTubularMap parameter, parameter, rfl⟩

theorem equatorialTubularMapToImage_injective :
    Function.Injective equatorialTubularMapToImage := by
  intro first second h
  apply equatorialTubularMap_injective
  exact congrArg Subtype.val h

def equatorialTubularEquivImage :
    EquatorialTubularParameter ≃ EquatorialTubularImage :=
  Equiv.ofBijective equatorialTubularMapToImage
    ⟨equatorialTubularMapToImage_injective, by
      rintro ⟨point, parameter, rfl⟩
      exact ⟨parameter, rfl⟩⟩

@[simp] theorem equatorialTubularEquivImage_apply
    (parameter : EquatorialTubularParameter) :
    (equatorialTubularEquivImage parameter : UnitThreeSphere) =
      equatorialTubularMap parameter := rfl

@[simp] theorem equatorialTubularEquivImage_symm_apply
    (parameter : EquatorialTubularParameter) :
    equatorialTubularEquivImage.symm
      ⟨equatorialTubularMap parameter, parameter, rfl⟩ = parameter :=
  equatorialTubularEquivImage.left_inv parameter

theorem equatorialTubularEquivImage_symm_normal
    (point : EquatorialTubularImage) :
    (equatorialTubularEquivImage.symm point).2.1 =
      equatorialTubularNormalInverse point.1 := by
  let parameter := equatorialTubularEquivImage.symm point
  have hPoint : equatorialTubularMap parameter = point.1 := by
    exact congrArg Subtype.val (equatorialTubularEquivImage.apply_symm_apply point)
  rw [← hPoint, equatorialTubularNormalInverse_map]

theorem equatorialTubularEquivImage_symm_tail
    (point : EquatorialTubularImage) :
    equatorialTubularTailInverse point.1 =
      (EuclideanSpace.equiv (Fin 3) Real).symm
        (fun index => (equatorialTubularEquivImage.symm point).1.1 index.succ) := by
  let parameter := equatorialTubularEquivImage.symm point
  have hPoint : equatorialTubularMap parameter = point.1 := by
    exact congrArg Subtype.val (equatorialTubularEquivImage.apply_symm_apply point)
  rw [← hPoint, equatorialTubularTailInverse_map]

theorem equatorialTubularEquivImage_inverse_pair :
    Function.LeftInverse equatorialTubularEquivImage.symm equatorialTubularEquivImage ∧
      Function.RightInverse equatorialTubularEquivImage.symm equatorialTubularEquivImage :=
  ⟨equatorialTubularEquivImage.left_inv, equatorialTubularEquivImage.right_inv⟩

end
end P0EFTJanusEquatorialTubularRangeEquiv4D
end JanusFormal
