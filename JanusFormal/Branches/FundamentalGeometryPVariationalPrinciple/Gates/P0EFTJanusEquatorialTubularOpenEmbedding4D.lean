import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularHomeomorph4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularOpenEmbedding4D
set_option autoImplicit false
noncomputable section
open Topology
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularRangeEquiv4D
open P0EFTJanusEquatorialTubularHomeomorph4D

def EquatorialSphericalBand : Set UnitThreeSphere :=
  {point | |point.1 0| < 1}

def equatorialBandNormal (point : UnitThreeSphere)
    (hPoint : point ∈ EquatorialSphericalBand) :
    Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨Real.arcsin (point.1 0),
    Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hPoint).1,
    Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp hPoint).2⟩

def equatorialBandBase (point : UnitThreeSphere)
    (hPoint : point ∈ EquatorialSphericalBand) : EquatorialTwoSphere :=
  ⟨Fin.cases 0 (fun index => point.1 index.succ /
      Real.cos (Real.arcsin (point.1 0))), by
    constructor
    · unfold OnUnitThreeSphere radiusSquared
      rw [Fin.sum_univ_succ]
      have hZero : (Fin.cases 0 (fun index => point.1 index.succ /
          Real.cos (Real.arcsin (point.1 0))) : Fin 4 → Real) 0 = 0 := rfl
      rw [hZero, zero_pow (by norm_num), zero_add]
      simp only [Fin.cases_succ, div_pow]
      have hSphere := point.2
      unfold OnUnitThreeSphere radiusSquared at hSphere
      rw [Fin.sum_univ_succ] at hSphere
      have hCosSq : Real.cos (Real.arcsin (point.1 0)) ^ 2 =
          1 - point.1 0 ^ 2 := by
        have hSin := Real.sin_arcsin (abs_lt.mp hPoint).1.le
          (abs_lt.mp hPoint).2.le
        calc
          _ = 1 - Real.sin (Real.arcsin (point.1 0)) ^ 2 := by
            nlinarith [Real.sin_sq_add_cos_sq (Real.arcsin (point.1 0))]
          _ = _ := by rw [hSin]
      have hCos : Real.cos (Real.arcsin (point.1 0)) ≠ 0 := by
        exact (Real.cos_pos_of_mem_Ioo
          (equatorialBandNormal point hPoint).2).ne'
      change ∑ x : Fin 3, point.1 x.succ ^ 2 /
        Real.cos (Real.arcsin (point.1 0)) ^ 2 = 1
      rw [← Finset.sum_div, hCosSq]
      have hTail : (∑ x : Fin 3, point.1 x.succ ^ 2) =
          1 - point.1 0 ^ 2 := by linarith
      rw [hTail]
      exact div_self (by rw [← hCosSq]; exact pow_ne_zero 2 hCos)
    · rfl⟩

theorem equatorialTubularMap_equatorialBandParameter
    (point : UnitThreeSphere) (hPoint : point ∈ EquatorialSphericalBand) :
    equatorialTubularMap
      (equatorialBandBase point hPoint, equatorialBandNormal point hPoint) = point := by
  apply Subtype.ext
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · exact Real.sin_arcsin (abs_lt.mp hPoint).1.le (abs_lt.mp hPoint).2.le
  · change Real.cos (Real.arcsin (point.1 0)) *
      (point.1 tail.succ / Real.cos (Real.arcsin (point.1 0))) = point.1 tail.succ
    have hCos :=
      (Real.cos_pos_of_mem_Ioo (equatorialBandNormal point hPoint).2).ne'
    unfold equatorialBandNormal at hCos
    field_simp [hCos]

theorem equatorialTubularImage_eq_band :
    EquatorialTubularImage = EquatorialSphericalBand := by
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    change |Real.sin parameter.2.1| < 1
    rw [abs_lt]
    have hCos := Real.cos_pos_of_mem_Ioo parameter.2.2
    have hCosSq : 0 < Real.cos parameter.2.1 ^ 2 := sq_pos_of_pos hCos
    constructor <;>
      nlinarith [Real.sin_sq_add_cos_sq parameter.2.1]
  · intro hPoint
    exact ⟨(equatorialBandBase point hPoint, equatorialBandNormal point hPoint),
      equatorialTubularMap_equatorialBandParameter point hPoint⟩

theorem equatorialTubularImage_isOpen : IsOpen EquatorialTubularImage := by
  rw [equatorialTubularImage_eq_band]
  exact isOpen_lt continuous_abs continuous_const |>.preimage
    ((continuous_apply 0).comp continuous_subtype_val)

theorem equatorialTubularMap_openEmbedding :
    IsOpenEmbedding equatorialTubularMap := by
  constructor
  · exact equatorialTubularImage_isOpen.isOpenEmbedding_subtypeVal.isEmbedding.comp
      equatorialTubularHomeomorphImage.isEmbedding
  · simpa [EquatorialTubularImage] using equatorialTubularImage_isOpen

end
end P0EFTJanusEquatorialTubularOpenEmbedding4D
end JanusFormal
