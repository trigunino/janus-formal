import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D

/-!
# Explicit inverse of the equatorial tubular latitude map

The open spherical band `|x₀| < 1` is exactly parametrized by

`(u,nu) ↦ (sin nu, cos nu • u)`

with `u ∈ S²` and `-pi/2 < nu < pi/2`.  The inverse is

* `nu = arcsin x₀`;
* `u = tail(x) / cos nu`.

This file proves that the reconstructed tail has unit norm, packages the two
inverse directions into an equivalence, and identifies the range of the
latitude map with the open non-polar band.  These are the coordinate facts
needed for local smoothness of the global Cauchy extension.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D

private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1

/-- The open non-polar band of the algebraic unit three-sphere. -/
def EquatorialTubularBand :=
  {point : UnitThreeSphere // |point.1 0| < 1}

/-- The arcsine inverse belongs to the canonical open normal interval. -/
def equatorialTubularNormalInverseSubtype
    (point : EquatorialTubularBand) :
    Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨equatorialTubularNormalInverse point.1, by
    constructor
    · exact Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp point.2).1
    · exact Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp point.2).2⟩

/-- The denominator occurring in the inverse tail is positive on the open
band. -/
theorem cos_equatorialTubularNormalInverse_pos
    (point : EquatorialTubularBand) :
    0 < Real.cos (equatorialTubularNormalInverse point.1) :=
  Real.cos_pos_of_mem_Ioo
    (equatorialTubularNormalInverseSubtype point).2

/-- The reconstructed equatorial tail has unit Euclidean norm. -/
theorem equatorialTubularTailInverse_norm
    (point : EquatorialTubularBand) :
    ‖equatorialTubularTailInverse point.1‖ = 1 := by
  let x : Real := point.1.1 0
  let c : Real := Real.cos (Real.arcsin x)
  have hBand : |x| < 1 := point.2
  have hLower : -1 < x := (abs_lt.mp hBand).1
  have hUpper : x < 1 := (abs_lt.mp hBand).2
  have hDenPositive : 0 < 1 - x ^ 2 := by
    have hProduct : 0 < (1 - x) * (1 + x) :=
      mul_pos (sub_pos.mpr hUpper) (by linarith)
    nlinarith
  have hSphere := point.1.2
  unfold OnUnitThreeSphere radiusSquared at hSphere
  rw [Fin.sum_univ_succ] at hSphere
  have hTail :
      (∑ index : Fin 3, point.1.1 index.succ ^ 2) = 1 - x ^ 2 := by
    dsimp [x]
    nlinarith
  have hCosSquare : c ^ 2 = 1 - x ^ 2 := by
    dsimp [c]
    rw [Real.cos_arcsin, Real.sq_sqrt hDenPositive.le]
  have hNormSquare : ‖equatorialTubularTailInverse point.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ index : Fin 3,
      (point.1.1 index.succ / c) ^ 2) = 1
    simp_rw [div_pow]
    rw [← Finset.sum_div, hTail, hCosSquare]
    exact div_self hDenPositive.ne'
  nlinarith [norm_nonneg (equatorialTubularTailInverse point.1)]

/-- Standard `S²` point reconstructed from the normalized tail. -/
def equatorialTubularStandardBaseInverse
    (point : EquatorialTubularBand) : StandardSphere2 :=
  ⟨equatorialTubularTailInverse point.1, by
    rw [Metric.mem_sphere, dist_zero_right,
      equatorialTubularTailInverse_norm point]⟩

/-- Algebraic equatorial point reconstructed from the normalized tail. -/
def equatorialTubularBaseInverse
    (point : EquatorialTubularBand) : EquatorialTwoSphere :=
  equatorialTwoSphereHomeomorph.symm
    (equatorialTubularStandardBaseInverse point)

/-- Full inverse tubular parameter. -/
def equatorialTubularMapInverse
    (point : EquatorialTubularBand) : EquatorialTubularParameter :=
  (equatorialTubularBaseInverse point,
    equatorialTubularNormalInverseSubtype point)

/-- The inverse recovers the normal parameter. -/
theorem equatorialTubularMapInverse_normal
    (parameter : EquatorialTubularParameter) :
    (equatorialTubularMapInverse
      ⟨equatorialTubularMap parameter, by
        have hCos : 0 < Real.cos parameter.2.1 :=
          Real.cos_pos_of_mem_Ioo parameter.2.2
        have hSquare : Real.sin parameter.2.1 ^ 2 < 1 := by
          nlinarith [Real.sin_sq_add_cos_sq parameter.2.1, sq_pos_of_pos hCos]
        have hAbsNonnegative : 0 ≤ |Real.sin parameter.2.1| := abs_nonneg _
        have hAbsSquare : |Real.sin parameter.2.1| ^ 2 < 1 := by
          simpa [sq_abs] using hSquare
        change |Real.sin parameter.2.1| < 1
        nlinarith⟩).2.1 = parameter.2.1 :=
  equatorialTubularMap_normal_inverse parameter

/-- The inverse recovers the equatorial base. -/
theorem equatorialTubularMapInverse_base
    (parameter : EquatorialTubularParameter) :
    (equatorialTubularMapInverse
      ⟨equatorialTubularMap parameter, by
        have hCos : 0 < Real.cos parameter.2.1 :=
          Real.cos_pos_of_mem_Ioo parameter.2.2
        have hSquare : Real.sin parameter.2.1 ^ 2 < 1 := by
          nlinarith [Real.sin_sq_add_cos_sq parameter.2.1, sq_pos_of_pos hCos]
        have hAbsNonnegative : 0 ≤ |Real.sin parameter.2.1| := abs_nonneg _
        have hAbsSquare : |Real.sin parameter.2.1| ^ 2 < 1 := by
          simpa [sq_abs] using hSquare
        change |Real.sin parameter.2.1| < 1
        nlinarith⟩).1 = parameter.1 := by
  apply equatorialTwoSphereHomeomorph.injective
  rw [equatorialTubularMapInverse, equatorialTubularBaseInverse,
    Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact equatorialTubularTailInverse_map parameter

/-- Left inverse identity. -/
theorem equatorialTubularMapInverse_left
    (parameter : EquatorialTubularParameter) :
    equatorialTubularMapInverse
      ⟨equatorialTubularMap parameter, by
        have hCos : 0 < Real.cos parameter.2.1 :=
          Real.cos_pos_of_mem_Ioo parameter.2.2
        have hSquare : Real.sin parameter.2.1 ^ 2 < 1 := by
          nlinarith [Real.sin_sq_add_cos_sq parameter.2.1, sq_pos_of_pos hCos]
        have hAbsNonnegative : 0 ≤ |Real.sin parameter.2.1| := abs_nonneg _
        have hAbsSquare : |Real.sin parameter.2.1| ^ 2 < 1 := by
          simpa [sq_abs] using hSquare
        change |Real.sin parameter.2.1| < 1
        nlinarith⟩ = parameter := by
  apply Prod.ext
  · exact equatorialTubularMapInverse_base parameter
  · apply Subtype.ext
    exact equatorialTubularMapInverse_normal parameter

/-- Reconstructing a band point gives the original sphere point. -/
theorem equatorialTubularMap_inverse
    (point : EquatorialTubularBand) :
    equatorialTubularMap (equatorialTubularMapInverse point) = point.1 := by
  apply Subtype.ext
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · change Real.sin (Real.arcsin (point.1.1 0)) = point.1.1 0
    exact Real.sin_arcsin
      (le_of_lt (abs_lt.mp point.2).1)
      (le_of_lt (abs_lt.mp point.2).2)
  · change Real.cos (Real.arcsin (point.1.1 0)) *
        (equatorialTubularBaseInverse point).1 tail.succ =
      point.1.1 tail.succ
    rw [equatorialTubularBaseInverse,
      equatorialTwoSphereHomeomorph_symm_tail]
    change Real.cos (Real.arcsin (point.1.1 0)) *
        ((EuclideanSpace.equiv (Fin 3) Real)
          (equatorialTubularTailInverse point.1)) tail =
      point.1.1 tail.succ
    have hCos : Real.cos (Real.arcsin (point.1.1 0)) ≠ 0 := by
      simpa [equatorialTubularNormalInverse] using
        (cos_equatorialTubularNormalInverse_pos point).ne'
    simp [equatorialTubularTailInverse, equatorialTubularNormalInverse]
    field_simp [hCos]

/-- Equivalence between tubular parameters and the open spherical band. -/
def equatorialTubularEquivBand :
    EquatorialTubularParameter ≃ EquatorialTubularBand where
  toFun parameter :=
    ⟨equatorialTubularMap parameter, by
      have hCos : 0 < Real.cos parameter.2.1 :=
        Real.cos_pos_of_mem_Ioo parameter.2.2
      have hSquare : Real.sin parameter.2.1 ^ 2 < 1 := by
        nlinarith [Real.sin_sq_add_cos_sq parameter.2.1, sq_pos_of_pos hCos]
      have hAbsNonnegative : 0 ≤ |Real.sin parameter.2.1| := abs_nonneg _
      have hAbsSquare : |Real.sin parameter.2.1| ^ 2 < 1 := by
        simpa [sq_abs] using hSquare
      change |Real.sin parameter.2.1| < 1
      nlinarith⟩
  invFun := equatorialTubularMapInverse
  left_inv := equatorialTubularMapInverse_left
  right_inv := by
    intro point
    apply Subtype.ext
    exact equatorialTubularMap_inverse point

/-- The latitude map has exactly the open non-polar band as its range. -/
theorem range_equatorialTubularMap :
    Set.range equatorialTubularMap =
      {point : UnitThreeSphere | |point.1 0| < 1} := by
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    exact (equatorialTubularEquivBand parameter).2
  · intro hPoint
    exact ⟨equatorialTubularMapInverse ⟨point, hPoint⟩,
      equatorialTubularMap_inverse ⟨point, hPoint⟩⟩

/-- Inverse-coordinate certificate. -/
theorem equatorialTubularCoverInverse_certificate :
    Function.Bijective
        (equatorialTubularEquivBand :
          EquatorialTubularParameter → EquatorialTubularBand) ∧
      Set.range equatorialTubularMap =
        {point : UnitThreeSphere | |point.1 0| < 1} :=
  ⟨(equatorialTubularEquivBand :
      EquatorialTubularParameter ≃ EquatorialTubularBand).bijective,
    range_equatorialTubularMap⟩

end
end P0EFTJanusMappingTorusEquatorialTubularCoverInverse4D
end JanusFormal
