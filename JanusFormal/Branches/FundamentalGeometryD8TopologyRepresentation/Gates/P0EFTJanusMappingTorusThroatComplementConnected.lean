import Mathlib.Analysis.Convex.PathConnected
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusThroatComplementSides

/-!
# Connected complement of the effective one-sided throat

Radial normalization of the affine segment to a pole gives explicit paths
inside each open sign side of the concrete unit three-sphere.  The positive
cover side is consequently path connected, and its continuous quotient image
is the entire effective throat complement.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusThroatComplementConnected

set_option autoImplicit false

noncomputable section

open Set unitInterval
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusThroatComplementSides

/-- Affine interpolation from a sphere point to the positive pole, before
radial normalization. -/
def affineToPositivePole (point : UnitThreeSphere) (t : ℝ) : R4Point :=
  (1 - t) • point.1 + t • positivePole.1

@[simp] theorem affineToPositivePole_zero (point : UnitThreeSphere) :
    affineToPositivePole point 0 = point.1 := by
  simp [affineToPositivePole]

@[simp] theorem affineToPositivePole_one (point : UnitThreeSphere) :
    affineToPositivePole point 1 = positivePole.1 := by
  simp [affineToPositivePole]

@[simp] theorem affineToPositivePole_first_coordinate
    (point : UnitThreeSphere) (t : ℝ) :
    affineToPositivePole point t 0 = (1 - t) * point.1 0 + t := by
  simp [affineToPositivePole, positivePole]

theorem affineToPositivePole_first_coordinate_pos
    (point : UnitThreeSphere) (hPositive : point ∈ positiveSphereSide)
    (t : I) :
    0 < affineToPositivePole point t 0 := by
  rw [affineToPositivePole_first_coordinate]
  change 0 < point.1 0 at hPositive
  by_cases ht : (t : ℝ) = 0
  · simp [ht, hPositive]
  · have htPositive : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.2.2) hPositive.le) htPositive

theorem radiusSquared_pos_of_first_coordinate_pos
    (vector : R4Point) (hFirst : 0 < vector 0) :
    0 < radiusSquared vector := by
  simp only [radiusSquared, Fin.sum_univ_four]
  nlinarith [sq_nonneg (vector 1), sq_nonneg (vector 2), sq_nonneg (vector 3)]

theorem radiusSquared_smul (coefficient : ℝ) (vector : R4Point) :
    radiusSquared (coefficient • vector) =
      coefficient ^ 2 * radiusSquared vector := by
  simp [radiusSquared, Finset.mul_sum, mul_pow]

/-- Radial normalization for a vector with nonzero squared radius. -/
def normalizeRadius (vector : R4Point) : R4Point :=
  (Real.sqrt (radiusSquared vector))⁻¹ • vector

theorem normalizeRadius_on_unit_sphere
    (vector : R4Point) (hRadius : 0 < radiusSquared vector) :
    OnUnitThreeSphere (normalizeRadius vector) := by
  have hSqrt : Real.sqrt (radiusSquared vector) ≠ 0 :=
    (Real.sqrt_pos.2 hRadius).ne'
  unfold OnUnitThreeSphere normalizeRadius
  rw [radiusSquared_smul]
  calc
    (Real.sqrt (radiusSquared vector))⁻¹ ^ 2 * radiusSquared vector =
        (Real.sqrt (radiusSquared vector))⁻¹ ^ 2 *
          Real.sqrt (radiusSquared vector) ^ 2 := by
            congr 1
            exact (Real.sq_sqrt hRadius.le).symm
    _ = 1 := by field_simp

theorem normalizeRadius_first_coordinate_pos
    (vector : R4Point) (hFirst : 0 < vector 0) :
    0 < normalizeRadius vector 0 := by
  have hRadius := radiusSquared_pos_of_first_coordinate_pos vector hFirst
  have hScale : 0 < (Real.sqrt (radiusSquared vector))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 hRadius)
  change 0 < (Real.sqrt (radiusSquared vector))⁻¹ * vector 0
  exact mul_pos hScale hFirst

theorem continuous_radiusSquared : Continuous radiusSquared := by
  unfold radiusSquared
  fun_prop

/-- Normalized affine path from a positive-side point to the positive pole. -/
def positivePolePath
    (point : UnitThreeSphere) (hPositive : point ∈ positiveSphereSide) :
    Path point positivePole where
  toFun t :=
    ⟨normalizeRadius (affineToPositivePole point t),
      normalizeRadius_on_unit_sphere _
        (radiusSquared_pos_of_first_coordinate_pos _
          (affineToPositivePole_first_coordinate_pos point hPositive t))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hAffine : Continuous (fun t : I => affineToPositivePole point t) := by
      unfold affineToPositivePole
      fun_prop
    have hRadius : Continuous
        (fun t : I => Real.sqrt (radiusSquared (affineToPositivePole point t))) :=
      (continuous_radiusSquared.comp hAffine).sqrt
    have hNonzero : ∀ t : I,
        Real.sqrt (radiusSquared (affineToPositivePole point t)) ≠ 0 := by
      intro t
      exact (Real.sqrt_pos.2
        (radiusSquared_pos_of_first_coordinate_pos _
          (affineToPositivePole_first_coordinate_pos point hPositive t))).ne'
    exact (hRadius.inv₀ hNonzero).smul hAffine
  source' := by
    apply Subtype.ext
    change normalizeRadius (affineToPositivePole point (0 : ℝ)) = point.1
    rw [affineToPositivePole_zero]
    unfold normalizeRadius
    rw [point.2]
    simp
  target' := by
    apply Subtype.ext
    change normalizeRadius (affineToPositivePole point (1 : ℝ)) = positivePole.1
    rw [affineToPositivePole_one]
    unfold normalizeRadius
    rw [positivePole.2]
    simp

theorem positivePolePath_mem_positiveSphereSide
    (point : UnitThreeSphere) (hPositive : point ∈ positiveSphereSide)
    (t : I) :
    positivePolePath point hPositive t ∈ positiveSphereSide := by
  change 0 < normalizeRadius (affineToPositivePole point t) 0
  exact normalizeRadius_first_coordinate_pos _
    (affineToPositivePole_first_coordinate_pos point hPositive t)

/-- The positive open side is path connected. -/
theorem positiveSphereSide_isPathConnected : IsPathConnected positiveSphereSide := by
  refine ⟨positivePole, by simp [positivePole, positiveSphereSide], ?_⟩
  intro point hPositive
  let path := positivePolePath point hPositive
  refine ⟨path.symm, ?_⟩
  rw [← range_subset_iff, Path.symm_range]
  rintro _ ⟨t, rfl⟩
  exact positivePolePath_mem_positiveSphereSide point hPositive t

/-- Reflection transfers path connectedness to the negative open side. -/
theorem negativeSphereSide_isPathConnected : IsPathConnected negativeSphereSide := by
  have hImage := positiveSphereSide_isPathConnected.image sphereReflection.continuous
  rwa [sphereReflection_image_positive] at hImage

theorem positiveSphereSide_subset_throat_complement :
    positiveSphereSide ⊆ sphereThroatᶜ := by
  rw [sphere_complement_eq_two_sides]
  exact subset_union_left

theorem negativeSphereSide_subset_throat_complement :
    negativeSphereSide ⊆ sphereThroatᶜ := by
  rw [sphere_complement_eq_two_sides]
  exact subset_union_right

/-- The positive sign side is exactly one connected component of the sphere
complement, not merely a connected open subset. -/
theorem connectedComponentIn_throat_complement_positivePole :
    connectedComponentIn sphereThroatᶜ positivePole = positiveSphereSide := by
  apply Subset.antisymm
  · have hCover : connectedComponentIn sphereThroatᶜ positivePole ⊆
        positiveSphereSide ∪ negativeSphereSide := by
      rw [← sphere_complement_eq_two_sides]
      exact connectedComponentIn_subset _ _
    rcases IsPreconnected.subset_or_subset positiveSphereSide_isOpen
        negativeSphereSide_isOpen positive_negative_disjoint hCover
        isPreconnected_connectedComponentIn with hPositive | hNegative
    · exact hPositive
    · exfalso
      have hPole : positivePole ∈ connectedComponentIn sphereThroatᶜ positivePole :=
        mem_connectedComponentIn (positiveSphereSide_subset_throat_complement
          (by simp [positivePole, positiveSphereSide]))
      have := hNegative hPole
      norm_num [positivePole, negativeSphereSide] at this
  · exact positiveSphereSide_isPathConnected.isConnected.isPreconnected
      |>.subset_connectedComponentIn
        (by simp [positivePole, positiveSphereSide])
        positiveSphereSide_subset_throat_complement

/-- The negative sign side is the other connected component. -/
theorem connectedComponentIn_throat_complement_negativePole :
    connectedComponentIn sphereThroatᶜ negativePole = negativeSphereSide := by
  apply Subset.antisymm
  · have hCover : connectedComponentIn sphereThroatᶜ negativePole ⊆
        positiveSphereSide ∪ negativeSphereSide := by
      rw [← sphere_complement_eq_two_sides]
      exact connectedComponentIn_subset _ _
    rcases IsPreconnected.subset_or_subset positiveSphereSide_isOpen
        negativeSphereSide_isOpen positive_negative_disjoint hCover
        isPreconnected_connectedComponentIn with hPositive | hNegative
    · exfalso
      have hPole : negativePole ∈ connectedComponentIn sphereThroatᶜ negativePole :=
        mem_connectedComponentIn (negativeSphereSide_subset_throat_complement
          (by simp [negativePole, negativeSphereSide]))
      have := hPositive hPole
      norm_num [negativePole, positiveSphereSide] at this
    · exact hNegative
  · exact negativeSphereSide_isPathConnected.isConnected.isPreconnected
      |>.subset_connectedComponentIn
        (by simp [negativePole, negativeSphereSide])
        negativeSphereSide_subset_throat_complement

section MappingTorus

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod

/-- The positive side in the product cover is path connected. -/
theorem positiveCoverSide_isPathConnected :
    IsPathConnected (positiveCoverSide period hPeriod) := by
  let base : MappingTorusCover (sphereData period hPeriod) :=
    ⟨positivePole, 0⟩
  refine ⟨base, by simp [base, positiveCoverSide, positivePole,
    positiveSphereSide], ?_⟩
  intro point hPositive
  have hSphere : JoinedIn positiveSphereSide positivePole point.fiber :=
    positiveSphereSide_isPathConnected.joinedIn _
      (by simp [positivePole, positiveSphereSide]) _ hPositive
  have hTime : Joined (0 : ℝ) point.time := PathConnectedSpace.joined 0 point.time
  let path : Path base point :=
    { toFun := fun t => ⟨hSphere.somePath t, hTime.somePath t⟩
      continuous_toFun := by
        have hProduct :=
          hSphere.somePath.continuous.prodMk hTime.somePath.continuous
        exact ((coverHomeomorphProd
          (sphereData period hPeriod)).symm.continuous.comp hProduct).congr
            fun _ => rfl
      source' := by
        apply MappingTorusCover.ext <;> simp [base]
      target' := by
        apply MappingTorusCover.ext <;> simp }
  exact ⟨path, fun t => hSphere.somePath_mem t⟩

/-- The effective throat complement is path connected, because it is exactly
the continuous quotient image of the positive cover side. -/
theorem effectiveThroat_complement_isPathConnected :
    IsPathConnected ((effectiveThroat period hPeriod)ᶜ) := by
  have hMk : Continuous (mappingTorusMk (sphereData period hPeriod)) :=
    continuous_quotient_mk'
  have hImage := (positiveCoverSide_isPathConnected period hPeriod).image
    hMk
  rwa [image_positiveCoverSide_eq_effective_complement] at hImage

/-- In particular the effective throat complement is connected. -/
theorem effectiveThroat_complement_isConnected :
    IsConnected ((effectiveThroat period hPeriod)ᶜ) :=
  (effectiveThroat_complement_isPathConnected period hPeriod).isConnected

end MappingTorus

end

end P0EFTJanusMappingTorusThroatComplementConnected
end JanusFormal
