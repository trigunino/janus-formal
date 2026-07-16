import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusPTInvolution

/-!
# The two sides of the reflected-sphere throat

The equatorial `S^2` separates the concrete unit `S^3` into the two open
sign domains of the reflected coordinate.  Reflection exchanges those
domains.  On the effective mapping torus a single deck iterate also exchanges
them, so their quotient images coincide: the throat is one-sided in this
precise topological sense.

No claim that either sign domain is a connected component is made here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusThroatComplementSides

set_option autoImplicit false

open Set
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution

/-- The positive side of the equatorial throat in the concrete unit sphere. -/
def positiveSphereSide : Set UnitThreeSphere :=
  {point | 0 < point.1 0}

/-- The negative side of the equatorial throat in the concrete unit sphere. -/
def negativeSphereSide : Set UnitThreeSphere :=
  {point | point.1 0 < 0}

/-- The equatorial locus viewed as a subset of the concrete unit sphere. -/
def sphereThroat : Set UnitThreeSphere :=
  Set.range equatorialSphereInclusion

/-- Concrete pole on the positive side. -/
def positivePole : UnitThreeSphere :=
  ⟨fun index => if index = 0 then 1 else 0, by
    simp [OnUnitThreeSphere, radiusSquared]⟩

/-- Concrete pole on the negative side. -/
def negativePole : UnitThreeSphere :=
  ⟨fun index => if index = 0 then -1 else 0, by
    simp [OnUnitThreeSphere, radiusSquared]⟩

theorem positiveSphereSide_nonempty : positiveSphereSide.Nonempty := by
  exact ⟨positivePole, by simp [positivePole, positiveSphereSide]⟩

theorem negativeSphereSide_nonempty : negativeSphereSide.Nonempty := by
  exact ⟨negativePole, by simp [negativePole, negativeSphereSide]⟩

theorem mem_sphereThroat_iff (point : UnitThreeSphere) :
    point ∈ sphereThroat ↔ point.1 0 = 0 := by
  constructor
  · rintro ⟨equator, rfl⟩
    exact equator.2.2
  · intro hZero
    refine ⟨⟨point.1, point.2, hZero⟩, ?_⟩
    rfl

theorem positiveSphereSide_isOpen : IsOpen positiveSphereSide := by
  exact isOpen_lt continuous_const
    ((continuous_apply (0 : Fin 4)).comp continuous_subtype_val)

theorem negativeSphereSide_isOpen : IsOpen negativeSphereSide := by
  exact isOpen_lt
    ((continuous_apply (0 : Fin 4)).comp continuous_subtype_val)
    continuous_const

theorem sphereThroat_isClosed : IsClosed sphereThroat := by
  rw [show sphereThroat =
      {point : UnitThreeSphere | point.1 0 = 0} from by
        ext point
        exact mem_sphereThroat_iff point]
  exact isClosed_eq
    ((continuous_apply (0 : Fin 4)).comp continuous_subtype_val)
    continuous_const

theorem sphere_complement_eq_two_sides :
    sphereThroatᶜ = positiveSphereSide ∪ negativeSphereSide := by
  ext point
  rw [mem_compl_iff, mem_sphereThroat_iff]
  simp only [positiveSphereSide, negativeSphereSide, mem_union, mem_setOf_eq]
  constructor
  · intro hNonzero
    rcases lt_trichotomy (point.1 0) 0 with hNegative | hZero | hPositive
    · exact Or.inr hNegative
    · exact False.elim (hNonzero hZero)
    · exact Or.inl hPositive
  · rintro (hPositive | hNegative) hZero <;> linarith

theorem positive_negative_disjoint :
    Disjoint positiveSphereSide negativeSphereSide := by
  rw [Set.disjoint_left]
  intro point hPositive hNegative
  change 0 < point.1 0 at hPositive
  change point.1 0 < 0 at hNegative
  linarith

@[simp] theorem sphereReflection_first_coordinate (point : UnitThreeSphere) :
    (sphereReflection point).1 0 = -point.1 0 := by
  rfl

theorem sphereReflection_mem_positive_iff (point : UnitThreeSphere) :
    sphereReflection point ∈ positiveSphereSide ↔ point ∈ negativeSphereSide := by
  change 0 < -point.1 0 ↔ point.1 0 < 0
  exact neg_pos

theorem sphereReflection_mem_negative_iff (point : UnitThreeSphere) :
    sphereReflection point ∈ negativeSphereSide ↔ point ∈ positiveSphereSide := by
  change -point.1 0 < 0 ↔ 0 < point.1 0
  exact neg_lt_zero

theorem sphereReflection_image_positive :
    sphereReflection '' positiveSphereSide = negativeSphereSide := by
  ext point
  constructor
  · rintro ⟨source, hSource, rfl⟩
    exact (sphereReflection_mem_negative_iff source).2 hSource
  · intro hPoint
    refine ⟨sphereReflection point, ?_, ?_⟩
    · exact (sphereReflection_mem_positive_iff point).2 hPoint
    · exact sphereReflection.apply_symm_apply point

theorem sphereReflection_image_negative :
    sphereReflection '' negativeSphereSide = positiveSphereSide := by
  ext point
  constructor
  · rintro ⟨source, hSource, rfl⟩
    exact (sphereReflection_mem_positive_iff source).2 hSource
  · intro hPoint
    refine ⟨sphereReflection point, ?_, ?_⟩
    · exact (sphereReflection_mem_negative_iff point).2 hPoint
    · exact sphereReflection.apply_symm_apply point

section MappingTorus

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod

/-- Positive representatives in the product cover. -/
def positiveCoverSide : Set (MappingTorusCover (sphereData period hPeriod)) :=
  {point | point.fiber ∈ positiveSphereSide}

/-- Negative representatives in the product cover. -/
def negativeCoverSide : Set (MappingTorusCover (sphereData period hPeriod)) :=
  {point | point.fiber ∈ negativeSphereSide}

/-- The prequotient throat, characterized directly by the reflected coordinate. -/
def coverThroat : Set (MappingTorusCover (sphereData period hPeriod)) :=
  {point | point.fiber.1 0 = 0}

theorem cover_complement_eq_two_sides :
    (coverThroat period hPeriod)ᶜ =
      positiveCoverSide period hPeriod ∪ negativeCoverSide period hPeriod := by
  ext point
  simp only [coverThroat, positiveCoverSide, negativeCoverSide, mem_compl_iff,
    mem_setOf_eq, mem_union, positiveSphereSide, negativeSphereSide]
  constructor
  · intro hNonzero
    rcases lt_trichotomy (point.fiber.1 0) 0 with hNegative | hZero | hPositive
    · exact Or.inr hNegative
    · exact False.elim (hNonzero hZero)
    · exact Or.inl hPositive
  · rintro (hPositive | hNegative) hZero <;> linarith

theorem positiveCoverSide_isOpen : IsOpen (positiveCoverSide period hPeriod) :=
  positiveSphereSide_isOpen.preimage (continuous_fiber _)

theorem negativeCoverSide_isOpen : IsOpen (negativeCoverSide period hPeriod) :=
  negativeSphereSide_isOpen.preimage (continuous_fiber _)

theorem coverThroat_isClosed : IsClosed (coverThroat period hPeriod) := by
  rw [show coverThroat period hPeriod =
      MappingTorusCover.fiber ⁻¹' sphereThroat from by
        ext point
        simp [coverThroat, mem_sphereThroat_iff]]
  exact sphereThroat_isClosed.preimage (continuous_fiber _)

/-- One generator of the deck action swaps the positive and negative sides. -/
theorem one_vadd_mem_negative_iff (point : MappingTorusCover (sphereData period hPeriod)) :
    (1 : ℤ) +ᵥ point ∈ negativeCoverSide period hPeriod ↔
      point ∈ positiveCoverSide period hPeriod := by
  change sphereReflection point.fiber ∈ negativeSphereSide ↔
    point.fiber ∈ positiveSphereSide
  exact sphereReflection_mem_negative_iff point.fiber

/-- One generator of the deck action swaps the negative and positive sides. -/
theorem one_vadd_mem_positive_iff (point : MappingTorusCover (sphereData period hPeriod)) :
    (1 : ℤ) +ᵥ point ∈ positiveCoverSide period hPeriod ↔
      point ∈ negativeCoverSide period hPeriod := by
  change sphereReflection point.fiber ∈ positiveSphereSide ↔
    point.fiber ∈ negativeSphereSide
  exact sphereReflection_mem_positive_iff point.fiber

/-- The actual throat inside the effective reflected-sphere mapping torus. -/
def effectiveThroat : Set (MappingTorus (sphereData period hPeriod)) :=
  Set.range (fixedThroatQuotientInclusion period hPeriod)

/-- The inverse image of the effective throat is exactly the equatorial cover locus. -/
theorem mappingTorusMk_preimage_effectiveThroat :
    mappingTorusMk (sphereData period hPeriod) ⁻¹' effectiveThroat period hPeriod =
      coverThroat period hPeriod := by
  ext point
  constructor
  · rintro ⟨throatPoint, hPoint⟩
    refine Quotient.inductionOn throatPoint ?_ hPoint
    intro representative hRepresentative
    rw [fixedThroatQuotientInclusion_mk] at hRepresentative
    have hReverse := hRepresentative.symm
    rw [mappingTorusMk_eq_iff_exists_vadd] at hReverse
    rcases hReverse with ⟨winding, hWinding⟩
    have hIncluded :
        fixedThroatCoverInclusion period hPeriod (winding +ᵥ representative) = point := by
      rw [fixedThroatCoverInclusion_equivariant]
      exact hWinding
    change point.fiber.1 0 = 0
    rw [← hIncluded]
    exact (winding +ᵥ representative).fiber.2.2
  · intro hPoint
    change point.fiber.1 0 = 0 at hPoint
    let equator : EquatorialTwoSphere := ⟨point.fiber.1, point.fiber.2, hPoint⟩
    let representative : MappingTorusCover (fixedEquatorData period hPeriod) :=
      ⟨equator, point.time⟩
    refine ⟨mappingTorusMk (fixedEquatorData period hPeriod) representative, ?_⟩
    rw [fixedThroatQuotientInclusion_mk]
    congr

/-- A quotient point is off the throat exactly when each representative lies
in one of the two sign domains. -/
theorem mappingTorusMk_mem_effectiveThroat_compl_iff
    (point : MappingTorusCover (sphereData period hPeriod)) :
    mappingTorusMk (sphereData period hPeriod) point ∈
        (effectiveThroat period hPeriod)ᶜ ↔
      point ∈ positiveCoverSide period hPeriod ∪ negativeCoverSide period hPeriod := by
  rw [← cover_complement_eq_two_sides period hPeriod]
  simp only [mem_compl_iff]
  exact not_congr
    (Set.ext_iff.mp (mappingTorusMk_preimage_effectiveThroat period hPeriod) point)

private theorem mappingTorusMk_one_vadd
    (point : MappingTorusCover (sphereData period hPeriod)) :
    mappingTorusMk (sphereData period hPeriod) ((1 : ℤ) +ᵥ point) =
      mappingTorusMk (sphereData period hPeriod) point := by
  rw [mappingTorusMk_eq_iff_exists_vadd]
  exact ⟨1, rfl⟩

/-- Every off-throat quotient point has a positive-side representative. -/
theorem image_positiveCoverSide_eq_effective_complement :
    mappingTorusMk (sphereData period hPeriod) '' positiveCoverSide period hPeriod =
      (effectiveThroat period hPeriod)ᶜ := by
  ext quotientPoint
  constructor
  · rintro ⟨point, hPositive, rfl⟩
    exact (mappingTorusMk_mem_effectiveThroat_compl_iff period hPeriod point).2
      (Or.inl hPositive)
  · intro hComplement
    rcases mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint with
      ⟨point, rfl⟩
    have hSides :=
      (mappingTorusMk_mem_effectiveThroat_compl_iff period hPeriod point).1 hComplement
    rcases hSides with hPositive | hNegative
    · exact ⟨point, hPositive, rfl⟩
    · refine ⟨(1 : ℤ) +ᵥ point,
        (one_vadd_mem_positive_iff period hPeriod point).2 hNegative, ?_⟩
      exact mappingTorusMk_one_vadd period hPeriod point

/-- Every off-throat quotient point also has a negative-side representative. -/
theorem image_negativeCoverSide_eq_effective_complement :
    mappingTorusMk (sphereData period hPeriod) '' negativeCoverSide period hPeriod =
      (effectiveThroat period hPeriod)ᶜ := by
  ext quotientPoint
  constructor
  · rintro ⟨point, hNegative, rfl⟩
    exact (mappingTorusMk_mem_effectiveThroat_compl_iff period hPeriod point).2
      (Or.inr hNegative)
  · intro hComplement
    rcases mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint with
      ⟨point, rfl⟩
    have hSides :=
      (mappingTorusMk_mem_effectiveThroat_compl_iff period hPeriod point).1 hComplement
    rcases hSides with hPositive | hNegative
    · refine ⟨(1 : ℤ) +ᵥ point,
        (one_vadd_mem_negative_iff period hPeriod point).2 hPositive, ?_⟩
      exact mappingTorusMk_one_vadd period hPeriod point
    · exact ⟨point, hNegative, rfl⟩

/-- Hence the two distinct cover sides become the same subset after quotienting. -/
theorem quotient_images_of_sides_coincide :
    mappingTorusMk (sphereData period hPeriod) '' positiveCoverSide period hPeriod =
      mappingTorusMk (sphereData period hPeriod) '' negativeCoverSide period hPeriod := by
  rw [image_positiveCoverSide_eq_effective_complement,
    image_negativeCoverSide_eq_effective_complement]

/-- Time reversal preserves each sign domain before quotienting. -/
theorem timeReverseCover_mem_positive_iff
    (point : MappingTorusCover (sphereData period hPeriod)) :
    timeReverseCover (sphereData period hPeriod) point ∈ positiveCoverSide period hPeriod ↔
      point ∈ positiveCoverSide period hPeriod :=
  Iff.rfl

theorem timeReverseCover_mem_negative_iff
    (point : MappingTorusCover (sphereData period hPeriod)) :
    timeReverseCover (sphereData period hPeriod) point ∈ negativeCoverSide period hPeriod ↔
      point ∈ negativeCoverSide period hPeriod :=
  Iff.rfl

/-- The quotient PT involution preserves the effective throat complement. -/
theorem reflectedSpherePT_mem_effective_complement_iff
    (point : MappingTorus (sphereData period hPeriod)) :
    reflectedSpherePT period hPeriod point ∈ (effectiveThroat period hPeriod)ᶜ ↔
      point ∈ (effectiveThroat period hPeriod)ᶜ := by
  refine Quotient.inductionOn point ?_
  intro representative
  change mappingTorusTimeReversal (sphereData period hPeriod) sphereReflection_symm
      (mappingTorusMk (sphereData period hPeriod) representative) ∈
        (effectiveThroat period hPeriod)ᶜ ↔ _
  rw [mappingTorusTimeReversal_mk]
  rw [mappingTorusMk_mem_effectiveThroat_compl_iff,
    mappingTorusMk_mem_effectiveThroat_compl_iff]
  rfl

/-- A PT image of a positive representative has an equivalent negative
representative, obtained by one deck iterate. -/
theorem reflectedSpherePT_positive_has_negative_representative
    (point : MappingTorusCover (sphereData period hPeriod))
    (hPositive : point ∈ positiveCoverSide period hPeriod) :
    ∃ negativeRepresentative ∈ negativeCoverSide period hPeriod,
      mappingTorusMk (sphereData period hPeriod) negativeRepresentative =
        reflectedSpherePT period hPeriod
          (mappingTorusMk (sphereData period hPeriod) point) := by
  refine ⟨(1 : ℤ) +ᵥ timeReverseCover (sphereData period hPeriod) point, ?_, ?_⟩
  · exact (one_vadd_mem_negative_iff period hPeriod _).2 hPositive
  · rw [mappingTorusMk_one_vadd]
    change mappingTorusMk (sphereData period hPeriod)
        (timeReverseCover (sphereData period hPeriod) point) =
      mappingTorusTimeReversal (sphereData period hPeriod) sphereReflection_symm
        (mappingTorusMk (sphereData period hPeriod) point)
    rw [mappingTorusTimeReversal_mk]

end MappingTorus

end P0EFTJanusMappingTorusThroatComplementSides
end JanusFormal
