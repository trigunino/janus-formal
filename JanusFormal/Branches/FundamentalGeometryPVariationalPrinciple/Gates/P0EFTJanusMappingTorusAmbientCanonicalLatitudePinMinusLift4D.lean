import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D

/-!
# Ambient Pin-minus lift of the canonical latitude normal

This gate instantiates the local Clifford/quaternionic construction on the
actual latitude normal of the effective throat cover.  It does not assert a
global nonzero normal on the one-sided quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (fixedEquatorData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (fixedEquatorData period hPeriod)).isLocalHomeomorph

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- Product-coordinate representative of the genuine canonical latitude
normal on the throat cover. -/
def canonicalLatitudeNormalCoordinates
    (anchor : EffectiveThroatCover period hPeriod) : CoverCoordinates :=
  coverProductDerivative period hPeriod
    (fixedThroatCoverInclusion period hPeriod anchor)
    (coverLatitudeNormalVector period hPeriod anchor)

theorem canonicalLatitudeNormalCoordinates_ne_zero
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalLatitudeNormalCoordinates period hPeriod anchor ≠ 0 := by
  intro hZero
  apply coverLatitudeNormalVector_ne_zero period hPeriod anchor
  let equivalence := coverProductDerivativeEquiv period hPeriod
    (fixedThroatCoverInclusion period hPeriod anchor)
  apply equivalence.injective
  have hMap : equivalence (coverLatitudeNormalVector period hPeriod anchor) =
      0 := by
    change canonicalLatitudeNormalCoordinates period hPeriod anchor = 0
    exact hZero
  simpa using hMap

/-- Changing the chosen throat-cover anchor by one deck turn preserves the
raw product-coordinate orientation; the sign reversal belongs to the ambient
chart transition, not to this cover representative itself. -/
theorem canonicalLatitudeNormalCoordinates_oneLoop
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalLatitudeNormalCoordinates period hPeriod ((1 : Int) +ᵥ anchor) =
      canonicalLatitudeNormalCoordinates period hPeriod anchor := by
  rw [canonicalLatitudeNormalCoordinates,
    coverProductDerivative_latitudeNormal,
    canonicalLatitudeNormalCoordinates,
    coverProductDerivative_latitudeNormal]
  have hFiber :
      (((fixedEquatorData period hPeriod).monodromy ^ (1 : Int))
        anchor.fiber) = anchor.fiber := by
    change ((Homeomorph.refl EquatorialTwoSphere) ^ (1 : Int))
        anchor.fiber = anchor.fiber
    rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ (1 : Int))
          anchor.fiber =
        ((Homeomorph.refl EquatorialTwoSphere) ^ (1 : Int)).toEquiv
          anchor.fiber from rfl,
      homeomorph_toEquiv_zpow]
    rw [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
      one_zpow]
    rfl
  have hAnchorFiber : (((1 : Int) +ᵥ anchor).fiber) = anchor.fiber :=
    hFiber
  cases hAnchorFiber
  rfl

/-- All-winding version of the raw cover-anchor invariance. -/
theorem canonicalLatitudeNormalCoordinates_vadd
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    canonicalLatitudeNormalCoordinates period hPeriod (winding +ᵥ anchor) =
      canonicalLatitudeNormalCoordinates period hPeriod anchor := by
  rw [canonicalLatitudeNormalCoordinates,
    coverProductDerivative_latitudeNormal,
    canonicalLatitudeNormalCoordinates,
    coverProductDerivative_latitudeNormal]
  have hMonodromy :
      (fixedEquatorData period hPeriod).monodromy ^ winding = 1 := by
    apply Homeomorph.ext
    intro point
    change ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point = point
    rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point =
        ((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv point from rfl,
      homeomorph_toEquiv_zpow]
    rw [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
      one_zpow]
    rfl
  simp only [vadd_fiber]
  rw [hMonodromy]
  rfl

/-- Genuine local Pin-minus generator of the canonical latitude normal. -/
def canonicalLatitudePinMinusGenerator
    (anchor : EffectiveThroatCover period hPeriod) :
    AmbientCoordinatePinMinusGroup :=
  ambientNormalizedPinMinusGenerator
    (canonicalLatitudeNormalCoordinates period hPeriod anchor)
    (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor)

theorem canonicalLatitudePinMinusGenerator_oneLoop
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalLatitudePinMinusGenerator period hPeriod ((1 : Int) +ᵥ anchor) =
      canonicalLatitudePinMinusGenerator period hPeriod anchor := by
  unfold canonicalLatitudePinMinusGenerator
  simp only [canonicalLatitudeNormalCoordinates_oneLoop]

theorem canonicalLatitudePinMinusGenerator_vadd
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    canonicalLatitudePinMinusGenerator period hPeriod (winding +ᵥ anchor) =
      canonicalLatitudePinMinusGenerator period hPeriod anchor := by
  unfold canonicalLatitudePinMinusGenerator
  simp only [canonicalLatitudeNormalCoordinates_vadd]

/-- Its projection is exactly the quaternionically aligned reflection of the
actual latitude-normal coordinates. -/
theorem canonicalLatitudePinMinusGenerator_projection
    (anchor : EffectiveThroatCover period hPeriod) :
    ambientPinMinusProjection
        (canonicalLatitudePinMinusGenerator period hPeriod anchor) =
      (ambientNormalizedQuaternionAlignedReflection
        (canonicalLatitudeNormalCoordinates period hPeriod anchor)
        (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor)
      ).toLinearEquiv := by
  exact ambientPinMinusProjection_normalizedGenerator_eq_alignedReflection
    (canonicalLatitudeNormalCoordinates period hPeriod anchor)
    (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor)

/-- Integer cyclic lift attached to the actual latitude normal on a cover
chart. -/
def canonicalLatitudePinMinusWindingLift
    (anchor : EffectiveThroatCover period hPeriod) (winding : Int) :
    AmbientCoordinatePinMinusGroup :=
  ambientNormalizedPinMinusWindingLift
    (canonicalLatitudeNormalCoordinates period hPeriod anchor)
    (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor) winding

theorem canonicalLatitudePinMinusWindingLift_anchor_oneLoop
    (anchor : EffectiveThroatCover period hPeriod) (winding : Int) :
    canonicalLatitudePinMinusWindingLift period hPeriod
        ((1 : Int) +ᵥ anchor) winding =
      canonicalLatitudePinMinusWindingLift period hPeriod anchor winding := by
  unfold canonicalLatitudePinMinusWindingLift
  simp only [canonicalLatitudeNormalCoordinates_oneLoop]

theorem canonicalLatitudePinMinusWindingLift_anchor_vadd
    (anchorWinding liftWinding : Int)
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalLatitudePinMinusWindingLift period hPeriod
        (anchorWinding +ᵥ anchor) liftWinding =
      canonicalLatitudePinMinusWindingLift period hPeriod anchor liftWinding := by
  unfold canonicalLatitudePinMinusWindingLift
  simp only [canonicalLatitudeNormalCoordinates_vadd]

theorem canonicalLatitudePinMinusWindingLift_add
    (anchor : EffectiveThroatCover period hPeriod) (first second : Int) :
    canonicalLatitudePinMinusWindingLift period hPeriod anchor (first + second) =
      canonicalLatitudePinMinusWindingLift period hPeriod anchor first *
        canonicalLatitudePinMinusWindingLift period hPeriod anchor second := by
  exact ambientNormalizedPinMinusWindingLift_add
    (canonicalLatitudeNormalCoordinates period hPeriod anchor)
    (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor)
    first second

theorem canonicalLatitudePinMinusWindingLift_projection
    (anchor : EffectiveThroatCover period hPeriod) (winding : Int) :
    ambientPinMinusProjection
        (canonicalLatitudePinMinusWindingLift period hPeriod anchor winding) =
      (ambientNormalizedQuaternionAlignedReflection
        (canonicalLatitudeNormalCoordinates period hPeriod anchor)
        (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor)
      ).toLinearEquiv ^ winding := by
  exact ambientPinMinusProjection_normalizedWindingLift_eq_alignedReflection
    (canonicalLatitudeNormalCoordinates period hPeriod anchor)
    (canonicalLatitudeNormalCoordinates_ne_zero period hPeriod anchor) winding

/-! ## Actual throat-atlas Cech lift -/

/-- Canonical normal coordinates evaluated at the actual local covering
section selected by a throat chart. -/
def canonicalLatitudeSectionNormal
    (chart : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) : CoverCoordinates :=
  canonicalLatitudeNormalCoordinates period hPeriod
    ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt chart base)

theorem canonicalLatitudeSectionNormal_ne_zero
    (chart : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) :
    canonicalLatitudeSectionNormal period hPeriod chart base ≠ 0 :=
  canonicalLatitudeNormalCoordinates_ne_zero period hPeriod _

/-- Ambient Pin-minus transition obtained from the actual throat Cech winding
and the canonical latitude normal in the source local section. -/
def canonicalLatitudeAmbientPinMinusTransitionLift
    (first second : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) :
    AmbientCoordinatePinMinusGroup :=
  ambientNormalizedPinMinusWindingLift
    (canonicalLatitudeSectionNormal period hPeriod first base)
    (canonicalLatitudeSectionNormal_ne_zero period hPeriod first base)
    (localTransitionWinding period hPeriod first second base)

theorem canonicalLatitudeAmbientPinMinusTransitionLift_normalized
    (chart : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod chart) :
    canonicalLatitudeAmbientPinMinusTransitionLift
        period hPeriod chart chart base = 1 := by
  unfold canonicalLatitudeAmbientPinMinusTransitionLift
  rw [localTransitionWinding_self period hPeriod chart base hBase]
  exact ambientNormalizedPinMinusWindingLift_zero _ _

/-- The source normals in two genuine local sections coincide after their
actual deck winding is taken into account. -/
theorem canonicalLatitudeSectionNormal_eq_on_overlap
    (first second : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    canonicalLatitudeSectionNormal period hPeriod second base =
      canonicalLatitudeSectionNormal period hPeriod first base := by
  unfold canonicalLatitudeSectionNormal
  rw [← localTransitionWinding_vadd period hPeriod first second base hBase,
    canonicalLatitudeNormalCoordinates_vadd]

/-- Strict Cech cocycle of the canonical ambient Pin-minus lifts on every
triple overlap of the actual throat atlas. -/
theorem canonicalLatitudeAmbientPinMinusTransitionLift_cocycle
    (first second third : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second ∩
      normalBundleBaseSet period hPeriod third) :
    canonicalLatitudeAmbientPinMinusTransitionLift
        period hPeriod second third base *
      canonicalLatitudeAmbientPinMinusTransitionLift
        period hPeriod first second base =
      canonicalLatitudeAmbientPinMinusTransitionLift
        period hPeriod first third base := by
  unfold canonicalLatitudeAmbientPinMinusTransitionLift
  have hNormal := canonicalLatitudeSectionNormal_eq_on_overlap
    period hPeriod first second base ⟨hBase.1.1, hBase.1.2⟩
  simp only [hNormal]
  rw [← ambientNormalizedPinMinusWindingLift_add,
    localTransitionWinding_add period hPeriod first second third base hBase]

theorem canonicalLatitudeAmbientPinMinusTransitionLift_inverse
    (first second : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    canonicalLatitudeAmbientPinMinusTransitionLift
        period hPeriod second first base =
      (canonicalLatitudeAmbientPinMinusTransitionLift
        period hPeriod first second base)⁻¹ := by
  have hCocycle := canonicalLatitudeAmbientPinMinusTransitionLift_cocycle
    period hPeriod first second first base ⟨⟨hBase.1, hBase.2⟩, hBase.1⟩
  rw [canonicalLatitudeAmbientPinMinusTransitionLift_normalized
    period hPeriod first base hBase.1] at hCocycle
  exact eq_inv_of_mul_eq_one_left hCocycle

/-- The actual one-loop throat transition has the defining Pin-minus square:
its lift squares to the nontrivial central sign. -/
theorem canonicalLatitudeAmbientPinMinusTransitionLift_oneLoop_square
    (anchor : EffectiveThroatCover period hPeriod) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    canonicalLatitudeAmbientPinMinusTransitionLift period hPeriod
        anchor ((1 : Int) +ᵥ anchor) base *
      canonicalLatitudeAmbientPinMinusTransitionLift period hPeriod
        anchor ((1 : Int) +ᵥ anchor) base =
      ambientPinMinusCentralSign := by
  dsimp only
  let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
  unfold canonicalLatitudeAmbientPinMinusTransitionLift
  rw [localTransitionWinding_one_loop period hPeriod anchor]
  simp only [ambientNormalizedPinMinusWindingLift,
    ambientPinMinusUnitNormalWindingLift, zpow_one]
  exact ambientNormalizedPinMinusGenerator_square
    (canonicalLatitudeSectionNormal period hPeriod anchor base)
    (canonicalLatitudeSectionNormal_ne_zero period hPeriod anchor base)

/-- Projection of the actual-winding Cech lift is the corresponding power of
the canonical aligned latitude reflection. -/
theorem canonicalLatitudeAmbientPinMinusTransitionLift_projection
    (first second : EffectiveThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) :
    ambientPinMinusProjection
        (canonicalLatitudeAmbientPinMinusTransitionLift
          period hPeriod first second base) =
      (ambientNormalizedQuaternionAlignedReflection
        (canonicalLatitudeSectionNormal period hPeriod first base)
        (canonicalLatitudeSectionNormal_ne_zero period hPeriod first base)
      ).toLinearEquiv ^
        localTransitionWinding period hPeriod first second base := by
  exact ambientPinMinusProjection_normalizedWindingLift_eq_alignedReflection
    (canonicalLatitudeSectionNormal period hPeriod first base)
    (canonicalLatitudeSectionNormal_ne_zero period hPeriod first base)
    (localTransitionWinding period hPeriod first second base)

end

end P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D
end JanusFormal
