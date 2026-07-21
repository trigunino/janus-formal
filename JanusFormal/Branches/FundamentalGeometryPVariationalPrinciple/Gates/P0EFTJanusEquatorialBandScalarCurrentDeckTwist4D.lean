import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D

/-!
# Deck sign of the globally extended latitude scalar current

The scalar Green-current density contains one derivative in the latitude
normal.  The reflected-sphere deck generator reverses that normal, so the
globally smooth zero extension is anti-invariant, not an ordinary scalar on
the mapping-torus quotient.
-/

namespace JanusFormal
namespace P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff Topology
open Set TopologicalSpace
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D
open P0EFTJanusNormalBundleOrientationCover

variable (period : Real) (hPeriod : period ≠ 0)

local instance : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

def canonicalLatitudeBaseDeckGenerator
    (base : CanonicalLatitudeBase) : CanonicalLatitudeBase :=
  (base.1, base.2 + period)

def canonicalLatitudeParameterDeckGenerator
    (parameter : CanonicalLatitudeParameter) : CanonicalLatitudeParameter :=
  (canonicalLatitudeBaseDeckGenerator period parameter.1, -parameter.2)

theorem canonicalLatitudeAnchor_deck_generator
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeAnchor period hPeriod
        (canonicalLatitudeBaseDeckGenerator period base) =
      (1 : Int) +ᵥ canonicalLatitudeAnchor period hPeriod base := by
  apply MappingTorusCover.ext
  · rfl
  · simp [canonicalLatitudeAnchor, canonicalLatitudeBaseDeckGenerator,
      fixedEquatorData]

theorem canonicalLatitudeValue_deck_generator
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeValue period hPeriod field
        (canonicalLatitudeBaseDeckGenerator period base) normal =
      canonicalLatitudeValue period hPeriod field base (-normal) := by
  unfold canonicalLatitudeValue canonicalNormalSlice
  rw [canonicalLatitudeAnchor_deck_generator]
  congr 1
  exact quotientNormalLatitude_deck_generator period hPeriod
    (canonicalLatitudeAnchor period hPeriod base) normal

theorem canonicalLatitudeDerivative_deck_generator
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeDerivative period hPeriod field
        (canonicalLatitudeBaseDeckGenerator period base) normal =
      -canonicalLatitudeDerivative period hPeriod field base (-normal) := by
  have hValue : canonicalLatitudeValue period hPeriod field
      (canonicalLatitudeBaseDeckGenerator period base) =
        fun current => canonicalLatitudeValue period hPeriod field base (-current) := by
    funext current
    exact canonicalLatitudeValue_deck_generator period hPeriod field base current
  unfold canonicalLatitudeDerivative
  rw [hValue, deriv_comp_neg]

theorem jointCutoffCollarScalarCurrentDensity_deck_generator
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) :
    jointCutoffCollarScalarCurrentDensity period hPeriod field test
        (canonicalLatitudeParameterDeckGenerator period parameter) =
      -jointCutoffCollarScalarCurrentDensity period hPeriod field test parameter := by
  rw [jointCutoffCollarScalarCurrentDensity_eq,
    jointCutoffCollarScalarCurrentDensity_eq]
  unfold cutoffCollarScalarCurrentDensity canonicalLatitudeScalarGreenCurrent
  dsimp only [canonicalLatitudeParameterDeckGenerator]
  rw [canonicalLatitudeValue_deck_generator,
    canonicalLatitudeValue_deck_generator,
    canonicalLatitudeDerivative_deck_generator,
    canonicalLatitudeDerivative_deck_generator]
  simp only [neg_neg]
  rw [canonicalLatitudeCollarCutoff.neg]
  ring

def equatorialTubularNormalReflection
    (normal : equatorialTubularNormalOpen) : equatorialTubularNormalOpen :=
  ⟨-normal.1, by
    constructor <;> linarith [normal.2.1, normal.2.2]⟩

def equatorialTubularParameterReflection
    (parameter : EquatorialTwoSphere × equatorialTubularNormalOpen) :
    EquatorialTwoSphere × equatorialTubularNormalOpen :=
  (parameter.1, equatorialTubularNormalReflection parameter.2)

def equatorialSphericalBandReflection
    (point : equatorialSphericalBandOpen) : equatorialSphericalBandOpen :=
  ⟨sphereReflection point.1, by
    have hPoint : |point.1.1 0| < 1 := by
      exact point.2
    change |(sphereReflection point.1).1 0| < 1
    change |-point.1.1 0| < 1
    simpa only [abs_neg] using hPoint⟩

theorem equatorialTubularSmoothMap_parameterReflection
    (parameter : EquatorialTwoSphere × equatorialTubularNormalOpen) :
    equatorialTubularSmoothMap
        (equatorialTubularParameterReflection parameter) =
      equatorialSphericalBandReflection
        (equatorialTubularSmoothMap parameter) := by
  apply Subtype.ext
  exact (sphereReflection_equatorialLatitude parameter.1 parameter.2.1).symm

theorem equatorialTubularSmoothInverse_reflection
    (point : equatorialSphericalBandOpen) :
    equatorialTubularSmoothInverse
        (equatorialSphericalBandReflection point) =
      equatorialTubularParameterReflection
        (equatorialTubularSmoothInverse point) := by
  apply equatorialTubularMap_injective
  exact congrArg Subtype.val
    (show equatorialTubularSmoothMap
          (equatorialTubularSmoothInverse
            (equatorialSphericalBandReflection point)) =
        equatorialTubularSmoothMap
          (equatorialTubularParameterReflection
            (equatorialTubularSmoothInverse point)) by
      rw [equatorialTubularSmoothMap_inverse,
        equatorialTubularSmoothMap_parameterReflection,
        equatorialTubularSmoothMap_inverse])

def equatorialBandSpacetimeDeckGenerator
    (input : equatorialSphericalBandOpen × Real) :
    equatorialSphericalBandOpen × Real :=
  (equatorialSphericalBandReflection input.1, input.2 + period)

theorem equatorialBandCanonicalParameter_deck_generator
    (input : equatorialSphericalBandOpen × Real) :
    equatorialBandCanonicalParameter
        (equatorialBandSpacetimeDeckGenerator period input) =
      canonicalLatitudeParameterDeckGenerator period
        (equatorialBandCanonicalParameter input) := by
  rw [equatorialBandCanonicalParameter, equatorialBandCanonicalParameter,
    equatorialBandSpacetimeDeckGenerator,
    equatorialTubularSmoothInverse_reflection]
  rfl

theorem equatorialBandScalarCurrentDensity_deck_generator
    (field test : SmoothQuotientField period hPeriod Real)
    (input : equatorialSphericalBandOpen × Real) :
    equatorialBandScalarCurrentDensity period hPeriod field test
        (equatorialBandSpacetimeDeckGenerator period input) =
      -equatorialBandScalarCurrentDensity period hPeriod field test input := by
  unfold equatorialBandScalarCurrentDensity
  rw [equatorialBandCanonicalParameter_deck_generator,
    jointCutoffCollarScalarCurrentDensity_deck_generator]

theorem sphereReflection_mem_equatorialSphericalBand_iff
    (point : UnitThreeSphere) :
    sphereReflection point ∈ EquatorialSphericalBand ↔
      point ∈ EquatorialSphericalBand := by
  change |(sphereReflection point).1 0| < 1 ↔ |point.1 0| < 1
  change |-point.1 0| < 1 ↔ |point.1 0| < 1
  rw [abs_neg]

theorem reflectedSphereProductDeck_one
    (input : UnitThreeSphere × Real) :
    reflectedSphereProductDeck period 1 input =
      (sphereReflection input.1, input.2 + period) := by
  simp only [reflectedSphereProductDeck, zpow_one, Int.cast_one, one_mul]
  rfl

theorem reflectedSphereProductDeck_add
    (first second : Int) (input : UnitThreeSphere × Real) :
    reflectedSphereProductDeck period (first + second) input =
      reflectedSphereProductDeck period first
        (reflectedSphereProductDeck period second input) := by
  apply Prod.ext
  · simp [reflectedSphereProductDeck, zpow_add]
  · simp [reflectedSphereProductDeck]
    ring

@[simp]
theorem reflectedSphereProductDeck_zero
    (input : UnitThreeSphere × Real) :
    reflectedSphereProductDeck period 0 input = input := by
  rcases input with ⟨point, time⟩
  unfold reflectedSphereProductDeck
  simp

theorem equatorialBandScalarCurrentZeroExtension_deck_generator
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real) :
    equatorialBandScalarCurrentZeroExtension period hPeriod field test
        (reflectedSphereProductDeck period 1 input) =
      -equatorialBandScalarCurrentZeroExtension period hPeriod field test input := by
  rw [reflectedSphereProductDeck_one]
  by_cases hInput : input.1 ∈ EquatorialSphericalBand
  · have hDeck : sphereReflection input.1 ∈ EquatorialSphericalBand :=
      (sphereReflection_mem_equatorialSphericalBand_iff input.1).2 hInput
    rw [equatorialBandScalarCurrentZeroExtension_eq_on_band
        period hPeriod field test (sphereReflection input.1, input.2 + period) hDeck,
      equatorialBandScalarCurrentZeroExtension_eq_on_band
        period hPeriod field test input hInput]
    have hBandPoint :
        (⟨sphereReflection input.1, hDeck⟩ : equatorialSphericalBandOpen) =
          equatorialSphericalBandReflection ⟨input.1, hInput⟩ := by
      rfl
    rw [hBandPoint]
    exact equatorialBandScalarCurrentDensity_deck_generator
      period hPeriod field test (⟨input.1, hInput⟩, input.2)
  · have hDeck : sphereReflection input.1 ∉ EquatorialSphericalBand := by
      rwa [sphereReflection_mem_equatorialSphericalBand_iff]
    simp [equatorialBandScalarCurrentZeroExtension, hInput, hDeck]

/-- Smooth cover presentation of a coefficient in the real sign local
system.  This records the exact associated-line twist required for descent;
it does not identify that line with an ordinary scalar bundle. -/
structure SmoothAmbientNormalSignLift where
  toFun : UnitThreeSphere × Real → Real
  contMDiff_toFun :
    ContMDiff
      ((modelWithCornersSelf Real EuclideanR3).prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ toFun
  deck_generator_sign : ∀ input,
    toFun (reflectedSphereProductDeck period 1 input) =
      (normalSignRepresentation 1 : Real) * toFun input

instance : CoeFun (SmoothAmbientNormalSignLift period)
    (fun _ => UnitThreeSphere × Real → Real) :=
  ⟨SmoothAmbientNormalSignLift.toFun⟩

theorem SmoothAmbientNormalSignLift.deck_sign
    (lift : SmoothAmbientNormalSignLift period)
    (winding : Int) (input : UnitThreeSphere × Real) :
    lift (reflectedSphereProductDeck period winding input) =
      (normalSignRepresentation winding : Real) * lift input := by
  have hInverse (current : UnitThreeSphere × Real) :
      lift (reflectedSphereProductDeck period (-1) current) = -lift current := by
    have hGenerator := lift.deck_generator_sign
      (reflectedSphereProductDeck period (-1) current)
    rw [← reflectedSphereProductDeck_add] at hGenerator
    norm_num only at hGenerator
    rw [reflectedSphereProductDeck_zero] at hGenerator
    simp [normalSignRepresentation] at hGenerator
    linarith
  let motive : Int → Prop := fun current => ∀ point,
    lift (reflectedSphereProductDeck period current point) =
      (normalSignRepresentation current : Real) * lift point
  have hAll : motive winding := by
    refine Int.inductionOn' winding 0 ?_ (fun current _ ih => ?_)
      (fun current _ ih => ?_)
    · intro point
      rw [reflectedSphereProductDeck_zero]
      simp [normalSignRepresentation]
    · intro point
      rw [reflectedSphereProductDeck_add, ih,
        lift.deck_generator_sign, normal_sign_add]
      simp only [Units.val_mul]
      ring
    · intro point
      rw [show current - 1 = current + (-1 : Int) by omega,
        reflectedSphereProductDeck_add, ih, hInverse,
        normal_sign_add]
      simp only [Units.val_mul]
      simp [normalSignRepresentation]
  exact hAll input

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

/-- Associated-sign-line cover over the actual reflected-sphere cover. -/
@[ext]
structure AmbientNormalSignCover where
  base : EffectiveCover period hPeriod
  coefficient : Real

def ambientNormalSignVAdd (winding : Int)
    (point : AmbientNormalSignCover period hPeriod) :
    AmbientNormalSignCover period hPeriod where
  base := winding +ᵥ point.base
  coefficient := (normalSignRepresentation winding : Real) * point.coefficient

instance : VAdd Int (AmbientNormalSignCover period hPeriod) :=
  ⟨ambientNormalSignVAdd period hPeriod⟩

instance : AddAction Int (AmbientNormalSignCover period hPeriod) where
  zero_vadd point := by
    change ambientNormalSignVAdd period hPeriod 0 point = point
    apply AmbientNormalSignCover.ext
    · simp [ambientNormalSignVAdd]
    · simp [ambientNormalSignVAdd, normalSignRepresentation]
  add_vadd first second point := by
    change ambientNormalSignVAdd period hPeriod (first + second) point =
      ambientNormalSignVAdd period hPeriod first
        (ambientNormalSignVAdd period hPeriod second point)
    apply AmbientNormalSignCover.ext
    · simp [ambientNormalSignVAdd, add_vadd]
    · simp [ambientNormalSignVAdd, normal_sign_add]
      ring

/-- Actual orbit quotient presenting the real sign local system over the
four-dimensional mapping torus.  No identification with an ordinary scalar
bundle is asserted. -/
abbrev AmbientNormalSignOrbitLine :=
  AddAction.orbitRel.Quotient Int (AmbientNormalSignCover period hPeriod)

abbrev ambientNormalSignLineMk :
    AmbientNormalSignCover period hPeriod →
      AmbientNormalSignOrbitLine period hPeriod :=
  Quotient.mk (AddAction.orbitRel Int (AmbientNormalSignCover period hPeriod))

def ambientNormalSignLineProjection :
    AmbientNormalSignOrbitLine period hPeriod →
      EffectiveQuotient period hPeriod :=
  Quotient.map AmbientNormalSignCover.base fun first second hOrbit => by
    change AddAction.orbitRel Int (AmbientNormalSignCover period hPeriod)
      first second at hOrbit
    change AddAction.orbitRel Int (EffectiveCover period hPeriod)
      first.base second.base
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    exact ⟨winding, congrArg AmbientNormalSignCover.base hWinding⟩

@[simp]
theorem ambientNormalSignLineProjection_mk
    (point : AmbientNormalSignCover period hPeriod) :
    ambientNormalSignLineProjection period hPeriod
        (ambientNormalSignLineMk period hPeriod point) =
      mappingTorusMk (reflectedSphereData period hPeriod) point.base :=
  rfl

theorem coverHomeomorphProd_vadd_eq_reflectedSphereProductDeck
    (winding : Int) (point : EffectiveCover period hPeriod) :
    coverHomeomorphProd (reflectedSphereData period hPeriod) (winding +ᵥ point) =
      reflectedSphereProductDeck period winding
        (coverHomeomorphProd (reflectedSphereData period hPeriod) point) := by
  unfold reflectedSphereProductDeck
  apply Prod.ext
  · rfl
  · change point.time + (winding : Real) *
        (reflectedSphereData period hPeriod).period =
      point.time + (winding : Real) * period
    rfl

def ambientNormalSignCoverPoint
    (lift : SmoothAmbientNormalSignLift period)
    (point : EffectiveCover period hPeriod) :
    AmbientNormalSignCover period hPeriod where
  base := point
  coefficient := lift
    (coverHomeomorphProd (reflectedSphereData period hPeriod) point)

theorem ambientNormalSignCoverPoint_vadd
    (lift : SmoothAmbientNormalSignLift period)
    (winding : Int) (point : EffectiveCover period hPeriod) :
    ambientNormalSignCoverPoint period hPeriod lift (winding +ᵥ point) =
      winding +ᵥ ambientNormalSignCoverPoint period hPeriod lift point := by
  apply AmbientNormalSignCover.ext
  · rfl
  · change lift
        (coverHomeomorphProd (reflectedSphereData period hPeriod)
          (winding +ᵥ point)) =
      (normalSignRepresentation winding : Real) * lift
        (coverHomeomorphProd (reflectedSphereData period hPeriod) point)
    rw [coverHomeomorphProd_vadd_eq_reflectedSphereProductDeck]
    exact SmoothAmbientNormalSignLift.deck_sign period lift winding _

/-- A smooth equivariant lift gives a genuine section of the associated
orbit line.  Smoothness is certified upstairs; registering the orbit line as
a Mathlib smooth vector bundle remains a separate construction. -/
def ambientNormalSignOrbitSection
    (lift : SmoothAmbientNormalSignLift period) :
    EffectiveQuotient period hPeriod →
      AmbientNormalSignOrbitLine period hPeriod :=
  Quotient.map (ambientNormalSignCoverPoint period hPeriod lift)
    fun first second hOrbit => by
      change AddAction.orbitRel Int (EffectiveCover period hPeriod)
        first second at hOrbit
      change AddAction.orbitRel Int (AmbientNormalSignCover period hPeriod)
        (ambientNormalSignCoverPoint period hPeriod lift first)
        (ambientNormalSignCoverPoint period hPeriod lift second)
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
      rcases hOrbit with ⟨winding, hWinding⟩
      refine ⟨winding, ?_⟩
      rw [← ambientNormalSignCoverPoint_vadd, hWinding]

@[simp]
theorem ambientNormalSignOrbitSection_mk
    (lift : SmoothAmbientNormalSignLift period)
    (point : EffectiveCover period hPeriod) :
    ambientNormalSignOrbitSection period hPeriod lift
        (mappingTorusMk (reflectedSphereData period hPeriod) point) =
      ambientNormalSignLineMk period hPeriod
        (ambientNormalSignCoverPoint period hPeriod lift point) :=
  rfl

theorem ambientNormalSignOrbitSection_isSection
    (lift : SmoothAmbientNormalSignLift period) :
    ambientNormalSignLineProjection period hPeriod ∘
        ambientNormalSignOrbitSection period hPeriod lift = id := by
  funext quotientPoint
  induction quotientPoint using Quotient.inductionOn with
  | _ point => rfl

def equatorialBandScalarCurrentNormalSignLift
    (field test : SmoothQuotientField period hPeriod Real) :
    SmoothAmbientNormalSignLift period where
  toFun := equatorialBandScalarCurrentZeroExtension period hPeriod field test
  contMDiff_toFun := equatorialBandScalarCurrentZeroExtension_contMDiff
    period hPeriod field test
  deck_generator_sign := by
    intro input
    rw [equatorialBandScalarCurrentZeroExtension_deck_generator]
    simp [normalSignRepresentation]

def equatorialBandScalarCurrentNormalSignSection
    (field test : SmoothQuotientField period hPeriod Real) :
    EffectiveQuotient period hPeriod →
      AmbientNormalSignOrbitLine period hPeriod :=
  ambientNormalSignOrbitSection period hPeriod
    (equatorialBandScalarCurrentNormalSignLift period hPeriod field test)

theorem equatorialBandScalarCurrentNormalSignSection_isSection
    (field test : SmoothQuotientField period hPeriod Real) :
    ambientNormalSignLineProjection period hPeriod ∘
        equatorialBandScalarCurrentNormalSignSection period hPeriod field test = id :=
  ambientNormalSignOrbitSection_isSection period hPeriod _

theorem equatorialBandScalarCurrentZeroExtension_eq_zero_of_scalarDeckInvariant
    (field test : SmoothQuotientField period hPeriod Real)
    (hScalarInvariant : ∀ input,
      equatorialBandScalarCurrentZeroExtension period hPeriod field test
          (reflectedSphereProductDeck period 1 input) =
        equatorialBandScalarCurrentZeroExtension period hPeriod field test input) :
    equatorialBandScalarCurrentZeroExtension period hPeriod field test = 0 := by
  funext input
  change equatorialBandScalarCurrentZeroExtension period hPeriod field test input = 0
  have hAnti := equatorialBandScalarCurrentZeroExtension_deck_generator
    period hPeriod field test input
  have hInvariant := hScalarInvariant input
  rw [hInvariant] at hAnti
  linarith

end
end P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D
end JanusFormal
