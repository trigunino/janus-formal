import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetPhysicalCollarMap4D

/-!
# Injective physical embedding of the latitude tubular collar quotient

Restrict the latitude normal to `(-π/2,π/2)`.  The explicit spherical tubular
map is injective on this band.  Adding the fundamental-domain time coordinate
therefore gives an injective map into the mapping-torus cover.  Its exact deck
equivariance descends to an injective map from the model collar orbit quotient
into the physical mapping torus.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetPhysicalCollarMap4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

/-- Open normal band of the genuine equatorial tubular chart. -/
abbrev CanonicalLatitudeTubularNormal :=
  Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- Model tubular collar with unrestricted cover time. -/
abbrev CanonicalLatitudeTubularCollar :=
  CanonicalLatitudeBase × CanonicalLatitudeTubularNormal

/-- Negation preserves the open latitude band. -/
def canonicalLatitudeTubularNormalNeg
    (normal : CanonicalLatitudeTubularNormal) :
    CanonicalLatitudeTubularNormal :=
  ⟨-normal.1, by
    constructor <;> nlinarith [normal.2.1, normal.2.2]⟩

/-- Deck generator on the tubular collar. -/
def canonicalLatitudeTubularDeckEquiv (period : Real) :
    CanonicalLatitudeTubularCollar ≃ CanonicalLatitudeTubularCollar where
  toFun parameter :=
    (canonicalLatitudeBaseDeck period parameter.1,
      canonicalLatitudeTubularNormalNeg parameter.2)
  invFun parameter :=
    ((parameter.1.1, parameter.1.2 - period),
      canonicalLatitudeTubularNormalNeg parameter.2)
  left_inv parameter := by
    rcases parameter with ⟨⟨sphere, time⟩, normal⟩
    ext <;> simp [canonicalLatitudeBaseDeck,
      canonicalLatitudeTubularNormalNeg]
  right_inv parameter := by
    rcases parameter with ⟨⟨sphere, time⟩, normal⟩
    ext <;> simp [canonicalLatitudeBaseDeck,
      canonicalLatitudeTubularNormalNeg]

instance (period : Real) : VAdd Int CanonicalLatitudeTubularCollar where
  vadd winding parameter :=
    (canonicalLatitudeTubularDeckEquiv period ^ winding) parameter

instance (period : Real) : AddAction Int CanonicalLatitudeTubularCollar where
  zero_vadd parameter := by
    change (canonicalLatitudeTubularDeckEquiv period ^ (0 : Int)) parameter =
      parameter
    simp
  add_vadd first second parameter := by
    change (canonicalLatitudeTubularDeckEquiv period ^ (first + second)) parameter =
      (canonicalLatitudeTubularDeckEquiv period ^ first)
        ((canonicalLatitudeTubularDeckEquiv period ^ second) parameter)
    rw [zpow_add]
    rfl

/-- Explicit tubular map into the physical cover. -/
def canonicalLatitudeTubularCoverMap
    (parameter : CanonicalLatitudeTubularCollar) :
    EffectiveCover period hPeriod :=
  normalLatitudeCover period hPeriod
    (canonicalLatitudeAnchor period hPeriod parameter.1) parameter.2.1

/-- The tubular cover map is injective. -/
theorem canonicalLatitudeTubularCoverMap_injective :
    Function.Injective
      (canonicalLatitudeTubularCoverMap period hPeriod) := by
  rintro ⟨⟨firstSphere, firstTime⟩, firstNormal⟩
    ⟨⟨secondSphere, secondTime⟩, secondNormal⟩ hEqual
  have hFiber := congrArg MappingTorusCover.fiber hEqual
  have hTime := congrArg MappingTorusCover.time hEqual
  change equatorialLatitude
      (equatorialTwoSphereHomeomorph.symm firstSphere) firstNormal.1 =
    equatorialLatitude
      (equatorialTwoSphereHomeomorph.symm secondSphere) secondNormal.1
    at hFiber
  change firstTime = secondTime at hTime
  have hTubular :
      (equatorialTwoSphereHomeomorph.symm firstSphere, firstNormal) =
        (equatorialTwoSphereHomeomorph.symm secondSphere, secondNormal) :=
    equatorialTubularMap_injective hFiber
  have hSphere : firstSphere = secondSphere := by
    apply equatorialTwoSphereHomeomorph.symm.injective
    exact congrArg Prod.fst hTubular
  have hNormal : firstNormal = secondNormal :=
    congrArg Prod.snd hTubular
  subst secondSphere
  subst secondTime
  subst secondNormal
  rfl

/-- Generator equivariance of the tubular cover map. -/
theorem canonicalLatitudeTubularCoverMap_deck
    (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularCoverMap period hPeriod
        (canonicalLatitudeTubularDeckEquiv period parameter) =
      (1 : Int) +ᵥ canonicalLatitudeTubularCoverMap period hPeriod parameter := by
  rcases parameter with ⟨base, normal⟩
  unfold canonicalLatitudeTubularCoverMap canonicalLatitudeTubularDeckEquiv
  simp only [Equiv.coe_fn_mk]
  rw [canonicalLatitudeAnchor_deck]
  simpa [canonicalLatitudeTubularNormalNeg] using
    normalLatitudeCover_deck_generator_twist
      period hPeriod (canonicalLatitudeAnchor period hPeriod base) (-normal.1)

/-- Inverse-generator equivariance. -/
theorem canonicalLatitudeTubularCoverMap_deck_inv
    (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularCoverMap period hPeriod
        ((canonicalLatitudeTubularDeckEquiv period).symm parameter) =
      (-1 : Int) +ᵥ canonicalLatitudeTubularCoverMap period hPeriod parameter := by
  have hForward := canonicalLatitudeTubularCoverMap_deck period hPeriod
    ((canonicalLatitudeTubularDeckEquiv period).symm parameter)
  rw [(canonicalLatitudeTubularDeckEquiv period).apply_symm_apply] at hForward
  have hAct := congrArg (fun point : EffectiveCover period hPeriod =>
    (-1 : Int) +ᵥ point) hForward
  simpa [add_vadd] using hAct.symm

/-- Equivariance under every integer winding. -/
theorem canonicalLatitudeTubularCoverMap_vadd
    (winding : Int) (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularCoverMap period hPeriod (winding +ᵥ parameter) =
      winding +ᵥ canonicalLatitudeTubularCoverMap period hPeriod parameter := by
  change canonicalLatitudeTubularCoverMap period hPeriod
      ((canonicalLatitudeTubularDeckEquiv period ^ winding) parameter) = _
  induction winding using Int.induction_on with
  | zero =>
      simp
  | succ winding ih =>
      rw [zpow_add_one]
      change canonicalLatitudeTubularCoverMap period hPeriod
          ((canonicalLatitudeTubularDeckEquiv period ^ winding)
            (canonicalLatitudeTubularDeckEquiv period parameter)) = _
      rw [ih (canonicalLatitudeTubularDeckEquiv period parameter),
        canonicalLatitudeTubularCoverMap_deck]
      simp [add_vadd]
  | pred winding ih =>
      rw [zpow_sub_one]
      change canonicalLatitudeTubularCoverMap period hPeriod
          ((canonicalLatitudeTubularDeckEquiv period ^ (-(winding : Int)))
            ((canonicalLatitudeTubularDeckEquiv period).symm parameter)) = _
      rw [ih ((canonicalLatitudeTubularDeckEquiv period).symm parameter),
        canonicalLatitudeTubularCoverMap_deck_inv]
      simp [add_vadd]

/-- Orbit quotient of the genuine tubular band. -/
abbrev CanonicalLatitudeTubularCollarQuotient (period : Real) :=
  AddAction.orbitRel.Quotient Int CanonicalLatitudeTubularCollar

/-- Tubular quotient projection. -/
def canonicalLatitudeTubularCollarMk (period : Real) :
    CanonicalLatitudeTubularCollar →
      CanonicalLatitudeTubularCollarQuotient period :=
  Quotient.mk (AddAction.orbitRel Int CanonicalLatitudeTubularCollar)

/-- Equality in the tubular quotient is equality up to a unique-unneeded deck
iterate. -/
theorem canonicalLatitudeTubularCollarMk_eq_iff_exists_vadd
    (first second : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularCollarMk period first =
        canonicalLatitudeTubularCollarMk period second ↔
      ∃ winding : Int, winding +ᵥ second = first := by
  rw [Quotient.eq'', AddAction.orbitRel_apply,
    AddAction.mem_orbit_iff]

/-- Physical bulk point represented by one tubular parameter. -/
def canonicalLatitudeTubularPhysicalMap
    (parameter : CanonicalLatitudeTubularCollar) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    (canonicalLatitudeTubularCoverMap period hPeriod parameter)

/-- The physical tubular map is constant on model deck orbits. -/
theorem canonicalLatitudeTubularPhysicalMap_vadd
    (winding : Int) (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularPhysicalMap period hPeriod
        (winding +ᵥ parameter) =
      canonicalLatitudeTubularPhysicalMap period hPeriod parameter := by
  unfold canonicalLatitudeTubularPhysicalMap
  rw [canonicalLatitudeTubularCoverMap_vadd]
  apply (mappingTorusMk_eq_iff_exists_vadd
    (sphereData period hPeriod) _ _).2
  exact ⟨winding, rfl⟩

/-- Descended tubular map into the physical bulk. -/
def canonicalLatitudeTubularCollarToBulk :
    CanonicalLatitudeTubularCollarQuotient period →
      EffectiveQuotient period hPeriod :=
  Quotient.lift (canonicalLatitudeTubularPhysicalMap period hPeriod)
    (fun first second hOrbit => by
      change AddAction.orbitRel Int CanonicalLatitudeTubularCollar
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact canonicalLatitudeTubularPhysicalMap_vadd
        period hPeriod winding second)

@[simp] theorem canonicalLatitudeTubularCollarToBulk_mk
    (parameter : CanonicalLatitudeTubularCollar) :
    canonicalLatitudeTubularCollarToBulk period hPeriod
        (canonicalLatitudeTubularCollarMk period parameter) =
      canonicalLatitudeTubularPhysicalMap period hPeriod parameter :=
  rfl

/-- The descended tubular map is injective. -/
theorem canonicalLatitudeTubularCollarToBulk_injective :
    Function.Injective
      (canonicalLatitudeTubularCollarToBulk period hPeriod) := by
  intro first second hEqual
  refine Quotient.inductionOn first ?_ hEqual
  intro firstParameter
  refine Quotient.inductionOn second ?_
  intro secondParameter hParameters
  change canonicalLatitudeTubularPhysicalMap period hPeriod firstParameter =
    canonicalLatitudeTubularPhysicalMap period hPeriod secondParameter
    at hParameters
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd
      (sphereData period hPeriod)
      (canonicalLatitudeTubularCoverMap period hPeriod firstParameter)
      (canonicalLatitudeTubularCoverMap period hPeriod secondParameter)).1
      hParameters
  have hCover :
      canonicalLatitudeTubularCoverMap period hPeriod
          (winding +ᵥ secondParameter) =
        canonicalLatitudeTubularCoverMap period hPeriod firstParameter := by
    rw [canonicalLatitudeTubularCoverMap_vadd]
    exact hWinding
  have hParameter : winding +ᵥ secondParameter = firstParameter :=
    canonicalLatitudeTubularCoverMap_injective period hPeriod hCover
  exact (canonicalLatitudeTubularCollarMk_eq_iff_exists_vadd
    period firstParameter secondParameter).2 ⟨winding, hParameter⟩

/-- Tubular embedding certificate. -/
theorem canonicalLatitudeTubularCollarEmbedding_certificate :
    Function.Injective
        (canonicalLatitudeTubularCoverMap period hPeriod) ∧
      Function.Injective
        (canonicalLatitudeTubularCollarToBulk period hPeriod) :=
  ⟨canonicalLatitudeTubularCoverMap_injective period hPeriod,
    canonicalLatitudeTubularCollarToBulk_injective period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
end JanusFormal
