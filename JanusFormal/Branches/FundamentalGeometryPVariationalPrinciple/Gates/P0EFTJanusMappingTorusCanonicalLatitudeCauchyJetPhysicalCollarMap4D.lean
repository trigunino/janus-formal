import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# The Cauchy collar quotient maps to the physical mapping torus

The model collar deck generator translates the equatorial time by one period and
reverses the normal.  The explicit latitude collar in the mapping-torus cover
satisfies precisely the same twist.  Therefore the canonical collar map is
constant on every model deck orbit and descends to the actual bulk quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetPhysicalCollarMap4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetAllWindingDeck4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

/-- Translating a latitude base by one period translates its selected throat
cover anchor by the fixed-throat deck generator. -/
theorem canonicalLatitudeAnchor_deck
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeAnchor period hPeriod
        (canonicalLatitudeBaseDeck period base) =
      (1 : Int) +ᵥ canonicalLatitudeAnchor period hPeriod base := by
  apply MappingTorusCover.ext
  · simp [canonicalLatitudeAnchor, canonicalLatitudeBaseDeck,
      mappingTorusVAdd, fixedEquatorData]
  · simp [canonicalLatitudeAnchor, canonicalLatitudeBaseDeck,
      mappingTorusVAdd, fixedEquatorData]

/-- The physical latitude collar map is invariant under the model deck
generator. -/
theorem canonicalLatitudeCollarMap_deck
    (parameter : CanonicalLatitudeCauchyCollar period) :
    canonicalLatitudeCollarMap period hPeriod
        (canonicalLatitudeCollarDeck period parameter) =
      canonicalLatitudeCollarMap period hPeriod parameter := by
  rcases parameter with ⟨base, normal⟩
  unfold canonicalLatitudeCollarDeck
  unfold canonicalLatitudeCollarMap quotientNormalLatitude
  simp only [Prod.fst, Prod.snd]
  rw [canonicalLatitudeAnchor_deck]
  rw [normalLatitudeCover_deck_generator_twist]
  simp only [neg_neg]
  apply (mappingTorusMk_eq_iff_exists_vadd
    (sphereData period hPeriod) _ _).2
  exact ⟨(1 : Int), rfl⟩

/-- Invariance under the inverse model deck generator. -/
theorem canonicalLatitudeCollarMap_deck_inv
    (parameter : CanonicalLatitudeCauchyCollar period) :
    canonicalLatitudeCollarMap period hPeriod
        ((canonicalLatitudeCollarDeckEquiv period).symm parameter) =
      canonicalLatitudeCollarMap period hPeriod parameter := by
  have hForward := canonicalLatitudeCollarMap_deck period hPeriod
    ((canonicalLatitudeCollarDeckEquiv period).symm parameter)
  rw [← canonicalLatitudeCollarDeckEquiv_apply,
    (canonicalLatitudeCollarDeckEquiv period).apply_symm_apply] at hForward
  exact hForward.symm

/-- The physical collar map is invariant under every integer model winding. -/
theorem canonicalLatitudeCollarMap_deck_zpow
    (winding : Int) (parameter : CanonicalLatitudeCauchyCollar period) :
    canonicalLatitudeCollarMap period hPeriod
        ((canonicalLatitudeCollarDeckEquiv period ^ winding) parameter) =
      canonicalLatitudeCollarMap period hPeriod parameter := by
  induction winding using Int.induction_on generalizing parameter with
  | zero =>
      simp
  | succ winding ih =>
      rw [zpow_add_one]
      change canonicalLatitudeCollarMap period hPeriod
          ((canonicalLatitudeCollarDeckEquiv period ^ (winding : Int))
            (canonicalLatitudeCollarDeckEquiv period parameter)) = _
      rw [ih (canonicalLatitudeCollarDeckEquiv period parameter)]
      exact canonicalLatitudeCollarMap_deck period hPeriod parameter
  | pred winding ih =>
      rw [zpow_sub_one]
      change canonicalLatitudeCollarMap period hPeriod
          ((canonicalLatitudeCollarDeckEquiv period ^ (-(winding : Int)))
            ((canonicalLatitudeCollarDeckEquiv period).symm parameter)) = _
      rw [ih ((canonicalLatitudeCollarDeckEquiv period).symm parameter)]
      exact canonicalLatitudeCollarMap_deck_inv period hPeriod parameter

/-- Canonical map from the model collar quotient into the actual physical bulk. -/
def canonicalLatitudeCauchyCollarToBulk :
    CanonicalLatitudeCauchyCollarQuotient period →
      EffectiveQuotient period hPeriod :=
  Quotient.lift (canonicalLatitudeCollarMap period hPeriod)
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (CanonicalLatitudeCauchyCollar period)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact canonicalLatitudeCollarMap_deck_zpow
        period hPeriod winding second)

@[simp] theorem canonicalLatitudeCauchyCollarToBulk_mk
    (parameter : CanonicalLatitudeCauchyCollar period) :
    canonicalLatitudeCauchyCollarToBulk period hPeriod
        (canonicalLatitudeCauchyCollarMk period parameter) =
      canonicalLatitudeCollarMap period hPeriod parameter :=
  rfl

/-- The zero-normal section of the physical collar quotient is the canonical
throat inclusion. -/
theorem canonicalLatitudeCauchyCollarToBulk_zero
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeCauchyCollarToBulk period hPeriod
        (canonicalLatitudeCauchyCollarMk period (base, 0)) =
      fixedThroatQuotientInclusion period hPeriod
        (canonicalLatitudeThroatMap period hPeriod base) := by
  rw [canonicalLatitudeCauchyCollarToBulk_mk]
  unfold canonicalLatitudeCollarMap
  rw [quotientNormalLatitude_zero]
  rfl

/-- Physical-collar descent certificate. -/
theorem canonicalLatitudeCauchyJetPhysicalCollarMap_certificate :
    (∀ (winding : Int) (parameter : CanonicalLatitudeCauchyCollar period),
      canonicalLatitudeCollarMap period hPeriod
          ((canonicalLatitudeCollarDeckEquiv period ^ winding) parameter) =
        canonicalLatitudeCollarMap period hPeriod parameter) ∧
      (∀ parameter,
        canonicalLatitudeCauchyCollarToBulk period hPeriod
            (canonicalLatitudeCauchyCollarMk period parameter) =
          canonicalLatitudeCollarMap period hPeriod parameter) :=
  ⟨canonicalLatitudeCollarMap_deck_zpow period hPeriod,
    canonicalLatitudeCauchyCollarToBulk_mk period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetPhysicalCollarMap4D
end JanusFormal
