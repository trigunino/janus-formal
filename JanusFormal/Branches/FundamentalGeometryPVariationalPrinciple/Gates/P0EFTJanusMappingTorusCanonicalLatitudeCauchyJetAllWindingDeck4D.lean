import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D

/-!
# All-winding deck invariance of the latitude Cauchy jet

Generator invariance is promoted to invariance under every integer iterate of the
collar deck equivalence.  This is the exact equivalence relation used by the
mapping-torus quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetAllWindingDeck4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D

/-- The collar deck generator as an explicit equivalence. -/
def canonicalLatitudeCollarDeckEquiv (period : Real) :
    (CanonicalLatitudeBase × Real) ≃ (CanonicalLatitudeBase × Real) where
  toFun := canonicalLatitudeCollarDeck period
  invFun := fun parameter =>
    ((parameter.1.1, parameter.1.2 - period), -parameter.2)
  left_inv parameter := by
    rcases parameter with ⟨⟨sphere, time⟩, normal⟩
    ext <;> simp [canonicalLatitudeCollarDeck,
      canonicalLatitudeBaseDeck]
  right_inv parameter := by
    rcases parameter with ⟨⟨sphere, time⟩, normal⟩
    ext <;> simp [canonicalLatitudeCollarDeck,
      canonicalLatitudeBaseDeck]

@[simp] theorem canonicalLatitudeCollarDeckEquiv_apply
    (period : Real) (parameter : CanonicalLatitudeBase × Real) :
    canonicalLatitudeCollarDeckEquiv period parameter =
      canonicalLatitudeCollarDeck period parameter :=
  rfl

/-- Invariance under the inverse generator follows from forward generator
invariance. -/
theorem canonicalLatitudeLocalCauchyExtension_deck_inv
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal)
    (parameter : CanonicalLatitudeBase × Real) :
    canonicalLatitudeLocalCauchyExtension (value, normal)
        ((canonicalLatitudeCollarDeckEquiv period).symm parameter) =
      canonicalLatitudeLocalCauchyExtension (value, normal) parameter := by
  have hForward := canonicalLatitudeLocalCauchyExtension_deck
    period value normal hValue hNormal
      ((canonicalLatitudeCollarDeckEquiv period).symm parameter)
  rw [← canonicalLatitudeCollarDeckEquiv_apply,
    (canonicalLatitudeCollarDeckEquiv period).apply_symm_apply] at hForward
  exact hForward.symm

/-- Invariance under every integer deck winding. -/
theorem canonicalLatitudeLocalCauchyExtension_deck_zpow
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal)
    (winding : Int) (parameter : CanonicalLatitudeBase × Real) :
    canonicalLatitudeLocalCauchyExtension (value, normal)
        ((canonicalLatitudeCollarDeckEquiv period ^ winding) parameter) =
      canonicalLatitudeLocalCauchyExtension (value, normal) parameter := by
  induction winding using Int.induction_on with
  | zero =>
      simp
  | succ winding ih =>
      rw [zpow_add_one]
      change canonicalLatitudeLocalCauchyExtension (value, normal)
          ((canonicalLatitudeCollarDeckEquiv period ^ winding)
            (canonicalLatitudeCollarDeckEquiv period parameter)) = _
      rw [ih (canonicalLatitudeCollarDeckEquiv period parameter)]
      exact canonicalLatitudeLocalCauchyExtension_deck
        period value normal hValue hNormal parameter
  | pred winding ih =>
      rw [zpow_sub_one]
      change canonicalLatitudeLocalCauchyExtension (value, normal)
          ((canonicalLatitudeCollarDeckEquiv period ^ (-(winding : Int)))
            ((canonicalLatitudeCollarDeckEquiv period).symm parameter)) = _
      rw [ih ((canonicalLatitudeCollarDeckEquiv period).symm parameter)]
      exact canonicalLatitudeLocalCauchyExtension_deck_inv
        period value normal hValue hNormal parameter

/-- Function-level all-winding invariance. -/
theorem canonicalLatitudeLocalCauchyExtension_comp_deck_zpow
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal)
    (winding : Int) :
    canonicalLatitudeLocalCauchyExtension (value, normal) ∘
        (canonicalLatitudeCollarDeckEquiv period ^ winding) =
      canonicalLatitudeLocalCauchyExtension (value, normal) := by
  funext parameter
  exact canonicalLatitudeLocalCauchyExtension_deck_zpow
    period value normal hValue hNormal winding parameter

/-- All-winding deck certificate. -/
theorem canonicalLatitudeCauchyJetAllWindingDeck_certificate
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal) :
    ∀ winding : Int,
      canonicalLatitudeLocalCauchyExtension (value, normal) ∘
          (canonicalLatitudeCollarDeckEquiv period ^ winding) =
        canonicalLatitudeLocalCauchyExtension (value, normal) :=
  canonicalLatitudeLocalCauchyExtension_comp_deck_zpow
    period value normal hValue hNormal

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetAllWindingDeck4D
end JanusFormal
