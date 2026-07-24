import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D

/-!
# Deck gluing law for the latitude Cauchy jet

The mapping-torus generator translates the throat time by one period and
reverses the latitude normal.  Boundary values are periodic, whereas oriented
normal data are antiperiodic.  The value profile is even and the normal profile
is odd, so the local Cauchy extension is invariant under the combined deck
transformation.

This is the exact algebraic gluing law needed to descend the collar extension.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

/-- The value profile is even. -/
theorem canonicalLatitudeCauchyValueProfile_neg (normal : Real) :
    canonicalLatitudeCauchyValueProfile (-normal) =
      canonicalLatitudeCauchyValueProfile normal := by
  unfold canonicalLatitudeCauchyValueProfile
  exact canonicalLatitudeCollarCutoff.neg normal

/-- The normal profile is odd. -/
theorem canonicalLatitudeCauchyNormalProfile_neg (normal : Real) :
    canonicalLatitudeCauchyNormalProfile (-normal) =
      -canonicalLatitudeCauchyNormalProfile normal := by
  unfold canonicalLatitudeCauchyNormalProfile
  rw [canonicalLatitudeCollarCutoff.neg]
  ring

/-- Generator action on the first-sheet latitude base.  The equatorial fiber is
fixed and time is translated by one period. -/
def canonicalLatitudeBaseDeck
    (period : Real) (base : CanonicalLatitudeBase) : CanonicalLatitudeBase :=
  (base.1, base.2 + period)

/-- Periodicity condition for boundary values. -/
def CanonicalLatitudeValueDeckPeriodic
    (period : Real) (value : CanonicalLatitudeBase → Real) : Prop :=
  ∀ base, value (canonicalLatitudeBaseDeck period base) = value base

/-- Antiperiodicity condition for oriented normal boundary data. -/
def CanonicalLatitudeNormalDeckAntiperiodic
    (period : Real) (normal : CanonicalLatitudeBase → Real) : Prop :=
  ∀ base, normal (canonicalLatitudeBaseDeck period base) = -normal base

/-- Combined generator action on collar parameters. -/
def canonicalLatitudeCollarDeck
    (period : Real) (parameter : CanonicalLatitudeBase × Real) :
    CanonicalLatitudeBase × Real :=
  (canonicalLatitudeBaseDeck period parameter.1, -parameter.2)

/-- The exact local Cauchy extension is invariant under the mapping-torus deck
generator when value data are periodic and normal data are antiperiodic. -/
theorem canonicalLatitudeLocalCauchyExtension_deck
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal)
    (parameter : CanonicalLatitudeBase × Real) :
    canonicalLatitudeLocalCauchyExtension (value, normal)
        (canonicalLatitudeCollarDeck period parameter) =
      canonicalLatitudeLocalCauchyExtension (value, normal) parameter := by
  unfold canonicalLatitudeCollarDeck canonicalLatitudeLocalCauchyExtension
  change canonicalLatitudeCauchyValueProfile (-parameter.2) *
        value (canonicalLatitudeBaseDeck period parameter.1) +
      canonicalLatitudeCauchyNormalProfile (-parameter.2) *
        normal (canonicalLatitudeBaseDeck period parameter.1) =
    canonicalLatitudeCauchyValueProfile parameter.2 * value parameter.1 +
      canonicalLatitudeCauchyNormalProfile parameter.2 * normal parameter.1
  rw [canonicalLatitudeCauchyValueProfile_neg,
    canonicalLatitudeCauchyNormalProfile_neg,
    hValue parameter.1, hNormal parameter.1]
  ring

/-- Function-level deck invariance of the local extension. -/
theorem canonicalLatitudeLocalCauchyExtension_comp_deck
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal) :
    canonicalLatitudeLocalCauchyExtension (value, normal) ∘
        canonicalLatitudeCollarDeck period =
      canonicalLatitudeLocalCauchyExtension (value, normal) := by
  funext parameter
  exact canonicalLatitudeLocalCauchyExtension_deck
    period value normal hValue hNormal parameter

/-- The local Cauchy jet simultaneously has the prescribed first jet and the
correct deck gluing law. -/
theorem canonicalLatitudeCauchyJetDeckGluing_certificate
    (period : Real)
    (value normal : CanonicalLatitudeBase → Real)
    (hValue : CanonicalLatitudeValueDeckPeriodic period value)
    (hNormal : CanonicalLatitudeNormalDeckAntiperiodic period normal) :
    (∀ base,
      canonicalLatitudeLocalCauchyExtensionSlice (value, normal) base 0 =
        value base) ∧
      (∀ base,
        deriv (canonicalLatitudeLocalCauchyExtensionSlice
          (value, normal) base) 0 = normal base) ∧
      canonicalLatitudeLocalCauchyExtension (value, normal) ∘
          canonicalLatitudeCollarDeck period =
        canonicalLatitudeLocalCauchyExtension (value, normal) :=
  ⟨canonicalLatitudeLocalCauchyExtensionSlice_zero (value, normal),
    deriv_canonicalLatitudeLocalCauchyExtensionSlice_zero (value, normal),
    canonicalLatitudeLocalCauchyExtension_comp_deck
      period value normal hValue hNormal⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
end JanusFormal
