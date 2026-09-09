import Mathlib

/-!
# Relative jet variational bicomplex core in dimension four

This module provides only the algebraic carrier needed by later Program-P
gates.  A cochain has a horizontal degree, a contact degree and one component
on each physical stratum.  The relative horizontal differential may keep a
component on its stratum or send it to an incident boundary stratum; the
contact differential preserves the stratum.

No concrete differential is manufactured here.  In particular, this file
does not instantiate the core with zero maps and does not assert that any
physical variational obstruction vanishes.  A later realization must supply
the actual jet cochains and prove all differential and incidence laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D

set_option autoImplicit false

universe u v

/-- Strata that occur in the relative four-dimensional variational problem. -/
inductive RelativeJetStratum4D where
  | bulk
  | nonNullBoundary
  | nullBoundary
  | joint
  deriving DecidableEq, Fintype, Repr

namespace RelativeJetStratum4D

/-- Intrinsic horizontal dimension of each stratum. -/
@[simp] def horizontalDimension : RelativeJetStratum4D → Nat
  | bulk => 4
  | nonNullBoundary => 3
  | nullBoundary => 3
  | joint => 2

/-- Codimension inside the four-dimensional bulk. -/
@[simp] def codimension : RelativeJetStratum4D → Nat
  | bulk => 0
  | nonNullBoundary => 1
  | nullBoundary => 1
  | joint => 2

theorem horizontalDimension_add_codimension
    (stratum : RelativeJetStratum4D) :
    stratum.horizontalDimension + stratum.codimension = 4 := by
  cases stratum <;> rfl

/-- Oriented incidence graph underlying the relative horizontal complex. -/
inductive IsImmediateBoundary :
    RelativeJetStratum4D → RelativeJetStratum4D → Prop where
  | bulk_nonNull : IsImmediateBoundary bulk nonNullBoundary
  | bulk_null : IsImmediateBoundary bulk nullBoundary
  | nonNull_joint : IsImmediateBoundary nonNullBoundary joint
  | null_joint : IsImmediateBoundary nullBoundary joint

theorem horizontalDimension_eq_succ_of_isImmediateBoundary
    {source target : RelativeJetStratum4D}
    (hBoundary : IsImmediateBoundary source target) :
    source.horizontalDimension = target.horizontalDimension + 1 := by
  cases hBoundary <;> rfl

theorem codimension_succ_of_isImmediateBoundary
    {source target : RelativeJetStratum4D}
    (hBoundary : IsImmediateBoundary source target) :
    target.codimension = source.codimension + 1 := by
  cases hBoundary <;> rfl

/-- A relative horizontal step may stay on one stratum or follow one boundary
incidence arrow. -/
def HorizontalIncidenceAllowed
    (source target : RelativeJetStratum4D) : Prop :=
  source = target ∨ IsImmediateBoundary source target

end RelativeJetStratum4D

/-- A bigraded relative jet cochain is a compatible slot for every stratum.
Concrete realizations choose the component types `C stratum p q`. -/
abbrev RelativeJetCochain
    (C : RelativeJetStratum4D → Nat → Nat → Type v)
    (horizontalDegree contactDegree : Nat) : Type v :=
  ∀ stratum, C stratum horizontalDegree contactDegree

/-- Support on exactly one stratum. -/
def RelativeJetCochain.SupportedOn
    {C : RelativeJetStratum4D → Nat → Nat → Type v}
    [∀ stratum p q, Zero (C stratum p q)]
    {p q : Nat}
    (cochain : RelativeJetCochain C p q)
    (source : RelativeJetStratum4D) : Prop :=
  ∀ target, target ≠ source → cochain target = 0

/-- Support in a specified collection of strata. -/
def RelativeJetCochain.SupportedWithin
    {C : RelativeJetStratum4D → Nat → Nat → Type v}
    [∀ stratum p q, Zero (C stratum p q)]
    {p q : Nat}
    (cochain : RelativeJetCochain C p q)
    (allowed : RelativeJetStratum4D → Prop) : Prop :=
  ∀ target, ¬ allowed target → cochain target = 0

/-- Evaluation of a relative cochain on one stratum is linear. -/
def relativeJetCochainComponent
    (R : Type u) [Semiring R]
    (C : RelativeJetStratum4D → Nat → Nat → Type v)
    [∀ stratum p q, AddCommMonoid (C stratum p q)]
    [∀ stratum p q, Module R (C stratum p q)]
    (p q : Nat) (stratum : RelativeJetStratum4D) :
    RelativeJetCochain C p q →ₗ[R] C stratum p q where
  toFun cochain := cochain stratum
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Algebraic core of a relative jet variational bicomplex.

`dH` raises horizontal degree and is allowed to contain restriction/incidence
terms towards immediate boundary strata.  `dV` raises contact degree and stays
on the same stratum.  The three identities are the bicomplex relations needed
to form the unsigned total differential.
-/
structure RelativeJetVariationalBicomplexCore
    (R : Type u) [CommRing R]
    (C : RelativeJetStratum4D → Nat → Nat → Type v)
    [∀ stratum p q, AddCommGroup (C stratum p q)]
    [∀ stratum p q, Module R (C stratum p q)] where
  dH : ∀ p q,
    RelativeJetCochain C p q →ₗ[R] RelativeJetCochain C (p + 1) q
  dV : ∀ p q,
    RelativeJetCochain C p q →ₗ[R] RelativeJetCochain C p (q + 1)
  dH_dH : ∀ p q (cochain : RelativeJetCochain C p q),
    dH (p + 1) q (dH p q cochain) = 0
  dV_dV : ∀ p q (cochain : RelativeJetCochain C p q),
    dV p (q + 1) (dV p q cochain) = 0
  mixed_anticommutes : ∀ p q (cochain : RelativeJetCochain C p q),
    dV (p + 1) q (dH p q cochain) +
        dH p (q + 1) (dV p q cochain) = 0
  dH_respects_incidence :
    ∀ p q source (cochain : RelativeJetCochain C p q),
      cochain.SupportedOn source →
      ∀ target,
        ¬ RelativeJetStratum4D.HorizontalIncidenceAllowed source target →
        dH p q cochain target = 0
  dV_preserves_stratum :
    ∀ p q source (cochain : RelativeJetCochain C p q),
      cochain.SupportedOn source →
      ∀ target, target ≠ source → dV p q cochain target = 0

namespace RelativeJetVariationalBicomplexCore

variable
    {R : Type u} [CommRing R]
    {C : RelativeJetStratum4D → Nat → Nat → Type v}
    [∀ stratum p q, AddCommGroup (C stratum p q)]
    [∀ stratum p q, Module R (C stratum p q)]

/-- The two homogeneous summands reached by one total-differential step. -/
abbrev TotalFirstTarget (p q : Nat) :=
  RelativeJetCochain C (p + 1) q ×
    RelativeJetCochain C p (q + 1)

/-- The three homogeneous summands reached after two total steps. -/
abbrev TotalSecondTarget (p q : Nat) :=
  (RelativeJetCochain C ((p + 1) + 1) q ×
      RelativeJetCochain C (p + 1) (q + 1)) ×
    RelativeJetCochain C p ((q + 1) + 1)

/-- On a homogeneous cochain, the total differential is `dH + dV`, recorded
in the two successor bidegrees. -/
def totalDifferential
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) :
    RelativeJetCochain C p q →ₗ[R] TotalFirstTarget (C := C) p q where
  toFun cochain :=
    (bicomplex.dH p q cochain, bicomplex.dV p q cochain)
  map_add' first second := by
    simp
  map_smul' scalar cochain := by
    simp

/-- The next total step combines the two mixed paths in their common
bidegree. -/
def totalDifferentialNext
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) :
    TotalFirstTarget (C := C) p q →ₗ[R]
      TotalSecondTarget (C := C) p q where
  toFun cochain :=
    ((bicomplex.dH (p + 1) q cochain.1,
        bicomplex.dV (p + 1) q cochain.1 +
          bicomplex.dH p (q + 1) cochain.2),
      bicomplex.dV p (q + 1) cochain.2)
  map_add' first second := by
    apply Prod.ext
    · apply Prod.ext
      · exact (bicomplex.dH (p + 1) q).map_add first.1 second.1
      · change
          bicomplex.dV (p + 1) q (first.1 + second.1) +
              bicomplex.dH p (q + 1) (first.2 + second.2) =
            (bicomplex.dV (p + 1) q first.1 +
                bicomplex.dH p (q + 1) first.2) +
              (bicomplex.dV (p + 1) q second.1 +
                bicomplex.dH p (q + 1) second.2)
        rw [map_add, map_add]
        abel
    · exact (bicomplex.dV p (q + 1)).map_add first.2 second.2
  map_smul' scalar cochain := by
    apply Prod.ext
    · apply Prod.ext
      · exact (bicomplex.dH (p + 1) q).map_smul scalar cochain.1
      · change
          bicomplex.dV (p + 1) q (scalar • cochain.1) +
              bicomplex.dH p (q + 1) (scalar • cochain.2) =
            scalar •
              (bicomplex.dV (p + 1) q cochain.1 +
                bicomplex.dH p (q + 1) cochain.2)
        rw [map_smul, map_smul, smul_add]
    · exact (bicomplex.dV p (q + 1)).map_smul scalar cochain.2

@[simp] theorem totalDifferential_horizontal
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) (cochain : RelativeJetCochain C p q) :
    (bicomplex.totalDifferential p q cochain).1 =
      bicomplex.dH p q cochain :=
  rfl

@[simp] theorem totalDifferential_vertical
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) (cochain : RelativeJetCochain C p q) :
    (bicomplex.totalDifferential p q cochain).2 =
      bicomplex.dV p q cochain :=
  rfl

/-- The total differential squares to zero on every homogeneous relative jet
cochain. -/
theorem totalDifferential_squared
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) (cochain : RelativeJetCochain C p q) :
    bicomplex.totalDifferentialNext p q
        (bicomplex.totalDifferential p q cochain) = 0 := by
  apply Prod.ext
  · apply Prod.ext
    · simpa [totalDifferentialNext, totalDifferential] using
        bicomplex.dH_dH p q cochain
    · simpa [totalDifferentialNext, totalDifferential] using
        bicomplex.mixed_anticommutes p q cochain
  · simpa [totalDifferentialNext, totalDifferential] using
      bicomplex.dV_dV p q cochain

/-- Vertical differentiation of a single-stratum cochain remains supported
on that stratum. -/
theorem dV_supportedOn
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) (source : RelativeJetStratum4D)
    (cochain : RelativeJetCochain C p q)
    (hSupport : cochain.SupportedOn source) :
    (bicomplex.dV p q cochain).SupportedOn source := by
  intro target hTarget
  exact bicomplex.dV_preserves_stratum p q source cochain hSupport target hTarget

/-- Horizontal differentiation can only retain a component or move it along
one immediate boundary-incidence arrow. -/
theorem dH_supportedWithin_incidence
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) (source : RelativeJetStratum4D)
    (cochain : RelativeJetCochain C p q)
    (hSupport : cochain.SupportedOn source) :
    (bicomplex.dH p q cochain).SupportedWithin
      (RelativeJetStratum4D.HorizontalIncidenceAllowed source) := by
  intro target hTarget
  exact bicomplex.dH_respects_incidence p q source cochain hSupport target hTarget

end RelativeJetVariationalBicomplexCore
end P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
end JanusFormal
