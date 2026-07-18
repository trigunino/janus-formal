import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D

/-!
# Orbit quotient of the concrete D8 independent-field time action

The complete pullback action on the actual `IndependentFields` package defines
an honest setoid.  Functions on its quotient are exactly functions invariant
under every real time translation.  No topology on the quotient is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentFieldOrbitQuotient4D

set_option autoImplicit false

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Orbit relation of the concrete complete pullback action. -/
def IndependentTimeOrbitRel
    (first second : IndependentFields period hPeriod) : Prop :=
  ∃ shift : Real,
    second = independentTimeAction period hPeriod shift first

theorem independentTimeOrbitRel_refl
    (fields : IndependentFields period hPeriod) :
    IndependentTimeOrbitRel period hPeriod fields fields := by
  exact ⟨0, (independentTimeAction_zero period hPeriod fields).symm⟩

theorem independentTimeOrbitRel_symm
    {first second : IndependentFields period hPeriod}
    (h : IndependentTimeOrbitRel period hPeriod first second) :
    IndependentTimeOrbitRel period hPeriod second first := by
  rcases h with ⟨shift, rfl⟩
  exact ⟨-shift, (independentTimeAction_neg period hPeriod shift first).symm⟩

theorem independentTimeOrbitRel_trans
    {first second third : IndependentFields period hPeriod}
    (hFirst : IndependentTimeOrbitRel period hPeriod first second)
    (hSecond : IndependentTimeOrbitRel period hPeriod second third) :
    IndependentTimeOrbitRel period hPeriod first third := by
  rcases hFirst with ⟨firstShift, rfl⟩
  rcases hSecond with ⟨secondShift, rfl⟩
  exact ⟨firstShift + secondShift,
    (independentTimeAction_add period hPeriod
      firstShift secondShift first).symm⟩

/-- Setoid of concrete independent-field time orbits. -/
def independentTimeOrbitSetoid :
    Setoid (IndependentFields period hPeriod) where
  r := IndependentTimeOrbitRel period hPeriod
  iseqv :=
    ⟨independentTimeOrbitRel_refl period hPeriod,
      independentTimeOrbitRel_symm period hPeriod,
      independentTimeOrbitRel_trans period hPeriod⟩

/-- Actual independent-field configurations modulo D8 time translation. -/
def IndependentFieldTimeOrbit :=
  Quotient (independentTimeOrbitSetoid period hPeriod)

/-- Canonical field-orbit projection. -/
def independentFieldOrbitClass
    (fields : IndependentFields period hPeriod) :
    IndependentFieldTimeOrbit period hPeriod :=
  Quotient.mk (independentTimeOrbitSetoid period hPeriod) fields

theorem independentFieldOrbitClass_timeAction
    (shift : Real) (fields : IndependentFields period hPeriod) :
    independentFieldOrbitClass period hPeriod
        (independentTimeAction period hPeriod shift fields) =
      independentFieldOrbitClass period hPeriod fields := by
  exact (Quotient.sound
    (show IndependentTimeOrbitRel period hPeriod fields
      (independentTimeAction period hPeriod shift fields) from
        ⟨shift, rfl⟩)).symm

/-- Functions on the concrete field package invariant under all time shifts. -/
def IndependentTimeInvariantFunction (Target : Type*) :=
  { function : IndependentFields period hPeriod → Target //
    ∀ fields shift,
      function (independentTimeAction period hPeriod shift fields) =
        function fields }

/-- Pull a function on field orbits back to the full field package. -/
def pullbackIndependentFieldOrbitFunction
    {Target : Type*}
    (function : IndependentFieldTimeOrbit period hPeriod → Target) :
    IndependentFields period hPeriod → Target :=
  fun fields ↦ function (independentFieldOrbitClass period hPeriod fields)

theorem pullbackIndependentFieldOrbitFunction_invariant
    {Target : Type*}
    (function : IndependentFieldTimeOrbit period hPeriod → Target) :
    ∀ fields shift,
      pullbackIndependentFieldOrbitFunction period hPeriod function
          (independentTimeAction period hPeriod shift fields) =
        pullbackIndependentFieldOrbitFunction period hPeriod function fields := by
  intro fields shift
  exact congrArg function
    (independentFieldOrbitClass_timeAction period hPeriod shift fields)

/-- Descend a concrete time-invariant field function to the orbit quotient. -/
def descendIndependentTimeInvariantFunction
    {Target : Type*}
    (function : IndependentTimeInvariantFunction period hPeriod Target) :
    IndependentFieldTimeOrbit period hPeriod → Target :=
  Quotient.lift function.1 (by
    intro first second h
    rcases h with ⟨shift, rfl⟩
    exact (function.2 first shift).symm)

@[simp]
theorem descendIndependentTimeInvariantFunction_orbitClass
    {Target : Type*}
    (function : IndependentTimeInvariantFunction period hPeriod Target)
    (fields : IndependentFields period hPeriod) :
    descendIndependentTimeInvariantFunction period hPeriod function
        (independentFieldOrbitClass period hPeriod fields) =
      function.1 fields :=
  rfl

/-- Concrete orbit functions are exactly invariant functions on the current
full independent-field package. -/
def independentFieldOrbitFunctionsEquivInvariant
    (Target : Type*) :
    (IndependentFieldTimeOrbit period hPeriod → Target) ≃
      IndependentTimeInvariantFunction period hPeriod Target where
  toFun function :=
    ⟨pullbackIndependentFieldOrbitFunction period hPeriod function,
      pullbackIndependentFieldOrbitFunction_invariant period hPeriod function⟩
  invFun := descendIndependentTimeInvariantFunction period hPeriod
  left_inv function := by
    funext orbit
    induction orbit using Quotient.inductionOn with
    | _ fields => rfl
  right_inv function := by
    apply Subtype.ext
    funext fields
    rfl

theorem independent_field_orbit_quotient4D_closed
    (shift : Real) (fields : IndependentFields period hPeriod) :
    independentFieldOrbitClass period hPeriod
        (independentTimeAction period hPeriod shift fields) =
      independentFieldOrbitClass period hPeriod fields :=
  independentFieldOrbitClass_timeAction period hPeriod shift fields

end P0EFTJanusMappingTorusIndependentFieldOrbitQuotient4D
end JanusFormal
