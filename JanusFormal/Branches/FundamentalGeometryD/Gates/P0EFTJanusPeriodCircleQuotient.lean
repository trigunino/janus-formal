import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTwistedMappingGenerator

namespace JanusFormal
namespace P0EFTJanusPeriodCircleQuotient

set_option autoImplicit false

open P0EFTJanusTwistedMappingGenerator

/-- Two logarithmic coordinates are equivalent when they differ by an integer period. -/
def PeriodEquivalent (period u v : ℝ) : Prop :=
  ∃ n : ℤ, v = u + (n : ℝ) * period

/-- Period equivalence is reflexive. -/
theorem period_equivalent_refl (period u : ℝ) :
    PeriodEquivalent period u u := by
  refine ⟨0, ?_⟩
  norm_num

/-- Period equivalence is symmetric. -/
theorem period_equivalent_symm
    (period u v : ℝ)
    (h : PeriodEquivalent period u v) :
    PeriodEquivalent period v u := by
  rcases h with ⟨n, rfl⟩
  refine ⟨-n, ?_⟩
  push_cast
  ring

/-- Period equivalence is transitive. -/
theorem period_equivalent_trans
    (period u v w : ℝ)
    (huv : PeriodEquivalent period u v)
    (hvw : PeriodEquivalent period v w) :
    PeriodEquivalent period u w := by
  rcases huv with ⟨n, rfl⟩
  rcases hvw with ⟨m, rfl⟩
  refine ⟨n + m, ?_⟩
  push_cast
  ring

/-- Setoid defining the additive period circle. -/
def periodSetoid (period : ℝ) : Setoid ℝ where
  r := PeriodEquivalent period
  iseqv :=
    { refl := period_equivalent_refl period
      symm := period_equivalent_symm period
      trans := period_equivalent_trans period }

/-- Algebraic circle of circumference/period `T`. -/
abbrev PeriodCircle (period : ℝ) :=
  Quotient (periodSetoid period)

/-- Class of a logarithmic coordinate in the period circle. -/
def periodClass (period u : ℝ) : PeriodCircle period :=
  Quotient.mk' u

/-- Adding one period does not change the circle class. -/
theorem period_class_add_period
    (period u : ℝ) :
    periodClass period u = periodClass period (u + period) := by
  apply Quotient.sound
  refine ⟨1, ?_⟩
  norm_num

/-- Adding an arbitrary integer multiple of the period does not change the class. -/
theorem period_class_add_integer_period
    (period u : ℝ)
    (n : ℤ) :
    periodClass period u =
      periodClass period (u + (n : ℝ) * period) := by
  apply Quotient.sound
  exact ⟨n, rfl⟩

/--
On a point fixed by the reflection, one twisted mapping-torus step descends to
the same point of the period circle.
-/
theorem fixed_fiber_step_descends_to_circle
    {X : Type*}
    (rho : X → X)
    (period : ℝ)
    (x : X)
    (u : ℝ)
    (hFixed : FixedBy rho x) :
    periodClass period
        (twistedStep rho period (x, u)).2 =
      periodClass period u := by
  rw [twisted_step_on_fixed_point rho period x u hFixed]
  exact (period_class_add_period period u).symm

/--
The quotient is now constructed as a type.  The remaining geometric work is to
supply its quotient topology, prove it is homeomorphic/diffeomorphic to the
standard circle for nonzero period, and combine it with the equatorial `S2`.
-/
structure PeriodCircleGeometryStatus where
  periodNonzero : Prop
  quotientTopologyDefined : Prop
  standardCircleHomeomorphismConstructed : Prop
  smoothCircleStructureConstructed : Prop
  fixedLocusProductMapConstructed : Prop
  fixedLocusIdentifiedWithS2TimesCircle : Prop


def periodCircleGeometryClosed
    (s : PeriodCircleGeometryStatus) : Prop :=
  s.periodNonzero /\
  s.quotientTopologyDefined /\
  s.standardCircleHomeomorphismConstructed /\
  s.smoothCircleStructureConstructed /\
  s.fixedLocusProductMapConstructed /\
  s.fixedLocusIdentifiedWithS2TimesCircle

end P0EFTJanusPeriodCircleQuotient
end JanusFormal
