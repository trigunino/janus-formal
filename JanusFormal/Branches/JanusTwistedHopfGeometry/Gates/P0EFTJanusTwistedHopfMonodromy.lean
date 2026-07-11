import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedHopfMonodromy

set_option autoImplicit false

/-- The two oriented folds of the Janus orientation double cover. -/
inductive Fold where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- One traversal of the PT-twisted tunnel exchanges the two folds. -/
def tunnelStep : Fold → Fold
  | Fold.plus => Fold.minus
  | Fold.minus => Fold.plus

@[simp] theorem tunnel_step_is_involutive (f : Fold) :
    tunnelStep (tunnelStep f) = f := by
  cases f <;> rfl

@[simp] theorem tunnel_step_has_no_fixed_fold (f : Fold) :
    tunnelStep f ≠ f := by
  cases f <;> decide

/-- The monodromy group is infinite cyclic; even powers preserve orientation. -/
def OrientationPreservingMonodromy (n : ℤ) : Prop := Even n

@[simp] theorem one_step_reverses_orientation :
    Not (OrientationPreservingMonodromy 1) := by
  simp [OrientationPreservingMonodromy]

@[simp] theorem two_steps_preserve_orientation :
    OrientationPreservingMonodromy 2 := by
  exact ⟨1, by norm_num⟩

/-- Orientation-preserving monodromies are closed under composition. -/
theorem orientation_preserving_add
    (m n : ℤ)
    (hm : OrientationPreservingMonodromy m)
    (hn : OrientationPreservingMonodromy n) :
    OrientationPreservingMonodromy (m + n) := by
  exact hm.add hn

/-- Every orientation-preserving monodromy is an even power of the generator. -/
theorem orientation_preserving_iff_double
    (n : ℤ) :
    OrientationPreservingMonodromy n ↔ ∃ k : ℤ, n = 2 * k := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    nlinarith
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/--
The geometric PT deck transformation is order two on the orientation cover.
A Pin/fermionic lift may instead be a central order-four extension.
-/
abbrev PinPhase := ZMod 4

/-- Lift of one geometric PT traversal. -/
def pinTunnelGenerator : PinPhase := 1

/-- Fermion parity in the additive `ZMod 4` convention. -/
def fermionParity : PinPhase := 2

@[simp] theorem pin_generator_square_is_fermion_parity :
    pinTunnelGenerator + pinTunnelGenerator = fermionParity := by
  norm_num [pinTunnelGenerator, fermionParity]

@[simp] theorem pin_generator_fourth_power_is_identity :
    pinTunnelGenerator + pinTunnelGenerator +
      pinTunnelGenerator + pinTunnelGenerator = 0 := by
  norm_num [pinTunnelGenerator]

@[simp] theorem pin_generator_square_is_nontrivial :
    pinTunnelGenerator + pinTunnelGenerator ≠ 0 := by
  norm_num [pinTunnelGenerator]

/--
This is the precise meaning of a genuine `Z4` in the resolved geometry:
its square is fermion parity, while its projection to spacetime is the `Z2`
fold exchange.
-/
structure PinLiftedTunnelMonodromy where
  geometricFoldExchangeDerived : Prop
  pinLiftDefined : Prop
  squareEqualsFermionParity : Prop
  fourthPowerIdentity : Prop
  fermionParityNontrivial : Prop


def pinLiftedZ4Closed (s : PinLiftedTunnelMonodromy) : Prop :=
  s.geometricFoldExchangeDerived /\
  s.pinLiftDefined /\
  s.squareEqualsFermionParity /\
  s.fourthPowerIdentity /\
  s.fermionParityNontrivial

end P0EFTJanusTwistedHopfMonodromy
end JanusFormal
