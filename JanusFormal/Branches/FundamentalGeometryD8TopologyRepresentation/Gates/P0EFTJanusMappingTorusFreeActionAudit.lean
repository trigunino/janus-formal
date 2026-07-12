import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTwistedMappingGenerator

namespace JanusFormal
namespace P0EFTJanusMappingTorusFreeActionAudit

set_option autoImplicit false

open P0EFTJanusTwistedMappingGenerator

variable {X : Type*}

/--
Algebraic integer action underlying the twisted mapping torus.  The fiber
component only records the parity of the iterate because `rho` is involutive;
the logarithmic coordinate always advances by `n*T`.
-/
def twistedIntegerStep
    (rho : X → X)
    (period : ℝ)
    (iterate : ℤ)
    (point : X × ℝ) : X × ℝ :=
  (if Even iterate then point.1 else rho point.1,
    point.2 + (iterate : ℝ) * period)

@[simp] theorem twisted_integer_step_second_coordinate
    (rho : X → X)
    (period : ℝ)
    (iterate : ℤ)
    (point : X × ℝ) :
    (twistedIntegerStep rho period iterate point).2 =
      point.2 + (iterate : ℝ) * period := by
  rfl

/-- Every nonzero iterate is fixed-point free when the translation period is nonzero. -/
theorem nonzero_integer_step_has_no_fixed_point
    (rho : X → X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (iterate : ℤ)
    (hIterate : iterate ≠ 0)
    (point : X × ℝ) :
    twistedIntegerStep rho period iterate point ≠ point := by
  intro hFixed
  have hSecond := congrArg Prod.snd hFixed
  change point.2 + (iterate : ℝ) * period = point.2 at hSecond
  have hProduct : (iterate : ℝ) * period = 0 := by
    linarith
  have hCast : (iterate : ℝ) = 0 :=
    (mul_eq_zero.mp hProduct).resolve_right hPeriod
  have hInteger : iterate = 0 := by
    exact_mod_cast hCast
  exact hIterate hInteger

/-- In particular, the one-step generator has no fixed point. -/
theorem twisted_generator_has_no_fixed_point
    (rho : X → X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (point : X × ℝ) :
    twistedStep rho period point ≠ point := by
  intro hFixed
  have hSecond := congrArg Prod.snd hFixed
  change point.2 + period = point.2 at hSecond
  exact hPeriod (by linarith)

/-- Two sheet labels in the orientation cover. -/
inductive WorldSide where
  | sideA
  | sideB
  deriving DecidableEq, Repr

/-- One orientation-reversing circuit exchanges the two sides. -/
def exchangeSide : WorldSide → WorldSide
  | WorldSide.sideA => WorldSide.sideB
  | WorldSide.sideB => WorldSide.sideA

@[simp] theorem exchange_side_twice
    (side : WorldSide) :
    exchangeSide (exchangeSide side) = side := by
  cases side <;> rfl

/-- There is no globally fixed side under one circuit. -/
theorem exchange_side_has_no_fixed_point
    (side : WorldSide) :
    exchangeSide side ≠ side := by
  cases side <;> decide

/-- Normal transport around the throat circle reverses a local normal vector. -/
def normalTransportOneLoop (normal : ℝ) : ℝ :=
  -normal

@[simp] theorem normal_transport_two_loops
    (normal : ℝ) :
    normalTransportOneLoop (normalTransportOneLoop normal) = normal := by
  simp [normalTransportOneLoop]

/-- A normal vector invariant under the reversing monodromy must vanish. -/
theorem invariant_normal_is_zero
    (normal : ℝ)
    (hInvariant : normalTransportOneLoop normal = normal) :
    normal = 0 := by
  unfold normalTransportOneLoop at hInvariant
  linarith

/-- Symmetric two-sheet volume bookkeeping. -/
structure SymmetricCoverVolumeData where
  sideAVolume : ℝ
  sideBVolume : ℝ
  quotientVolume : ℝ
  coverVolume : ℝ
  deckIsometry : sideAVolume = sideBVolume
  quotientIsOneFundamentalDomain : quotientVolume = sideAVolume
  coverIsSumOfSides : coverVolume = sideAVolume + sideBVolume

/-- The two worlds have equal volume under the deck symmetry. -/
theorem deck_symmetry_gives_one_to_one_world_ratio
    (s : SymmetricCoverVolumeData) :
    s.sideAVolume = s.sideBVolume :=
  s.deckIsometry

/-- The two-to-one ratio is between the orientation cover and the quotient. -/
theorem orientation_cover_is_twice_quotient_volume
    (s : SymmetricCoverVolumeData) :
    s.coverVolume = 2 * s.quotientVolume := by
  calc
    s.coverVolume = s.sideAVolume + s.sideBVolume :=
      s.coverIsSumOfSides
    _ = s.sideAVolume + s.sideAVolume := by
      rw [← s.deckIsometry]
    _ = 2 * s.sideAVolume := by ring
    _ = 2 * s.quotientVolume := by
      rw [s.quotientIsOneFundamentalDomain]

/--
A nonzero translation removes all local isotropy from the reflection action.
Thus the proposed quotient is a smooth mapping-torus candidate, not an orbifold
with a singular fixed locus.  The equatorial throat is instead a one-sided
embedded hypersurface: its two local sides become globally distinct only on the
orientation double cover.
-/
structure MappingTorusVersusOrbifoldStatus where
  integerActionConstructed : Prop
  nonzeroTranslationProved : Prop
  actionFreeProved : Prop
  actionProperlyDiscontinuousProved : Prop
  smoothQuotientConstructed : Prop
  equatorialSubmanifoldConstructed : Prop
  normalLineMonodromyMinusOneProved : Prop
  throatOneSidedProved : Prop
  orientationCoverConstructed : Prop
  complementHasTwoComponentsUpstairs : Prop
  deckTransformationExchangesComponents : Prop
  quotientComplementConnected : Prop


def mappingTorusVersusOrbifoldClosed
    (s : MappingTorusVersusOrbifoldStatus) : Prop :=
  s.integerActionConstructed /\
  s.nonzeroTranslationProved /\
  s.actionFreeProved /\
  s.actionProperlyDiscontinuousProved /\
  s.smoothQuotientConstructed /\
  s.equatorialSubmanifoldConstructed /\
  s.normalLineMonodromyMinusOneProved /\
  s.throatOneSidedProved /\
  s.orientationCoverConstructed /\
  s.complementHasTwoComponentsUpstairs /\
  s.deckTransformationExchangesComponents /\
  s.quotientComplementConnected

end P0EFTJanusMappingTorusFreeActionAudit
end JanusFormal
