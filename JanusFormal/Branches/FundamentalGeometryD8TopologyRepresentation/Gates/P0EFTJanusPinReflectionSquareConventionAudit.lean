import Mathlib

namespace JanusFormal
namespace P0EFTJanusPinReflectionSquareConventionAudit

set_option autoImplicit false

/-- Standard Clifford-algebra naming by the square of a unit reflection lift. -/
inductive PinCliffordSign where
  | pinPlus
  | pinMinus
  deriving DecidableEq, Repr

/-- In the standard Clifford convention, a reflection lift squares to `+1` in
`Pin+` and to `-1` in `Pin-`. -/
def reflectionLiftSquare : PinCliffordSign → ℤ
  | PinCliffordSign.pinPlus => 1
  | PinCliffordSign.pinMinus => -1

@[simp] theorem pin_plus_reflection_square :
    reflectionLiftSquare PinCliffordSign.pinPlus = 1 := by
  rfl

@[simp] theorem pin_minus_reflection_square :
    reflectionLiftSquare PinCliffordSign.pinMinus = -1 := by
  rfl

/-- The standard `Pin+` reflection lift has the order-two square pattern. -/
theorem pin_plus_reflection_has_order_two_pattern :
    reflectionLiftSquare PinCliffordSign.pinPlus = 1 /\
      reflectionLiftSquare PinCliffordSign.pinPlus ^ 2 = 1 := by
  norm_num [reflectionLiftSquare]

/-- The standard `Pin-` reflection lift has the order-four square pattern. -/
theorem pin_minus_reflection_has_order_four_pattern :
    reflectionLiftSquare PinCliffordSign.pinMinus = -1 /\
      reflectionLiftSquare PinCliffordSign.pinMinus ^ 2 = 1 := by
  norm_num [reflectionLiftSquare]

/-- A reflection lift squaring to `-1` cannot be the standard `Pin+` lift. -/
theorem square_minus_one_excludes_standard_pin_plus
    (sign : PinCliffordSign)
    (hSquare : reflectionLiftSquare sign = -1) :
    sign = PinCliffordSign.pinMinus := by
  cases sign
  · norm_num [reflectionLiftSquare] at hSquare
  · rfl

/-- A reflection lift squaring to `+1` cannot be the standard `Pin-` lift. -/
theorem square_plus_one_excludes_standard_pin_minus
    (sign : PinCliffordSign)
    (hSquare : reflectionLiftSquare sign = 1) :
    sign = PinCliffordSign.pinPlus := by
  cases sign
  · rfl
  · norm_num [reflectionLiftSquare] at hSquare

/--
Physics papers sometimes label Euclidean Pin structures through the square of
an antiunitary time-reversal operator rather than directly through the
Clifford reflection lift.  A Program-D claim of a fermionic order-four
monodromy must therefore state the dictionary explicitly instead of silently
identifying `Pin+`, `Pin-`, reflection square and `T^2`.
-/
structure PinConventionDictionaryStatus where
  cliffordSignatureConventionFixed : Prop
  geometricReflectionLiftConstructed : Prop
  reflectionLiftSquareComputed : Prop
  euclideanToLorentzianContinuationDerived : Prop
  antiunitaryPTActionConstructed : Prop
  fermionParityIdentificationProved : Prop
  pinLabelDictionaryProved : Prop
  orderFourClaimConventionIndependent : Prop


def pinConventionDictionaryClosed
    (s : PinConventionDictionaryStatus) : Prop :=
  s.cliffordSignatureConventionFixed /\
  s.geometricReflectionLiftConstructed /\
  s.reflectionLiftSquareComputed /\
  s.euclideanToLorentzianContinuationDerived /\
  s.antiunitaryPTActionConstructed /\
  s.fermionParityIdentificationProved /\
  s.pinLabelDictionaryProved /\
  s.orderFourClaimConventionIndependent

end P0EFTJanusPinReflectionSquareConventionAudit
end JanusFormal
