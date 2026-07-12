import Mathlib

namespace JanusFormal
namespace P0EFTJanusInvariantCoefficientModule

set_option autoImplicit false

universe u v w

/-- A light action interface sufficient for invariant scalar coefficients and
background-dependent pairing families. -/
structure ActionData (Symmetry : Type u) (Space : Type v) where
  act : Symmetry → Space → Space

/-- A scalar coefficient on the background-jet space is invariant when it is
constant along every symmetry orbit. -/
def IsInvariantScalar
    {Symmetry : Type u}
    {Base : Type v}
    (baseAction : ActionData Symmetry Base)
    (coefficient : Base → ℝ) : Prop :=
  ∀ symmetry base,
    coefficient (baseAction.act symmetry base) = coefficient base

/-- A background-dependent pairing is invariant when the background and both
field arguments are transformed simultaneously. -/
def IsInvariantPairing
    {Symmetry : Type u}
    {Base : Type v}
    {Field : Type w}
    (baseAction : ActionData Symmetry Base)
    (fieldAction : ActionData Symmetry Field)
    (pairing : Base → Field → Field → ℝ) : Prop :=
  ∀ symmetry base first second,
    pairing
        (baseAction.act symmetry base)
        (fieldAction.act symmetry first)
        (fieldAction.act symmetry second) =
      pairing base first second

/-- Multiplication of a pairing family by a scalar coefficient on the
background-jet space. -/
def scalePairing
    {Base : Type v}
    {Field : Type w}
    (coefficient : Base → ℝ)
    (pairing : Base → Field → Field → ℝ) :
    Base → Field → Field → ℝ :=
  fun base first second => coefficient base * pairing base first second

/-- Invariant pairing families are closed under multiplication by invariant
scalar coefficients. This is the formal module-closure statement needed by
Program P-D. -/
theorem scale_pairing_preserves_invariance
    {Symmetry : Type u}
    {Base : Type v}
    {Field : Type w}
    (baseAction : ActionData Symmetry Base)
    (fieldAction : ActionData Symmetry Field)
    (coefficient : Base → ℝ)
    (pairing : Base → Field → Field → ℝ)
    (hCoefficient : IsInvariantScalar baseAction coefficient)
    (hPairing : IsInvariantPairing baseAction fieldAction pairing) :
    IsInvariantPairing baseAction fieldAction
      (scalePairing coefficient pairing) := by
  intro symmetry base first second
  simp only [scalePairing]
  rw [hCoefficient symmetry base]
  rw [hPairing symmetry base first second]

/-- Trivial action, used for the finite counterexample below. -/
def trivialAction
    (Symmetry : Type u)
    (Space : Type v) : ActionData Symmetry Space where
  act := fun _ value => value

/-- One fixed pointwise pairing shape. -/
def constantPairing : Bool → ℝ → ℝ → ℝ :=
  fun _ first second => first * second

/-- A nonconstant scalar coefficient on the two-point background space. -/
def switchingCoefficient : Bool → ℝ
  | false => 0
  | true => 1

/-- The same pointwise pairing shape with a background-dependent coefficient. -/
def varyingPairing : Bool → ℝ → ℝ → ℝ :=
  scalePairing switchingCoefficient constantPairing

@[simp] theorem switching_coefficient_is_invariant :
    IsInvariantScalar
      (trivialAction Unit Bool)
      switchingCoefficient := by
  intro symmetry base
  rfl

@[simp] theorem constant_pairing_is_invariant :
    IsInvariantPairing
      (trivialAction Unit Bool)
      (trivialAction Unit ℝ)
      constantPairing := by
  intro symmetry base first second
  rfl

@[simp] theorem varying_pairing_is_invariant :
    IsInvariantPairing
      (trivialAction Unit Bool)
      (trivialAction Unit ℝ)
      varyingPairing :=
  scale_pairing_preserves_invariance
    (trivialAction Unit Bool)
    (trivialAction Unit ℝ)
    switchingCoefficient
    constantPairing
    switching_coefficient_is_invariant
    constant_pairing_is_invariant

/-- Even when every fiber uses the same one-dimensional pairing shape, a
background-dependent invariant coefficient need not be one constant global
normalization. -/
theorem varying_pairing_is_not_one_constant_multiple :
    Not (∃ coefficient : ℝ, ∀ base first second,
      varyingPairing base first second =
        coefficient * constantPairing base first second) := by
  rintro ⟨coefficient, hCoefficient⟩
  have hZero : (0 : ℝ) = coefficient := by
    simpa [varyingPairing, scalePairing, switchingCoefficient,
      constantPairing] using hCoefficient false 1 1
  have hOne : (1 : ℝ) = coefficient := by
    simpa [varyingPairing, scalePairing, switchingCoefficient,
      constantPairing] using hCoefficient true 1 1
  linarith

/-- Compact finite-model verdict: pointwise multiplicity one does not imply
one-dimensional global coupling space over the constant scalars. -/
theorem pointwise_shape_does_not_force_global_constant_scale :
    IsInvariantPairing
        (trivialAction Unit Bool)
        (trivialAction Unit ℝ)
        constantPairing /\
      IsInvariantPairing
        (trivialAction Unit Bool)
        (trivialAction Unit ℝ)
        varyingPairing /\
      Not (∃ coefficient : ℝ, ∀ base first second,
        varyingPairing base first second =
          coefficient * constantPairing base first second) := by
  exact ⟨constant_pairing_is_invariant,
    varying_pairing_is_invariant,
    varying_pairing_is_not_one_constant_multiple⟩

/-- The extra data required to promote pointwise pairing dimensions to a global
natural-coupling classification. -/
structure GlobalPairingClassificationStatus where
  pointwiseInvariantSpacesComputed : Prop
  jetOrbitStratificationControlled : Prop
  invariantScalarAlgebraComputed : Prop
  equivariantPairingModuleComputed : Prop
  coefficientClassRestricted : Prop
  physicalNormalizationDerived : Prop

/-- Full global pairing closure. -/
def globalPairingClassificationClosed
    (s : GlobalPairingClassificationStatus) : Prop :=
  s.pointwiseInvariantSpacesComputed /\
  s.jetOrbitStratificationControlled /\
  s.invariantScalarAlgebraComputed /\
  s.equivariantPairingModuleComputed /\
  s.coefficientClassRestricted /\
  s.physicalNormalizationDerived

/-- Pointwise multiplicity one cannot close the global problem while the
invariant coefficient algebra is uncontrolled. -/
theorem missing_invariant_scalar_algebra_blocks_global_classification
    (s : GlobalPairingClassificationStatus)
    (hMissing : Not s.invariantScalarAlgebraComputed) :
    Not (globalPairingClassificationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end P0EFTJanusInvariantCoefficientModule
end JanusFormal
