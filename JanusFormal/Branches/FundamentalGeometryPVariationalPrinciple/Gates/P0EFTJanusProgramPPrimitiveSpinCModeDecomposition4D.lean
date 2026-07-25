import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D

/-!
# Primitive SpinC mode decomposition

The complete primitive spectrum is the disjoint union of the monopole sphere
zero sector and the positive sphere levels already used by the legacy product
Dirac model.  This gate gives the exact equivalence of mode labels and proves
that the squared eigenvalues agree on both summands.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Positive primitive sphere levels, before identifying their multiplicity
labels with the legacy product model. -/
abbrev PrimitiveSpinCPositiveSphereMode :=
  Σ level : Nat, Fin (primitiveSphereModeDegeneracy (level + 1))

/-- Exact identification of each positive-level multiplicity fiber. -/
def primitiveSpinCPositiveMultiplicityEquiv (level : Nat) :
    Fin (primitiveSphereModeDegeneracy (level + 1)) ≃
      Fin (sphereMultiplicity
        (PrimitiveSpinCSpectralData period hPeriod) level) :=
  Equiv.cast <| congrArg Fin <|
    primitiveSpinCFull_positiveSphereMultiplicity_agrees
      period hPeriod level

/-- Exact identification of all positive primitive sphere labels with the
legacy charge-one sphere labels. -/
def primitiveSpinCPositiveSphereModeEquiv :
    PrimitiveSpinCPositiveSphereMode ≃
      ProductThroatSphereMode
        (PrimitiveSpinCSpectralData period hPeriod) :=
  Equiv.sigmaCongrRight fun level =>
    primitiveSpinCPositiveMultiplicityEquiv period hPeriod level

/-- The zero-level multiplicity fiber is a singleton. -/
def primitiveSpinCZeroMultiplicityEquiv :
    Fin (primitiveSphereModeDegeneracy 0) ≃ Fin 1 :=
  Equiv.cast <| congrArg Fin primitive_sphere_zero_mode_degeneracy

/-- Remove the singleton zero-level multiplicity label. -/
def primitiveSpinCZeroProductEquiv :
    Fin (primitiveSphereModeDegeneracy 0) × Int ≃ Int :=
  ((primitiveSpinCZeroMultiplicityEquiv.prodCongr
      (Equiv.refl Int)).trans
    (Equiv.uniqueProd Int (Fin 1)))

/-- The complete primitive mode set is exactly the circle zero-sphere sector
plus the positive-level product mode set. -/
def primitiveSpinCFullModeEquiv :
    PrimitiveSpinCFullMode ≃
      Int ⊕ ProductThroatHeatMode
        (PrimitiveSpinCSpectralData period hPeriod) :=
  ((((Equiv.sigmaNatSucc fun level : Nat =>
        Fin (primitiveSphereModeDegeneracy level)).prodCongr
          (Equiv.refl Int)).trans
      (Equiv.sumProdDistrib
        (Fin (primitiveSphereModeDegeneracy 0))
        PrimitiveSpinCPositiveSphereMode Int)).trans
    (Equiv.sumCongr
      primitiveSpinCZeroProductEquiv
      ((primitiveSpinCPositiveSphereModeEquiv period hPeriod).prodCongr
        (Equiv.refl Int))))

/-- Canonical embedding of an old positive-level product mode into the full
primitive spectrum. -/
def primitiveSpinCPositiveModeEmbedding
    (mode : ProductThroatHeatMode
      (PrimitiveSpinCSpectralData period hPeriod)) :
    PrimitiveSpinCFullMode :=
  (⟨mode.1.1 + 1,
      (primitiveSpinCPositiveMultiplicityEquiv
        period hPeriod mode.1.1).symm mode.1.2⟩,
    mode.2)

/-- Canonical full primitive mode in the monopole sphere zero sector. -/
def primitiveSpinCZeroSphereMode (circleMode : Int) :
    PrimitiveSpinCFullMode :=
  (⟨0, primitiveSpinCZeroMultiplicityEquiv.symm 0⟩, circleMode)

@[simp]
theorem primitiveSpinCFullModeEquiv_positive
    (mode : ProductThroatHeatMode
      (PrimitiveSpinCSpectralData period hPeriod)) :
    primitiveSpinCFullModeEquiv period hPeriod
        (primitiveSpinCPositiveModeEmbedding period hPeriod mode) =
      Sum.inr mode :=
  by
    rcases mode with ⟨⟨level, multiplicity⟩, circleMode⟩
    rfl

@[simp]
theorem primitiveSpinCFullModeEquiv_zero
    (circleMode : Int) :
    primitiveSpinCFullModeEquiv period hPeriod
        (primitiveSpinCZeroSphereMode circleMode) =
      Sum.inl circleMode :=
  by
    rfl

theorem primitiveSpinCPositiveModeEmbedding_injective :
    Function.Injective
      (primitiveSpinCPositiveModeEmbedding period hPeriod) := by
  intro first second h
  have hMapped := congrArg
    (primitiveSpinCFullModeEquiv period hPeriod) h
  simpa using hMapped

theorem primitiveSpinCZeroSphereMode_injective :
    Function.Injective
      primitiveSpinCZeroSphereMode := by
  intro first second h
  exact congrArg Prod.snd h

/-- On the zero-sphere summand the complete squared operator is exactly the
circle squared operator. -/
theorem primitiveSpinCZeroSphereMode_squaredEigenvalue
    (fold : Fold) (twist : CircleTwist) (circleMode : Int) :
    primitiveSpinCFullDiracSquaredEigenvalue fold twist
        (primitiveSpinCZeroSphereMode circleMode) =
      circleOperatorSquaredEigenvalue fold twist circleMode := by
  simp [primitiveSpinCZeroSphereMode,
    primitiveSpinCFullDiracSquaredEigenvalue]

/-- On the positive-level summand the complete squared spectrum is exactly
the existing charge-one product Dirac spectrum. -/
theorem primitiveSpinCPositiveMode_squaredEigenvalue
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode
      (PrimitiveSpinCSpectralData period hPeriod)) :
    primitiveSpinCFullDiracSquaredEigenvalue fold twist
        (primitiveSpinCPositiveModeEmbedding period hPeriod mode) =
      productThroatDiracSquaredEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod) fold twist mode := by
  rcases mode with ⟨⟨level, multiplicity⟩, circleMode⟩
  change
    primitiveSpinCFullSphereEigenvalueSquared (level + 1) +
        circleOperatorSquaredEigenvalue fold twist circleMode =
      sphereEigenvalueSquared
          (PrimitiveSpinCSpectralData period hPeriod) level +
        circleOperatorSquaredEigenvalue fold twist circleMode
  rw [primitiveSpinCFull_positiveSphereEigenvalue_agrees
    period hPeriod level]

end
end P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D
end JanusFormal
