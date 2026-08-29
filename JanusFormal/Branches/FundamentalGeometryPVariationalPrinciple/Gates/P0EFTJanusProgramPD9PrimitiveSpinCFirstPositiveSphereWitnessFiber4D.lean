import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
import Mathlib.Tactic

/-!
# Opposite Hopf witness identities in the SpinC fiber

The two constant Hopf frame maps are

`F₊(ψ) = ψ - J Γ₂ ψ`,
`F₋(ψ) = ψ + J Γ₂ ψ`.

Their sum is the equatorial witness already used by the real multiplicity
proof, while their difference is the fiber value produced by the antipodal
phase.  On every normal-mode fiber satisfying `Γ₁ ψ = J Γ₂ ψ`, the two
witnesses obey opposite tangential Clifford relations:

`Γ₁(F₊+F₋) =  J Γ₂(F₊+F₋)`,
`Γ₁(F₊-F₋) = -J Γ₂(F₊-F₋)`.

This gate proves those identities without choosing a quotient chart.  The
remaining geometric step is only to show that the monopole values at phases
`0` and `π` select the sum and difference respectively.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D

/-- Fiber value selected when the two Hopf scalar representatives have the
same phase. -/
def primitiveSpinCHopfPositiveWitnessFiber
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCHopfFirstFrameCLM sector matter +
    d9PrimitiveSpinCHopfSecondFrameCLM sector matter

/-- Fiber value selected when the complementary Hopf representative changes
sign at the antipodal equatorial point. -/
def primitiveSpinCHopfAntipodalWitnessFiber
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCHopfFirstFrameCLM sector matter -
    d9PrimitiveSpinCHopfSecondFrameCLM sector matter

/-- The equal-phase witness is exactly twice the original normal-mode fiber. -/
theorem primitiveSpinCHopfPositiveWitnessFiber_eq_two_smul
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    primitiveSpinCHopfPositiveWitnessFiber sector matter =
      (2 : Real) • matter := by
  simp only [primitiveSpinCHopfPositiveWitnessFiber,
    d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply]
  module

/-- The antipodal witness is exactly `-2 J Γ₂` applied to the original
normal-mode fiber. -/
theorem primitiveSpinCHopfAntipodalWitnessFiber_eq
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    primitiveSpinCHopfAntipodalWitnessFiber sector matter =
      (-2 : Real) •
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter) := by
  simp only [primitiveSpinCHopfAntipodalWitnessFiber,
    d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply]
  module

/-- The equal-phase witness preserves the positive tangential Clifford
relation. -/
theorem primitiveSpinCHopfPositiveWitnessFiber_tangential
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hTangential :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfPositiveWitnessFiber sector matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfPositiveWitnessFiber sector matter)) := by
  rw [primitiveSpinCHopfPositiveWitnessFiber_eq_two_smul]
  simp only [map_smul]
  exact congrArg (fun current : D9DoubledMatterFiber => (2 : Real) • current)
    hTangential

/-- Core Clifford calculation behind the antipodal sign reversal. -/
theorem d9PrimitiveSpinCGammaOne_imaginary_gammaTwo
    (matter : D9DoubledMatterFiber)
    (hTangential :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) =
      -matter := by
  calc
    d9DoubledMatterFiberCliffordGammaCLM 1
          (d9PrimitiveSpinCImaginaryAction
            (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 1
            (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) := by
      rw [← d9PrimitiveSpinCImaginaryAction_clifford]
    _ =
        d9PrimitiveSpinCImaginaryAction
          (-d9DoubledMatterFiberCliffordGammaCLM 2
            (d9DoubledMatterFiberCliffordGammaCLM 1 matter)) := by
      simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
      rw [d9DoubledMatterFiberCliffordGamma_anticommute 1 2 (by decide)]
    _ =
        d9PrimitiveSpinCImaginaryAction
          (-d9DoubledMatterFiberCliffordGammaCLM 2
            (d9PrimitiveSpinCImaginaryAction
              (d9DoubledMatterFiberCliffordGammaCLM 2 matter))) := by
      rw [hTangential]
    _ =
        d9PrimitiveSpinCImaginaryAction
          (-d9PrimitiveSpinCImaginaryAction
            (d9DoubledMatterFiberCliffordGammaCLM 2
              (d9DoubledMatterFiberCliffordGammaCLM 2 matter))) := by
      rw [← d9PrimitiveSpinCImaginaryAction_clifford]
    _ =
        d9PrimitiveSpinCImaginaryAction
          (-d9PrimitiveSpinCImaginaryAction (-matter)) := by
      simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
      rw [d9DoubledMatterFiberCliffordGamma_sq]
    _ = -matter := by
      simp only [map_neg, d9PrimitiveSpinCImaginaryAction_sq, neg_neg]

/-- The left side of the antipodal tangential relation reduces to `2 ψ`. -/
theorem primitiveSpinCHopfAntipodalWitnessFiber_gammaOne
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hTangential :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfAntipodalWitnessFiber sector matter) =
      (2 : Real) • matter := by
  rw [primitiveSpinCHopfAntipodalWitnessFiber_eq, map_smul,
    d9PrimitiveSpinCGammaOne_imaginary_gammaTwo matter hTangential]
  module

/-- The right side of the antipodal tangential relation also reduces to
`2 ψ`. -/
theorem primitiveSpinCHopfAntipodalWitnessFiber_negative_imaginary_gammaTwo
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfAntipodalWitnessFiber sector matter)) =
      (2 : Real) • matter := by
  rw [primitiveSpinCHopfAntipodalWitnessFiber_eq, map_smul,
    ← d9PrimitiveSpinCImaginaryAction_clifford]
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [d9DoubledMatterFiberCliffordGamma_sq, map_smul,
    d9PrimitiveSpinCImaginaryAction_sq]
  module

/-- The antipodal phase reverses the tangential complex Clifford relation. -/
theorem primitiveSpinCHopfAntipodalWitnessFiber_tangential
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hTangential :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfAntipodalWitnessFiber sector matter) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfAntipodalWitnessFiber sector matter)) := by
  rw [primitiveSpinCHopfAntipodalWitnessFiber_gammaOne
      sector matter hTangential,
    primitiveSpinCHopfAntipodalWitnessFiber_negative_imaginary_gammaTwo]

/-- Consolidated opposite-witness fiber package. -/
theorem primitiveSpinCHopfOppositeWitnessFiber_closed
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (hTangential :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    primitiveSpinCHopfPositiveWitnessFiber sector matter =
        (2 : Real) • matter ∧
      primitiveSpinCHopfAntipodalWitnessFiber sector matter =
        (-2 : Real) •
          d9PrimitiveSpinCImaginaryAction
            (d9DoubledMatterFiberCliffordGammaCLM 2 matter) ∧
      d9DoubledMatterFiberCliffordGammaCLM 1
          (primitiveSpinCHopfPositiveWitnessFiber sector matter) =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2
            (primitiveSpinCHopfPositiveWitnessFiber sector matter)) ∧
      d9DoubledMatterFiberCliffordGammaCLM 1
          (primitiveSpinCHopfAntipodalWitnessFiber sector matter) =
        -d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2
            (primitiveSpinCHopfAntipodalWitnessFiber sector matter)) :=
  ⟨primitiveSpinCHopfPositiveWitnessFiber_eq_two_smul sector matter,
    primitiveSpinCHopfAntipodalWitnessFiber_eq sector matter,
    primitiveSpinCHopfPositiveWitnessFiber_tangential
      sector matter hTangential,
    primitiveSpinCHopfAntipodalWitnessFiber_tangential
      sector matter hTangential⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
end JanusFormal
