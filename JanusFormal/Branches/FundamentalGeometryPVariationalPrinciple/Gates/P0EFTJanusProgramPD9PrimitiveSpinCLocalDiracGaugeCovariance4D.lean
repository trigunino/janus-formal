import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCConnection4D

/-!
# Gauge-covariant local primitive SpinC Dirac block

This gate separates the representation-theoretic part of the coupled Dirac
operator from its geometric coefficients.  A local directional derivative is
corrected by an arbitrary real `U(1)` connection coefficient and contracted
with the three Clifford generators.  Exact gauge covariance follows from the
connection transformation law, without adding an axiom or spectral input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D

/-- One local SpinC covariant derivative `∂ + i A`. -/
def d9PrimitiveSpinCLocalDirectionalDerivative
    (connectionCoefficient : Real)
    (ordinaryDerivative matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  ordinaryDerivative +
    connectionCoefficient • d9PrimitiveSpinCImaginaryAction matter

/-- Leibniz transform of a directional derivative under a phase whose
logarithmic derivative has real coefficient `transitionCoefficient`. -/
def d9PrimitiveSpinCGaugeTransformedDirectionalPartial
    (transitionCoefficient : Real) (phase : Circle)
    (ordinaryDerivative matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  d9PrimitiveSpinCPhaseActionCLM phase ordinaryDerivative +
    transitionCoefficient •
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCPhaseActionCLM phase matter)

/-- Exact covariance of one connection direction. -/
theorem d9PrimitiveSpinCLocalDirectionalDerivative_gauge
    (northCoefficient southCoefficient transitionCoefficient : Real)
    (phase : Circle) (ordinaryDerivative matter : D9DoubledMatterFiber)
    (hCoefficient :
      transitionCoefficient + southCoefficient = northCoefficient) :
    d9PrimitiveSpinCLocalDirectionalDerivative southCoefficient
        (d9PrimitiveSpinCGaugeTransformedDirectionalPartial
          transitionCoefficient phase ordinaryDerivative matter)
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      d9PrimitiveSpinCPhaseActionCLM phase
        (d9PrimitiveSpinCLocalDirectionalDerivative
          northCoefficient ordinaryDerivative matter) := by
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
    d9PrimitiveSpinCGaugeTransformedDirectionalPartial
  rw [map_add, map_smul]
  rw [← d9PrimitiveSpinCImaginaryAction_commutes_phase]
  rw [add_assoc, ← add_smul, hCoefficient]

/-- Clifford contraction of the three local coupled derivatives. -/
def d9PrimitiveSpinCLocalDirac
    (connectionCoefficient : Fin 3 → Real)
    (ordinaryDerivative : Fin 3 → D9DoubledMatterFiber)
    (matter : D9DoubledMatterFiber) :
    D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGammaCLM direction
      (d9PrimitiveSpinCLocalDirectionalDerivative
        (connectionCoefficient direction)
        (ordinaryDerivative direction) matter)

/-- The local coupled Dirac contraction is exactly gauge covariant in all
three frame directions. -/
theorem d9PrimitiveSpinCLocalDirac_gauge
    (northCoefficient southCoefficient transitionCoefficient : Fin 3 → Real)
    (phase : Circle)
    (ordinaryDerivative : Fin 3 → D9DoubledMatterFiber)
    (matter : D9DoubledMatterFiber)
    (hCoefficient :
      ∀ direction,
        transitionCoefficient direction + southCoefficient direction =
          northCoefficient direction) :
    d9PrimitiveSpinCLocalDirac southCoefficient
        (fun direction =>
          d9PrimitiveSpinCGaugeTransformedDirectionalPartial
            (transitionCoefficient direction) phase
            (ordinaryDerivative direction) matter)
        (d9PrimitiveSpinCPhaseActionCLM phase matter) =
      d9PrimitiveSpinCPhaseActionCLM phase
        (d9PrimitiveSpinCLocalDirac
          northCoefficient ordinaryDerivative matter) := by
  unfold d9PrimitiveSpinCLocalDirac
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  rw [d9PrimitiveSpinCLocalDirectionalDerivative_gauge
    (hCoefficient := hCoefficient direction)]
  exact
    (d9PrimitiveSpinCPhaseAction_clifford
      phase direction
      (d9PrimitiveSpinCLocalDirectionalDerivative
        (northCoefficient direction)
        (ordinaryDerivative direction) matter)).symm

/-- The connection correction is zeroth order: changing only the ordinary
partials changes the Dirac block by their bare Clifford contraction. -/
theorem d9PrimitiveSpinCLocalDirac_partial_add
    (connectionCoefficient : Fin 3 → Real)
    (ordinaryDerivative increment : Fin 3 → D9DoubledMatterFiber)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCLocalDirac connectionCoefficient
        (fun direction =>
          ordinaryDerivative direction + increment direction) matter =
      d9PrimitiveSpinCLocalDirac
          connectionCoefficient ordinaryDerivative matter +
        ∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            (increment direction) := by
  simp only [d9PrimitiveSpinCLocalDirac,
    d9PrimitiveSpinCLocalDirectionalDerivative, add_assoc, map_add,
    Finset.sum_add_distrib]
  abel

end
end P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
end JanusFormal
