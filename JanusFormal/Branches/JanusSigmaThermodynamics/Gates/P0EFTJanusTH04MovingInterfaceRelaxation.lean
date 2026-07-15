import JanusFormal.Branches.JanusSigmaThermodynamics.Gates.P0EFTJanusTH03EntropyPositivity

namespace JanusFormal
namespace P0EFTJanusTH04MovingInterfaceRelaxation

set_option autoImplicit false

noncomputable section

open P0EFTJanusTH03EntropyPositivity

/-- Rankine-Hugoniot residual for a moving interface. -/
def movingInterfaceResidual
    (plusFlux minusFlux speed plusDensity minusDensity sigmaSource : ℝ) : ℝ :=
  plusFlux - minusFlux - speed * (plusDensity - minusDensity) - sigmaSource

theorem stationary_source_free_interface_reduces_to_flux_continuity
    (plusFlux minusFlux : ℝ) :
    movingInterfaceResidual plusFlux minusFlux 0 0 0 0 =
      plusFlux - minusFlux := by
  unfold movingInterfaceResidual
  ring

theorem interface_source_closes_jump_balance
    (plusFlux minusFlux speed plusDensity minusDensity : ℝ) :
    movingInterfaceResidual plusFlux minusFlux speed plusDensity minusDensity
      (plusFlux - minusFlux - speed * (plusDensity - minusDensity)) = 0 := by
  unfold movingInterfaceResidual
  ring

/-- Quadratic Lyapunov function for two thermodynamic forces. -/
def quadraticLyapunov (x y : ℝ) : ℝ := (x ^ 2 + y ^ 2) / 2

/-- Along `Xdot=-L X`, the Lyapunov derivative is minus the entropy-producing
quadratic form. -/
def lyapunovDerivative
    (l11 symmetricCross l22 x y : ℝ) : ℝ :=
  -quadraticEntropyProduction l11 symmetricCross l22 x y

theorem positive_transport_makes_lyapunov_nonincreasing
    (l11 symmetricCross l22 x y : ℝ)
    (h11 : 0 < l11)
    (hDet : symmetricCross ^ 2 ≤ l11 * l22) :
    lyapunovDerivative l11 symmetricCross l22 x y ≤ 0 := by
  unfold lyapunovDerivative
  exact neg_nonpos.mpr
    (positive_semidefinite_transport_gives_nonnegative_entropy
      l11 symmetricCross l22 x y h11 hDet)

structure TH04Inputs where
  interfaceVelocityDerived : Prop
  surfaceEnergyDensityDerived : Prop
  surfaceEntropyDensityDerived : Prop
  jumpConditionsDerivedFromP : Prop
  relaxationMatrixDerivedFromP : Prop

def physicalTH04Closed (s : TH04Inputs) : Prop :=
  s.interfaceVelocityDerived ∧
  s.surfaceEnergyDensityDerived ∧
  s.surfaceEntropyDensityDerived ∧
  s.jumpConditionsDerivedFromP ∧
  s.relaxationMatrixDerivedFromP

end

end P0EFTJanusTH04MovingInterfaceRelaxation
end JanusFormal
