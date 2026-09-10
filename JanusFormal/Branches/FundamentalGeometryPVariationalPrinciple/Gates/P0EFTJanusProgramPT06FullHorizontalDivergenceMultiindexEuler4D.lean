import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DirectionalHorizontalDivergenceEulerTelescoping4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MultiindexLocalEulerLinearity4D

/-!
# Euler soundness of a full horizontal divergence

Linearity upgrades the directional Euler telescoping theorem to the sum of
the three components of a smooth second-order horizontal current.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FullHorizontalDivergenceMultiindexEuler4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06MultiindexLocalEulerLinearity4D
open P0EFTJanusProgramPT06DirectionalHorizontalDivergenceEulerTelescoping4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- The order-four multi-index Euler operator annihilates the full
horizontal divergence of a smooth order-three current. -/
theorem programPT06SecondOrderHorizontalCurrentDH_multiindexEuler_eq_zero
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction))
    (jet : SpatialJet Fiber 8) :
    programPT06MultiindexLocalEuler 4
        (programPT06SecondOrderHorizontalCurrentDH current) jet = 0 := by
  let summand : Fin 3 → SpatialJet Fiber 4 → Real :=
    fun direction ↦
      programPT06ThroatSpatialLocalFunctionTotalDerivative
        direction (current direction)
  have hSummand (direction : Fin 3) :
      ContDiff Real ∞ (summand direction) := by
    exact programPT06ThroatSpatialLocalFunctionTotalDerivative_contDiff_top
      (current direction) (hCurrent direction) direction
  have hExpand :
      programPT06SecondOrderHorizontalCurrentDH current =
        summand 0 + (summand 1 + summand 2) := by
    funext fourthJet
    simp [programPT06SecondOrderHorizontalCurrentDH, summand,
      Fin.sum_univ_succ]
  rw [hExpand,
    programPT06MultiindexLocalEuler_add 4
      (summand 0) (summand 1 + summand 2)
      (hSummand 0) ((hSummand 1).add (hSummand 2)),
    programPT06MultiindexLocalEuler_add 4
      (summand 1) (summand 2) (hSummand 1) (hSummand 2)]
  simp only [Pi.add_apply]
  rw [programPT06DirectionalHorizontalDivergence_multiindexEuler_eq_zero
      (current 0) (hCurrent 0) 0 jet,
    programPT06DirectionalHorizontalDivergence_multiindexEuler_eq_zero
      (current 1) (hCurrent 1) 1 jet,
    programPT06DirectionalHorizontalDivergence_multiindexEuler_eq_zero
      (current 2) (hCurrent 2) 2 jet]
  simp

end
end P0EFTJanusProgramPT06FullHorizontalDivergenceMultiindexEuler4D
end JanusFormal
