import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

/-!
# T08: genuine spatial Euler expressions for value-only potentials

The existing second-order T06 Euler operator reduces to the ordinary
derivative for differentiable potentials of the value field. This is a
jet-level identity, not existence of a physical background or integrated
covariant action.
-/

namespace JanusFormal
namespace P0EFTJanusT08ValuePotentialEuler4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D

universe u
variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

def valueOnly (potential : Fiber → Real) (jet : ThroatSpatialMultiindexJet2 Fiber) : Real :=
  potential (jet programPT06SecondOrderZeroMultiIndex)

private def valueProjection : ThroatSpatialMultiindexJet2 Fiber →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex

theorem valueOnly_fderiv (potential : Fiber → Real) (hPotential : Differentiable Real potential)
    (jet : ThroatSpatialMultiindexJet2 Fiber) :
    fderiv Real (valueOnly potential) jet =
      (fderiv Real potential (jet programPT06SecondOrderZeroMultiIndex)).comp
        valueProjection := by
  exact ((hPotential _).hasFDerivAt.comp jet valueProjection.hasFDerivAt).fderiv

private theorem zero_ne_first (direction : Fin 3) :
    programPT06SecondOrderZeroMultiIndex ≠ programPT06SecondOrderFirstMultiIndex direction := by
  intro h
  have ho := congrArg (fun index : ThroatSpatialTruncatedIndex 2 =>
    throatSpatialMultiIndexOrder index.1) h
  simp [programPT06SecondOrderZeroMultiIndex, programPT06SecondOrderFirstMultiIndex] at ho

private theorem zero_ne_second (first second : Fin 3) :
    programPT06SecondOrderZeroMultiIndex ≠ programPT06SecondOrderSecondMultiIndex first second := by
  intro h
  have ho := congrArg (fun index : ThroatSpatialTruncatedIndex 2 =>
    throatSpatialMultiIndexOrder index.1) h
  simp [programPT06SecondOrderZeroMultiIndex, programPT06SecondOrderSecondMultiIndex,
    throatSpatialMultiIndexOrder_add] at ho

theorem valueOnly_vertical_one (potential : Fiber → Real)
    (hPotential : Differentiable Real potential) (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne (valueOnly potential) direction = 0 := by
  ext jet variation
  rw [programPT06SecondOrderLocalVerticalPartialOne_apply, valueOnly_fderiv potential hPotential]
  simp [valueProjection, zero_ne_first]

theorem valueOnly_vertical_two (potential : Fiber → Real)
    (hPotential : Differentiable Real potential) (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo (valueOnly potential) first second = 0 := by
  ext jet variation
  rw [programPT06SecondOrderLocalVerticalPartialTwo_apply, valueOnly_fderiv potential hPotential]
  simp [valueProjection, zero_ne_second]

/-- No first- or second-jet total terms survive for a value-only potential. -/
theorem valueOnly_euler (potential : Fiber → Real) (hPotential : Differentiable Real potential)
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderLocalEuler (valueOnly potential) jet =
      fderiv Real potential (jet ⟨0, by simp⟩) := by
  simp only [programPT06SecondOrderLocalEuler,
    programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06SecondOrderLocalEulerSecondTotalTerm,
    valueOnly_vertical_one potential hPotential, valueOnly_vertical_two potential hPotential,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_zero, Pi.zero_apply,
    Finset.sum_const_zero, smul_zero, sub_zero, add_zero]
  ext variation
  rw [programPT06SecondOrderLocalVerticalPartialZero_apply, valueOnly_fderiv potential hPotential]
  simp [valueProjection, truncateThroatSpatialMultiindexJet, programPT06SecondOrderZeroMultiIndex]

def centeredPower (coordinate : Fiber →L[Real] Real) (coupling reference : Real)
    (degree : Nat) (value : Fiber) : Real :=
  coupling * (coordinate value - reference) ^ degree

theorem centeredPower_hasFDerivAt (coordinate : Fiber →L[Real] Real)
    (coupling reference : Real) (degree : Nat) (value : Fiber) :
    HasFDerivAt (centeredPower coordinate coupling reference degree)
      ((coupling * degree * (coordinate value - reference) ^ (degree - 1)) • coordinate) value := by
  convert (((coordinate.hasFDerivAt.sub_const reference).pow degree).const_mul coupling) using 1 <;>
    ext variation <;> simp [centeredPower, mul_assoc]

theorem centeredPower_differentiable (coordinate : Fiber →L[Real] Real)
    (coupling reference : Real) (degree : Nat) :
    Differentiable Real (centeredPower coordinate coupling reference degree) :=
  fun value => (centeredPower_hasFDerivAt coordinate coupling reference degree value).differentiableAt

/-- The genuine T06 Euler operator sees nonlinear potential coefficients. -/
theorem centeredPower_euler (coordinate : Fiber →L[Real] Real)
    (coupling reference : Real) (degree : Nat) (jet : ThroatSpatialMultiindexJet4 Fiber)
    (variation : Fiber) :
    programPT06SecondOrderLocalEuler (valueOnly (centeredPower coordinate coupling reference degree))
      jet variation =
      coupling * degree * (coordinate (jet ⟨0, by simp⟩) - reference) ^ (degree - 1) *
        coordinate variation := by
  rw [valueOnly_euler _ (centeredPower_differentiable coordinate coupling reference degree),
    (centeredPower_hasFDerivAt coordinate coupling reference degree _).fderiv]
  rfl

end
end P0EFTJanusT08ValuePotentialEuler4D
end JanusFormal
