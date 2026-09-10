import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D

/-!
# Commutation of fixed-ambient total derivatives

The derivative of a local function along a truncated jet shift has the
expected Hessian term and the derivative of the linear shift.  Symmetry of
the Hessian and commutation of the truncated shifts then show that any two
fixed-ambient total derivatives commute.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientTotalDerivativeCommutation4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Frechet derivative of a local function differentiated along one linear
truncated jet shift. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_fderiv_apply
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet variation : SpatialJet Fiber order) :
    fderiv Real
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet variation =
      fderiv Real localFunction jet
          (programPT06TruncatedJetShiftContinuousLinearMap
            (Fiber := Fiber) order direction variation) +
        fderiv Real (fderiv Real localFunction) jet variation
          (programPT06TruncatedJetShiftContinuousLinearMap
            (Fiber := Fiber) order direction jet) := by
  let shift := programPT06TruncatedJetShiftContinuousLinearMap
    (Fiber := Fiber) order direction
  have hGradientContDiff : ContDiff Real 1
      (fderiv Real localFunction) :=
    hLocalFunction.fderiv_right (m := 1) (by norm_num)
  have hGradient : DifferentiableAt Real
      (fderiv Real localFunction) jet :=
    hGradientContDiff.differentiable (by norm_num) jet
  have hDerivative := fderiv_clm_apply hGradient
    shift.differentiableAt
  have hApplied := congrArg
    (fun derivative : SpatialJet Fiber order →L[Real] Target ↦
      derivative variation) hDerivative
  change fderiv Real
      (fun y => fderiv Real localFunction y (shift y)) jet variation = _
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.fderiv] using hApplied

/-- Fixed-ambient total derivatives in two spatial directions commute for a
twice continuously differentiable local function. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_comm
    (order : Nat) (first second : Fin 3)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real 2 localFunction) :
    programPT06AmbientLocalFunctionTotalDerivative order first
        (programPT06AmbientLocalFunctionTotalDerivative
          order second localFunction) =
      programPT06AmbientLocalFunctionTotalDerivative order second
        (programPT06AmbientLocalFunctionTotalDerivative
          order first localFunction) := by
  funext jet
  let firstShift := programPT06TruncatedJetShiftContinuousLinearMap
    (Fiber := Fiber) order first
  let secondShift := programPT06TruncatedJetShiftContinuousLinearMap
    (Fiber := Fiber) order second
  have hHessian :
      fderiv Real (fderiv Real localFunction) jet
          (firstShift jet) (secondShift jet) =
        fderiv Real (fderiv Real localFunction) jet
          (secondShift jet) (firstShift jet) :=
    (hLocalFunction.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
      (firstShift jet) (secondShift jet)
  have hShiftComm : firstShift (secondShift jet) =
      secondShift (firstShift jet) := by
    have hMaps := programPT06TruncatedJetShiftContinuousLinearMap_comm
      (Fiber := Fiber) order first second
    have hAtJet := congrArg
      (fun shift : SpatialJet Fiber order →L[Real] SpatialJet Fiber order ↦
        shift jet) hMaps
    simpa only [firstShift, secondShift,
      ContinuousLinearMap.comp_apply] using hAtJet
  change fderiv Real
      (programPT06AmbientLocalFunctionTotalDerivative
        order second localFunction) jet (firstShift jet) =
    fderiv Real
      (programPT06AmbientLocalFunctionTotalDerivative
        order first localFunction) jet (secondShift jet)
  rw [programPT06AmbientLocalFunctionTotalDerivative_fderiv_apply
      order second localFunction hLocalFunction jet (firstShift jet),
    programPT06AmbientLocalFunctionTotalDerivative_fderiv_apply
      order first localFunction hLocalFunction jet (secondShift jet),
    hShiftComm, hHessian]

end
end P0EFTJanusProgramPT06AmbientTotalDerivativeCommutation4D
end JanusFormal
