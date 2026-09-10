import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientTotalDerivativeCommutation4D

/-!
# Vertical derivative of a fixed-ambient total derivative

The vertical derivative of one fixed-ambient total derivative splits into a
Hessian term and the derivative along the shifted coordinate injection.
Symmetry of the Hessian identifies the first term with the total derivative
of the corresponding vertical partial.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeIdentity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06AmbientTotalDerivativeCommutation4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Evaluated product-rule formula for the vertical derivative of one
fixed-ambient total derivative. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_verticalPartial_apply
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) (variation : Fiber) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index variation =
      fderiv Real (fderiv Real localFunction) jet
          (programPT06ThroatSpatialJetCoordinateInjection index variation)
          (programPT06TruncatedJetShiftContinuousLinearMap
            (Fiber := Fiber) order direction jet) +
        fderiv Real localFunction jet
          (programPT06TruncatedJetShiftContinuousLinearMap
            (Fiber := Fiber) order direction
            (programPT06ThroatSpatialJetCoordinateInjection
              index variation)) := by
  rw [programPT06ThroatSpatialVerticalPartialDerivative_apply,
    programPT06AmbientLocalFunctionTotalDerivative_fderiv_apply
      order direction localFunction hLocalFunction jet
      (programPT06ThroatSpatialJetCoordinateInjection index variation)]
  ac_rfl

/-- The derivative of a vertical partial is the Hessian restricted to its
fixed coordinate injection. -/
theorem programPT06ThroatSpatialVerticalPartialDerivative_fderiv_apply
    (order : Nat) (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet tangent : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) (variation : Fiber) :
    fderiv Real
        (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
          localFunction y index) jet tangent variation =
      fderiv Real (fderiv Real localFunction) jet tangent
        (programPT06ThroatSpatialJetCoordinateInjection index variation) := by
  let injection :=
    programPT06ThroatSpatialJetCoordinateInjection
      (Fiber := Fiber) index
  let restrictGradient :
      (SpatialJet Fiber order →L[Real] Real) →L[Real]
        (Fiber →L[Real] Real) :=
    (ContinuousLinearMap.compL Real Fiber (SpatialJet Fiber order) Real).flip
      injection
  have hGradient : DifferentiableAt Real
      (fderiv Real localFunction) jet :=
    (hLocalFunction.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) jet
  have hDerivative : HasFDerivAt
      (fun y ↦ restrictGradient (fderiv Real localFunction y))
      (restrictGradient.comp
        (fderiv Real (fderiv Real localFunction) jet)) jet :=
    restrictGradient.hasFDerivAt.comp jet hGradient.hasFDerivAt
  have hApplied := congrArg
    (fun derivative : SpatialJet Fiber order →L[Real]
        (Fiber →L[Real] Real) ↦ derivative tangent variation)
    hDerivative.fderiv
  change fderiv Real
      (fun y ↦ (fderiv Real localFunction y).comp injection)
      jet tangent variation = _
  simpa only [restrictGradient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    injection] using hApplied

/-- Evaluating the total derivative of a vertical partial gives the Hessian
with the ambient shift in its first slot. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_verticalPartialField_apply
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) (variation : Fiber) :
    programPT06AmbientLocalFunctionTotalDerivative order direction
        (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
          localFunction y index) jet variation =
      fderiv Real (fderiv Real localFunction) jet
        (programPT06TruncatedJetShiftContinuousLinearMap
          (Fiber := Fiber) order direction jet)
        (programPT06ThroatSpatialJetCoordinateInjection index variation) := by
  exact programPT06ThroatSpatialVerticalPartialDerivative_fderiv_apply
    order localFunction hLocalFunction jet
    (programPT06TruncatedJetShiftContinuousLinearMap
      (Fiber := Fiber) order direction jet) index variation

/-- Pointwise Cartan identity: vertical differentiation and one ambient total
derivative commute up to the shifted coordinate-injection term. -/
theorem programPT06AmbientVerticalTotalDerivativeIdentity_apply
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) (variation : Fiber) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index variation =
      programPT06AmbientLocalFunctionTotalDerivative order direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localFunction y index) jet variation +
        fderiv Real localFunction jet
          (programPT06TruncatedJetShiftContinuousLinearMap
            (Fiber := Fiber) order direction
            (programPT06ThroatSpatialJetCoordinateInjection
              index variation)) := by
  rw [programPT06AmbientLocalFunctionTotalDerivative_verticalPartial_apply
      order direction localFunction hLocalFunction jet index variation,
    programPT06AmbientLocalFunctionTotalDerivative_verticalPartialField_apply
      order direction localFunction hLocalFunction jet index variation]
  rw [(hLocalFunction.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
    (programPT06ThroatSpatialJetCoordinateInjection index variation)
    (programPT06TruncatedJetShiftContinuousLinearMap
      (Fiber := Fiber) order direction jet)]

/-- Continuous-linear-map form of the ambient vertical Cartan identity. -/
theorem programPT06AmbientVerticalTotalDerivativeIdentity
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index =
      programPT06AmbientLocalFunctionTotalDerivative order direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localFunction y index) jet +
        (fderiv Real localFunction jet).comp
          ((programPT06TruncatedJetShiftContinuousLinearMap
            (Fiber := Fiber) order direction).comp
            (programPT06ThroatSpatialJetCoordinateInjection index)) := by
  apply ContinuousLinearMap.ext
  intro variation
  simpa only [add_apply, ContinuousLinearMap.comp_apply] using
    programPT06AmbientVerticalTotalDerivativeIdentity_apply
      order direction localFunction hLocalFunction jet index variation

end
end P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeIdentity4D
end JanusFormal
