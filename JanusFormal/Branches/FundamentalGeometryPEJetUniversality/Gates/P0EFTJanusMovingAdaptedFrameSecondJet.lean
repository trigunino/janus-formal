import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothAdaptedFrame
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalFormJet

namespace JanusFormal
namespace P0EFTJanusMovingAdaptedFrameSecondJet

set_option autoImplicit false

noncomputable section

universe u v

open P0EFTJanusSecondFundamentalFormJet

variable {Tangent : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Tangent]
variable [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]

/-- First jet at a base point of a varying orthogonal ambient frame.

`value` is the orthogonal frame change at the point. `derivative x v` is the
first variation of that frame in source direction `x`, applied to an ambient
vector `v`. The algebraic second-jet calculation below only needs these two
coefficients. -/
@[ext]
structure MovingAmbientFrameOneJet
    (Tangent : Type u) (Ambient : Type v) where
  value : Ambient ≃ₗᵢ[ℝ] Ambient
  derivative : Tangent → Ambient → Ambient

/-- First derivative of the immersion expressed in the moving ambient frame. -/
def transformedDerivative
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    Tangent →ₗᵢ[ℝ] Ambient :=
  frame.value.toLinearIsometry.comp derivative

@[simp]
theorem transformedDerivative_apply
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (x : Tangent) :
    transformedDerivative frame derivative x =
      frame.value (derivative x) := by
  rfl

/-- Symmetric derivative-of-frame contribution in the second derivative of an
origin-based immersion:

`(dR·di)(x,y) = dR(x)(di(y)) + dR(y)(di(x))`.
-/
def frameDerivativeCorrection
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    Tangent → Tangent → Ambient :=
  fun x y =>
    frame.derivative x (derivative y) +
      frame.derivative y (derivative x)

/-- The moving-frame correction is symmetric without any additional assumption:
it is the symmetrized product-rule term. -/
theorem frameDerivativeCorrection_isSymmetric
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) :
    IsSymmetricTensor (frameDerivativeCorrection frame derivative) := by
  intro x y
  simp only [frameDerivativeCorrection]
  exact add_comm _ _

/-- Raw second derivative after an ambient moving-frame change at an immersion
base point whose position has been translated to the origin. The zeroth-order
`d²R · i` term vanishes at that origin. -/
def movingFrameRawSecond
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (rawSecond : Tangent → Tangent → Ambient) :
    Tangent → Tangent → Ambient :=
  fun x y =>
    frame.value (rawSecond x y) +
      frameDerivativeCorrection frame derivative x y

/-- Exact formal product-rule formula for the raw second coefficient in a moving
ambient frame. -/
theorem movingFrameRawSecond_formula
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (rawSecond : Tangent → Tangent → Ambient)
    (x y : Tangent) :
    movingFrameRawSecond frame derivative rawSecond x y =
      frame.value (rawSecond x y) +
        frame.derivative x (derivative y) +
        frame.derivative y (derivative x) := by
  simp only [movingFrameRawSecond, frameDerivativeCorrection]
  abel

/-- Paired transformation of a connection-corrected immersion two-jet.

The derivative-of-frame contribution is added to the raw Hessian and subtracted
from the ambient connection coefficient. This is the moving-frame version of the
ambient coordinate cancellation formalized in the preceding pointwise gate. -/
def movingAmbientFrameChange
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    ConnectionCorrectedSecondJet Tangent Ambient where
  rawSecond := movingFrameRawSecond frame derivative jet.rawSecond
  ambientConnection x y :=
    frame.value (jet.ambientConnection x y) -
      frameDerivativeCorrection frame derivative x y
  sourceConnection := jet.sourceConnection

@[simp]
theorem movingAmbientFrameChange_rawSecond
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    (movingAmbientFrameChange frame derivative jet).rawSecond =
      movingFrameRawSecond frame derivative jet.rawSecond := by
  rfl

@[simp]
theorem movingAmbientFrameChange_ambientConnection
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    (movingAmbientFrameChange frame derivative jet).ambientConnection =
      fun x y => frame.value (jet.ambientConnection x y) -
        frameDerivativeCorrection frame derivative x y := by
  rfl

/-- Main S5.3 cancellation theorem: the connection-corrected second derivative
in the moving frame is exactly the orthogonal transform of the original
covariant second derivative. All first derivatives of the frame cancel. -/
theorem covariantSecondDerivative_movingAmbientFrameChange
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    covariantSecondDerivative (transformedDerivative frame derivative)
        (movingAmbientFrameChange frame derivative jet) =
      fun x y => frame.value
        (covariantSecondDerivative derivative jet x y) := by
  funext x y
  change
    (frame.value (jet.rawSecond x y) +
        frameDerivativeCorrection frame derivative x y) +
      (frame.value (jet.ambientConnection x y) -
        frameDerivativeCorrection frame derivative x y) -
      frame.value (derivative (jet.sourceConnection x y)) =
    frame.value
      (jet.rawSecond x y + jet.ambientConnection x y -
        derivative (jet.sourceConnection x y))
  rw [frame.value.map_sub, frame.value.map_add]
  abel

/-- Combined source-coordinate and moving-ambient-frame transformation. The
source two-jet correction and derivative-of-frame correction are both visible in
the transformed raw Hessian, while the corresponding source and ambient
connection coefficients absorb them. -/
def movingAdaptedFrameChange
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (sourceChange : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    ConnectionCorrectedSecondJet Tangent Ambient :=
  movingAmbientFrameChange frame derivative
    (sourceCoordinateChange derivative sourceChange jet)

/-- Raw second derivative under the combined moving adapted-frame change. -/
theorem movingAdaptedFrameChange_rawSecond_formula
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (sourceChange : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient)
    (x y : Tangent) :
    (movingAdaptedFrameChange frame derivative sourceChange jet).rawSecond x y =
      frame.value
          (jet.rawSecond x y + derivative (sourceChange x y)) +
        frame.derivative x (derivative y) +
        frame.derivative y (derivative x) := by
  simp only [movingAdaptedFrameChange, movingAmbientFrameChange,
    movingFrameRawSecond, sourceCoordinateChange, frameDerivativeCorrection]
  abel

/-- The complete source-plus-moving-frame two-jet law. The corrected second
derivative transforms tensorially by the zeroth-order orthogonal frame value. -/
theorem covariantSecondDerivative_movingAdaptedFrameChange
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (sourceChange : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient) :
    covariantSecondDerivative (transformedDerivative frame derivative)
        (movingAdaptedFrameChange frame derivative sourceChange jet) =
      fun x y => frame.value
        (covariantSecondDerivative derivative jet x y) := by
  rw [movingAdaptedFrameChange,
    covariantSecondDerivative_movingAmbientFrameChange,
    covariantSecondDerivative_sourceCoordinateChange]

/-- If the raw Hessian and connection data are symmetric, the transformed
covariant second derivative remains symmetric. -/
theorem movingAdaptedFrameChange_preserves_covariant_symmetry
    (frame : MovingAmbientFrameOneJet Tangent Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (sourceChange : Tangent → Tangent → Tangent)
    (jet : ConnectionCorrectedSecondJet Tangent Ambient)
    (hRaw : IsSymmetricTensor jet.rawSecond)
    (hAmbient : IsSymmetricTensor jet.ambientConnection)
    (hSource : IsSymmetricTensor jet.sourceConnection) :
    IsSymmetricTensor
      (covariantSecondDerivative (transformedDerivative frame derivative)
        (movingAdaptedFrameChange frame derivative sourceChange jet)) := by
  rw [covariantSecondDerivative_movingAdaptedFrameChange]
  intro x y
  exact congrArg frame.value
    (covariantSecondDerivative_isSymmetric derivative jet
      hRaw hAmbient hSource x y)

/-- Exact boundary after the formal S5.3 moving-frame calculation. -/
structure MovingAdaptedFrameSecondJetStatus where
  movingAmbientFrameOneJetDefined : Prop
  productRuleCorrectionDefined : Prop
  correctionSymmetryProved : Prop
  rawSecondTransformationFormulaProved : Prop
  ambientConnectionCompensationProved : Prop
  combinedSourceFrameLawProved : Prop
  covariantSecondDerivativeTensorialityProved : Prop
  frameJetExtractedFromSmoothAdaptedFrame : Prop
  normalProjectionTransportedBetweenMovingNormalSpaces : Prop
  secondFundamentalFormMovingFrameEquivarianceProved : Prop
  manifoldConnectionTransformationDerived : Prop
  spinCFrameJetLiftConstructed : Prop

/-- Closure of the full geometric S5.3 stage. -/
def movingAdaptedFrameSecondJetClosed
    (s : MovingAdaptedFrameSecondJetStatus) : Prop :=
  s.movingAmbientFrameOneJetDefined /\
  s.productRuleCorrectionDefined /\
  s.correctionSymmetryProved /\
  s.rawSecondTransformationFormulaProved /\
  s.ambientConnectionCompensationProved /\
  s.combinedSourceFrameLawProved /\
  s.covariantSecondDerivativeTensorialityProved /\
  s.frameJetExtractedFromSmoothAdaptedFrame /\
  s.normalProjectionTransportedBetweenMovingNormalSpaces /\
  s.secondFundamentalFormMovingFrameEquivarianceProved /\
  s.manifoldConnectionTransformationDerived /\
  s.spinCFrameJetLiftConstructed

/-- The formal two-jet cancellation law does not itself extract the frame jet
from the smooth Gram--Schmidt construction. -/
theorem missing_frame_jet_extraction_blocks_full_S5_3
    (s : MovingAdaptedFrameSecondJetStatus)
    (hMissing : Not s.frameJetExtractedFromSmoothAdaptedFrame) :
    Not (movingAdaptedFrameSecondJetClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusMovingAdaptedFrameSecondJet
end JanusFormal
