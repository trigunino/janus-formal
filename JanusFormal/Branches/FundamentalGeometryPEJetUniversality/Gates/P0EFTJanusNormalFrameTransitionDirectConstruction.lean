import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameTransitionJetBridge

namespace JanusFormal
namespace P0EFTJanusNormalFrameTransitionDirectConstruction

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusNormalFrameSmoothTransition
open P0EFTJanusMetricNormalConnectionCurvature
open P0EFTJanusSmoothNormalFrameJetExtraction
open P0EFTJanusNormalFrameConnectionGaugeLaw
open P0EFTJanusNormalConnectionCurvatureGaugeLaw
open P0EFTJanusSmoothOrthogonalGaugeJetExtraction
open P0EFTJanusNormalFrameTransitionJetBridge

universe u v w

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

/-- The adjoint of one frame value, viewed as an operator-valued field. -/
def adjointFrameValue
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Ambient →L[ℝ] Normal :=
  ContinuousLinearMap.adjoint (frame.field base)

/-- First derivative of the adjoint frame field. Since the real Hilbert adjoint
is continuous linear on operator spaces, this is obtained by postcomposition
with the stored first derivative of the frame. -/
def adjointFrameFirst
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Tangent →L[ℝ] Ambient →L[ℝ] Normal :=
  (realAdjointContinuousLinearMap
    (Normal := Normal) (Ambient := Ambient)).comp (frame.first base)

/-- Fixed continuous linear operation applying the Hilbert adjoint pointwise to
an operator-valued tangent one-form. -/
def adjointOnFrameDerivatives :
    (Tangent →L[ℝ] Normal →L[ℝ] Ambient) →L[ℝ]
      Tangent →L[ℝ] Ambient →L[ℝ] Normal :=
  compL ℝ Tangent
    (Normal →L[ℝ] Ambient) (Ambient →L[ℝ] Normal)
    (realAdjointContinuousLinearMap
      (Normal := Normal) (Ambient := Ambient))

/-- Second derivative of the adjoint frame field, bundled as a nested continuous
linear map. -/
def adjointFrameSecond
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    Tangent →L[ℝ] Tangent →L[ℝ] Ambient →L[ℝ] Normal :=
  (adjointOnFrameDerivatives
    (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)).comp
      (frame.second base)

/-- Composition of an ambient-to-normal operator with a normal-to-ambient
operator. This is the bilinear operation underlying `e₁† e₂`. -/
def normalFrameComposition :
    (Ambient →L[ℝ] Normal) →L[ℝ]
      (Normal →L[ℝ] Ambient) →L[ℝ] Normal →L[ℝ] Normal :=
  compL ℝ Normal Ambient Normal

/-- Canonical transition field written entirely as the adjoint composition
`e₁† e₂`. -/
def canonicalTransitionField
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Normal →L[ℝ] Normal :=
  (adjointFrameValue first base).comp (second.field base)

/-- First derivative produced by the exact Fréchet product rule for composition
of continuous linear maps. -/
def canonicalTransitionFirst
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Tangent →L[ℝ] Normal →L[ℝ] Normal :=
  ((normalFrameComposition (Normal := Normal) (Ambient := Ambient))
      (adjointFrameValue first base)).comp (second.first base) +
    ((normalFrameComposition (Normal := Normal) (Ambient := Ambient)).flip
      (second.field base)).comp (adjointFrameFirst first base)

/-- Derivative of the `e₁† · de₂` contribution to the first transition jet. -/
def canonicalTransitionSecondRight
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    Tangent →L[ℝ] Tangent →L[ℝ] Normal →L[ℝ] Normal :=
  (compL ℝ Tangent
      (Normal →L[ℝ] Ambient) (Normal →L[ℝ] Normal)
      ((normalFrameComposition (Normal := Normal) (Ambient := Ambient))
        (adjointFrameValue first base))).comp (second.second base) +
    ((compL ℝ Tangent
      (Normal →L[ℝ] Ambient) (Normal →L[ℝ] Normal)).flip
      (second.first base)).comp
        ((normalFrameComposition (Normal := Normal) (Ambient := Ambient)).comp
          (adjointFrameFirst first base))

/-- Derivative of the `(de₁)† · e₂` contribution to the first transition jet. -/
def canonicalTransitionSecondLeft
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    Tangent →L[ℝ] Tangent →L[ℝ] Normal →L[ℝ] Normal :=
  (compL ℝ Tangent
      (Ambient →L[ℝ] Normal) (Normal →L[ℝ] Normal)
      ((normalFrameComposition (Normal := Normal) (Ambient := Ambient)).flip
        (second.field base))).comp (adjointFrameSecond first base) +
    ((compL ℝ Tangent
      (Ambient →L[ℝ] Normal) (Normal →L[ℝ] Normal)).flip
      (adjointFrameFirst first base)).comp
        ((normalFrameComposition
          (Normal := Normal) (Ambient := Ambient)).flip.comp
          (second.first base))

/-- Full second derivative of the canonical transition. -/
def canonicalTransitionSecond
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    Tangent →L[ℝ] Tangent →L[ℝ] Normal →L[ℝ] Normal :=
  canonicalTransitionSecondRight first second base +
    canonicalTransitionSecondLeft first second base

/-- The adjoint frame field has the derivative obtained by applying the
continuous-linear adjoint operation to the frame derivative. -/
theorem adjointFrameValue_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (adjointFrameValue frame)
      (adjointFrameFirst frame base) base := by
  have h :=
    (realAdjointContinuousLinearMap
      (Normal := Normal) (Ambient := Ambient)).hasFDerivAt
      (x := frame.field base) |>.comp base (frame.field_hasFDerivAt base)
  convert h using 1
  · funext point
    rfl
  · rfl

/-- The first adjoint-frame derivative itself has the expected second
Fréchet derivative. -/
theorem adjointFrameFirst_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (adjointFrameFirst frame)
      (adjointFrameSecond frame base) base := by
  let postAdjoint := adjointOnFrameDerivatives
    (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
  have h := postAdjoint.hasFDerivAt
    (x := frame.first base) |>.comp base (frame.first_hasFDerivAt base)
  convert h using 1
  · funext point
    rfl
  · rfl

/-- First differentiation of `e₁†e₂`, with no derivative witness supplied by the
caller. -/
theorem canonicalTransitionField_hasFDerivAt
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (canonicalTransitionField first second)
      (canonicalTransitionFirst first second base) base := by
  have h := (adjointFrameValue_hasFDerivAt first base).clm_comp
    (second.field_hasFDerivAt base)
  convert h using 1
  · funext point
    rfl
  · rfl

/-- Second differentiation of `e₁†e₂`, obtained by applying the continuous
linear-map product rule to the two summands of its first derivative. -/
theorem canonicalTransitionFirst_hasFDerivAt
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (canonicalTransitionFirst first second)
      (canonicalTransitionSecond first second base) base := by
  let composition := normalFrameComposition
    (Normal := Normal) (Ambient := Ambient)
  have hRightHead : HasFDerivAt
      (fun point => composition (adjointFrameValue first point))
      (composition.comp (adjointFrameFirst first base)) base := by
    exact (composition.hasFDerivAt
      (x := adjointFrameValue first base)).comp base
        (adjointFrameValue_hasFDerivAt first base)
  have hRight := hRightHead.clm_comp (second.first_hasFDerivAt base)
  have hLeftHead : HasFDerivAt
      (fun point => composition.flip (second.field point))
      (composition.flip.comp (second.first base)) base := by
    exact (composition.flip.hasFDerivAt
      (x := second.field base)).comp base
        (second.field_hasFDerivAt base)
  have hLeft := hLeftHead.clm_comp
    (adjointFrameFirst_hasFDerivAt first base)
  have h := hRight.add hLeft
  convert h using 1
  · funext point
    rfl
  · rfl

/-- The bundled first derivative agrees with the explicit differentiated-adjoint
formula used by the existing bridge module. -/
theorem canonicalTransitionFirst_apply
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base x : Tangent) :
    canonicalTransitionFirst first second base x =
      adjointTransitionFirstFormula first second base x := by
  change
    (ContinuousLinearMap.adjoint (first.field base)).comp
        (second.first base x) +
      (ContinuousLinearMap.adjoint (first.first base x)).comp
        (second.field base) =
    (ContinuousLinearMap.adjoint (first.first base x)).comp
        (second.field base) +
      (ContinuousLinearMap.adjoint (first.field base)).comp
        (second.first base x)
  exact add_comm _ _

/-- The bundled second derivative agrees with the four-term Hessian formula in
the bridge module. -/
theorem canonicalTransitionSecond_apply
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base x y : Tangent) :
    canonicalTransitionSecond first second base x y =
      adjointTransitionSecondFormula first second base x y := by
  apply ContinuousLinearMap.ext
  intro normal
  change
    (ContinuousLinearMap.adjoint (first.field base))
        (second.second base x y normal) +
      ((ContinuousLinearMap.adjoint (first.first base x))
          (second.first base y normal) +
        ((ContinuousLinearMap.adjoint (first.second base x y))
            (second.field base normal) +
          (ContinuousLinearMap.adjoint (first.first base y))
            (second.first base x normal))) =
    (ContinuousLinearMap.adjoint (first.second base x y))
        (second.field base normal) +
      ((ContinuousLinearMap.adjoint (first.first base y))
          (second.first base x normal) +
        ((ContinuousLinearMap.adjoint (first.first base x))
            (second.first base y normal) +
          (ContinuousLinearMap.adjoint (first.field base))
            (second.second base x y normal)))
  abel

/-- The second transition derivative is symmetric because it is the genuine
second Fréchet derivative of the canonical transition field. -/
theorem canonicalTransitionSecond_symmetric
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base x y : Tangent) :
    canonicalTransitionSecond first second base x y =
      canonicalTransitionSecond first second base y x :=
  second_derivative_symmetric
    (fun point => canonicalTransitionField_hasFDerivAt first second point)
    (canonicalTransitionFirst_hasFDerivAt first second base) x y

/-- The operator field `e₁†e₂` is definitionally the adjoint transition of the
pointwise linear-isometry values. -/
theorem canonicalTransitionField_eq_adjointTransition
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    canonicalTransitionField first second base =
      normalFrameAdjointTransition
        (frameValueAt first base) (frameValueAt second base) := by
  rfl

/-- Under equality of the two ambient normal subspaces, the directly
differentiated field is the canonical orthogonal transition. -/
theorem canonicalTransitionField_eq_canonical
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base))
    (base : Tangent) :
    canonicalTransitionField first second base =
      (normalFrameTransition
        (frameValueAt first base) (frameValueAt second base)
        (hRange base)).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [canonicalTransitionField_eq_adjointTransition]
  exact normalFrameAdjointTransition_eq_canonical
    (frameValueAt first base) (frameValueAt second base) (hRange base)

/-- Direct construction of the orthogonal transition gauge two-jet from the two
frame fields and their stored Fréchet derivatives. No independent value, first-
derivative or second-derivative witnesses are required. -/
def canonicalNormalFrameGaugeTwoJet
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base)) :
    SmoothOrthogonalGaugeTwoJetField Tangent Normal where
  field := canonicalTransitionField first second
  first := canonicalTransitionFirst first second
  second := canonicalTransitionSecond first second
  field_hasFDerivAt := canonicalTransitionField_hasFDerivAt first second
  first_hasFDerivAt := canonicalTransitionFirst_hasFDerivAt first second
  orthonormal := by
    intro base firstNormal secondNormal
    rw [canonicalTransitionField_eq_canonical first second hRange base]
    simpa using
      (normalFrameTransition
        (frameValueAt first base) (frameValueAt second base)
        (hRange base)).inner_map_map firstNormal secondNormal
  inverse := fun base =>
    ((normalFrameTransition
      (frameValueAt first base) (frameValueAt second base)
      (hRange base)).symm).toContinuousLinearEquiv.toContinuousLinearMap
  inverse_value := by
    intro base normal
    rw [canonicalTransitionField_eq_canonical first second hRange base]
    exact (normalFrameTransition
      (frameValueAt first base) (frameValueAt second base)
      (hRange base)).symm_apply_apply normal
  value_inverse := by
    intro base normal
    rw [canonicalTransitionField_eq_canonical first second hRange base]
    exact (normalFrameTransition
      (frameValueAt first base) (frameValueAt second base)
      (hRange base)).apply_symm_apply normal
  second_symmetric := canonicalTransitionSecond_symmetric first second

/-- The exact bridge demanded by the previous module is now constructed directly
from the two frame fields. -/
def canonicalNormalFrameTransitionTwoJetOfFrames
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base)) :
    CanonicalNormalFrameTransitionTwoJet Tangent Normal Ambient where
  firstFrame := first
  secondFrame := second
  sameRange := hRange
  gauge := canonicalNormalFrameGaugeTwoJet first second hRange
  field_eq := by
    intro base
    exact canonicalTransitionField_eq_adjointTransition first second base
  first_eq := canonicalTransitionFirst_apply first second
  second_eq := canonicalTransitionSecond_apply first second

/-- Canonical Maurer--Cartan two-jet attached directly to two smooth normal-frame
two-jets. -/
def canonicalFrameTransitionMaurerCartanTwoJetAt
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base))
    (base : Tangent) :
    OrthogonalGaugeMaurerCartanTwoJet Tangent Normal :=
  bridgeMaurerCartanTwoJetAt
    (canonicalNormalFrameTransitionTwoJetOfFrames first second hRange) base

/-- Curvature covariance on a normal-frame overlap now follows with no
independent gauge-jet witness. -/
theorem canonicalFrameTransition_curvature_covariance
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base))
    (base : Tangent)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    gaugeTransformedCurvatureEndomorphism
        (canonicalFrameTransitionMaurerCartanTwoJetAt
          first second hRange base) jet x y =
      orthogonalConjugate
        (normalFrameTransition
          (frameValueAt first base) (frameValueAt second base)
          (hRange base))
        (normalConnectionCurvatureEndomorphism jet x y) :=
  canonicalTransition_curvature_covariance
    (canonicalNormalFrameTransitionTwoJetOfFrames first second hRange)
    base jet x y

/-- The former final status atom is constructively realized in the fixed ambient
Hilbert model. -/
theorem direct_frame_frechet_construction_exists
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base)) :
    Nonempty (CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient) :=
  ⟨canonicalNormalFrameTransitionTwoJetOfFrames first second hRange⟩

/-- Remaining boundary after direct construction: the normal-frame fields must
still be obtained from the actual manifold bundle trivializations, and ordinary
Fréchet derivatives must be replaced by ambient covariant derivatives. -/
structure NormalFrameTransitionDirectConstructionStatus where
  adjointFrameFirstDerivativeProved : Prop
  adjointFrameSecondDerivativeProved : Prop
  transitionFirstDerivativeProved : Prop
  transitionSecondDerivativeProved : Prop
  transitionHessianSymmetryProved : Prop
  orthogonalGaugeTwoJetConstructed : Prop
  bridgeConstructedDirectlyFromFrameFrechetData : Prop
  maurerCartanJetConstructedWithoutWitnesses : Prop
  curvatureCovarianceConstructedWithoutWitnesses : Prop
  actualBundleOverlapFramesInserted : Prop
  ambientCovariantDerivativesInserted : Prop

/-- Closure of the geometric overlap-gauge construction. -/
def normalFrameTransitionDirectConstructionClosed
    (s : NormalFrameTransitionDirectConstructionStatus) : Prop :=
  s.adjointFrameFirstDerivativeProved ∧
  s.adjointFrameSecondDerivativeProved ∧
  s.transitionFirstDerivativeProved ∧
  s.transitionSecondDerivativeProved ∧
  s.transitionHessianSymmetryProved ∧
  s.orthogonalGaugeTwoJetConstructed ∧
  s.bridgeConstructedDirectlyFromFrameFrechetData ∧
  s.maurerCartanJetConstructedWithoutWitnesses ∧
  s.curvatureCovarianceConstructedWithoutWitnesses ∧
  s.actualBundleOverlapFramesInserted ∧
  s.ambientCovariantDerivativesInserted

/-- Flat fixed-model overlap data still do not substitute for actual bundle
trivializations and ambient covariant derivatives. -/
theorem missing_bundle_overlap_blocks_geometric_descent
    (s : NormalFrameTransitionDirectConstructionStatus)
    (hMissing : Not s.actualBundleOverlapFramesInserted) :
    Not (normalFrameTransitionDirectConstructionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusNormalFrameTransitionDirectConstruction
end JanusFormal
