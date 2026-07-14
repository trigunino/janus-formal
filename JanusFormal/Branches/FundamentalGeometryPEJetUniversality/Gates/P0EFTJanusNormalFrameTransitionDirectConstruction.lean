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

/-- The adjoint of one frame value, viewed through the fixed continuous-linear
adjoint map on real operator spaces. -/
def adjointFrameValue
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Ambient →L[ℝ] Normal :=
  realAdjointContinuousLinearMap
    (Normal := Normal) (Ambient := Ambient) (frame.field base)

/-- First derivative of the adjoint frame field. -/
def adjointFrameFirst
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Tangent →L[ℝ] Ambient →L[ℝ] Normal :=
  (realAdjointContinuousLinearMap
    (Normal := Normal) (Ambient := Ambient)).comp (frame.first base)

/-- Apply the real Hilbert adjoint pointwise to an operator-valued tangent
one-form. -/
def adjointOnFrameDerivatives :
    (Tangent →L[ℝ] Normal →L[ℝ] Ambient) →L[ℝ]
      Tangent →L[ℝ] Ambient →L[ℝ] Normal :=
  compL ℝ Tangent
    (Normal →L[ℝ] Ambient) (Ambient →L[ℝ] Normal)
    (realAdjointContinuousLinearMap
      (Normal := Normal) (Ambient := Ambient))

/-- Second derivative of the adjoint frame field. -/
def adjointFrameSecond
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    Tangent →L[ℝ] Tangent →L[ℝ] Ambient →L[ℝ] Normal :=
  (adjointOnFrameDerivatives
    (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)).comp
      (frame.second base)

/-- Composition of an ambient-to-normal operator with a normal-to-ambient
operator. -/
def normalFrameComposition :
    (Ambient →L[ℝ] Normal) →L[ℝ]
      (Normal →L[ℝ] Ambient) →L[ℝ] Normal →L[ℝ] Normal :=
  compL ℝ Normal Ambient Normal

/-- Canonical transition field `g=e₁†e₂`. -/
def canonicalTransitionField
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Normal →L[ℝ] Normal :=
  normalFrameComposition (Normal := Normal) (Ambient := Ambient)
    (adjointFrameValue first base) (second.field base)

/-- First derivative of `g=e₁†e₂`. -/
def canonicalTransitionFirst
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) : Tangent →L[ℝ] Normal →L[ℝ] Normal :=
  ((normalFrameComposition (Normal := Normal) (Ambient := Ambient))
      (adjointFrameValue first base)).comp (second.first base) +
    ((normalFrameComposition (Normal := Normal) (Ambient := Ambient)).flip
      (second.field base)).comp (adjointFrameFirst first base)

/-- Derivative of the `e₁†·de₂` contribution. -/
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

/-- Derivative of the `(de₁)†·e₂` contribution. -/
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

/-- The adjoint frame field has the pointwise-adjoint derivative. -/
theorem adjointFrameValue_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (adjointFrameValue frame)
      (adjointFrameFirst frame base) base := by
  let adjointMap := realAdjointContinuousLinearMap
    (Normal := Normal) (Ambient := Ambient)
  have hOuter : HasFDerivAt
      (fun operator : Normal →L[ℝ] Ambient => adjointMap operator)
      adjointMap (frame.field base) :=
    adjointMap.hasFDerivAt
  change HasFDerivAt
    (fun point => adjointMap (frame.field point))
    (adjointMap.comp (frame.first base)) base
  exact hOuter.comp base (frame.field_hasFDerivAt base)

/-- The first adjoint derivative has the adjointed second frame derivative. -/
theorem adjointFrameFirst_hasFDerivAt
    (frame : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (adjointFrameFirst frame)
      (adjointFrameSecond frame base) base := by
  let postAdjoint := adjointOnFrameDerivatives
    (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
  have hOuter : HasFDerivAt
      (fun derivative : Tangent →L[ℝ] Normal →L[ℝ] Ambient =>
        postAdjoint derivative)
      postAdjoint (frame.first base) :=
    postAdjoint.hasFDerivAt
  change HasFDerivAt
    (fun point => postAdjoint (frame.first point))
    (postAdjoint.comp (frame.second base)) base
  exact hOuter.comp base (frame.first_hasFDerivAt base)

/-- First product-rule differentiation of `e₁†e₂`. -/
theorem canonicalTransitionField_hasFDerivAt
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (canonicalTransitionField first second)
      (canonicalTransitionFirst first second base) base := by
  change HasFDerivAt
    (fun point =>
      (adjointFrameValue first point).comp (second.field point))
    (canonicalTransitionFirst first second base) base
  simpa only [canonicalTransitionFirst, normalFrameComposition] using
    (adjointFrameValue_hasFDerivAt first base).clm_comp
      (second.field_hasFDerivAt base)

/-- Second product-rule differentiation of `e₁†e₂`. -/
theorem canonicalTransitionFirst_hasFDerivAt
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    HasFDerivAt (canonicalTransitionFirst first second)
      (canonicalTransitionSecond first second base) base := by
  let composition := normalFrameComposition
    (Normal := Normal) (Ambient := Ambient)
  have hComposition : HasFDerivAt
      (fun operator : Ambient →L[ℝ] Normal => composition operator)
      composition (adjointFrameValue first base) :=
    composition.hasFDerivAt
  have hRightHead : HasFDerivAt
      (fun point => composition (adjointFrameValue first point))
      (composition.comp (adjointFrameFirst first base)) base :=
    hComposition.comp base (adjointFrameValue_hasFDerivAt first base)
  have hRight := hRightHead.clm_comp (second.first_hasFDerivAt base)
  have hFlip : HasFDerivAt
      (fun operator : Normal →L[ℝ] Ambient => composition.flip operator)
      composition.flip (second.field base) :=
    composition.flip.hasFDerivAt
  have hLeftHead : HasFDerivAt
      (fun point => composition.flip (second.field point))
      (composition.flip.comp (second.first base)) base :=
    hFlip.comp base (second.field_hasFDerivAt base)
  have hLeft := hLeftHead.clm_comp
    (adjointFrameFirst_hasFDerivAt first base)
  change HasFDerivAt
    (fun point =>
      (composition (adjointFrameValue first point)).comp (second.first point) +
        (composition.flip (second.field point)).comp
          (adjointFrameFirst first point))
    (canonicalTransitionSecond first second base) base
  simpa only [canonicalTransitionSecond, canonicalTransitionSecondRight,
    canonicalTransitionSecondLeft, normalFrameComposition] using
      hRight.add hLeft

/-- The first derivative agrees with the bridge formula. -/
theorem canonicalTransitionFirst_apply
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base x : Tangent) :
    canonicalTransitionFirst first second base x =
      adjointTransitionFirstFormula first second base x := by
  ext normal
  simp [canonicalTransitionFirst, adjointTransitionFirstFormula,
    normalFrameComposition, adjointFrameValue, adjointFrameFirst,
    realAdjointContinuousLinearMap_apply]
  abel

/-- The second derivative agrees with the bridge four-term Hessian formula. -/
theorem canonicalTransitionSecond_apply
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base x y : Tangent) :
    canonicalTransitionSecond first second base x y =
      adjointTransitionSecondFormula first second base x y := by
  ext normal
  simp [canonicalTransitionSecond, canonicalTransitionSecondRight,
    canonicalTransitionSecondLeft, adjointTransitionSecondFormula,
    normalFrameComposition, adjointFrameValue, adjointFrameFirst,
    adjointFrameSecond, adjointOnFrameDerivatives,
    realAdjointContinuousLinearMap_apply]
  abel

/-- The transition Hessian is symmetric because it is a genuine second Fréchet
derivative. -/
theorem canonicalTransitionSecond_symmetric
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base x y : Tangent) :
    canonicalTransitionSecond first second base x y =
      canonicalTransitionSecond first second base y x :=
  second_derivative_symmetric
    (fun point => canonicalTransitionField_hasFDerivAt first second point)
    (canonicalTransitionFirst_hasFDerivAt first second base) x y

/-- The operator field is the adjoint transition of the pointwise frame values. -/
theorem canonicalTransitionField_eq_adjointTransition
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (base : Tangent) :
    canonicalTransitionField first second base =
      normalFrameAdjointTransition
        (frameValueAt first base) (frameValueAt second base) := by
  rfl

/-- On equal ambient normal subspaces, it is the canonical orthogonal
transition. -/
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

/-- Direct orthogonal transition gauge two-jet. No independent value or
derivative witnesses are requested from the caller. -/
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

/-- Construct the exact bridge demanded by the earlier interface directly from
the two frame fields. -/
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

/-- Canonical Maurer--Cartan two-jet attached directly to two frame two-jets. -/
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

/-- Curvature covariance on a normal-frame overlap, with no independent gauge
jet witness. -/
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

/-- The former bridge existence atom is constructively realized in the fixed
ambient Hilbert model. -/
theorem direct_frame_frechet_construction_exists
    (first second : SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (frameValueAt first base) =
        normalFrameRange (frameValueAt second base)) :
    Nonempty (CanonicalNormalFrameTransitionTwoJet
      Tangent Normal Ambient) :=
  ⟨canonicalNormalFrameTransitionTwoJetOfFrames first second hRange⟩

/-- Remaining boundary after the fixed-model direct construction. -/
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
