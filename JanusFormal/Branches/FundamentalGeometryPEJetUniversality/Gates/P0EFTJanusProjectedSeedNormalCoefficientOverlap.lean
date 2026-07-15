import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedSmoothCoefficientTransport
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenCanonicalTransition

namespace JanusFormal
namespace P0EFTJanusProjectedSeedNormalCoefficientOverlap

set_option autoImplicit false

noncomputable section

open Module
open scoped InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusNormalFrameSmoothTransition
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusProjectedSeedSmoothCoefficientTransport

universe u v w x y

variable {Base : Type w} {Tangent : Type u}
variable {Normal : Type v} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Fixed-model normal coordinates supplied by the Hilbert adjoint of one
isometric normal frame. -/
def frameAdjointCoordinates
    (frame : Normal →ₗᵢ[ℝ] Ambient) : Ambient →L[ℝ] Normal :=
  realAdjointContinuousLinearMap frame.toContinuousLinearMap

/-- If two isometric normal frames have the same ambient image, their adjoint
coordinate maps differ exactly by the canonical orthogonal transition. -/
theorem frameAdjointCoordinates_transition
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second) :
    frameAdjointCoordinates first =
      ((normalFrameTransition first second hRange)
        .toContinuousLinearEquiv.toContinuousLinearMap).comp
          (frameAdjointCoordinates second) := by
  apply ContinuousLinearMap.ext
  intro ambient
  apply ext_inner_right ℝ
  intro normal
  let transition := normalFrameTransition first second hRange
  change
    ⟪ContinuousLinearMap.adjoint first.toContinuousLinearMap ambient,
        normal⟫_ℝ =
      ⟪transition
          (ContinuousLinearMap.adjoint second.toContinuousLinearMap ambient),
        normal⟫_ℝ
  calc
    ⟪ContinuousLinearMap.adjoint first.toContinuousLinearMap ambient,
        normal⟫_ℝ =
      ⟪ambient, first normal⟫_ℝ :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪ambient, second (transition.symm normal)⟫_ℝ := by
      have hFrame := normalFrameTransition_spec first second hRange
        (transition.symm normal)
      have hFrame' : first normal = second (transition.symm normal) := by
        simpa [transition] using hFrame
      rw [hFrame']
    _ =
      ⟪ContinuousLinearMap.adjoint second.toContinuousLinearMap ambient,
        transition.symm normal⟫_ℝ := by
      symm
      exact ContinuousLinearMap.adjoint_inner_left _ _ _
    _ =
      ⟪transition
          (ContinuousLinearMap.adjoint second.toContinuousLinearMap ambient),
        normal⟫_ℝ :=
      (transition.inner_map_eq_flip _ _).symm

@[simp]
theorem frameAdjointCoordinates_transition_apply
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second)
    (ambient : Ambient) :
    frameAdjointCoordinates first ambient =
      normalFrameTransition first second hRange
        (frameAdjointCoordinates second ambient) := by
  have hAt := congrArg
    (fun operator : Ambient →L[ℝ] Normal => operator ambient)
    (frameAdjointCoordinates_transition first second hRange)
  exact hAt

/-- Normal coefficient extracted from one ambient bilinear tensor through one
isometric normal frame. -/
def frameNormalQuadratic
    (frame : Normal →ₗᵢ[ℝ] Ambient)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  projectedSeedFixedNormalQuadratic
    (frameAdjointCoordinates frame) ambientForm

@[simp]
theorem frameNormalQuadratic_transition_apply
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (x y : Tangent) :
    frameNormalQuadratic first ambientForm x y =
      normalFrameTransition first second hRange
        (frameNormalQuadratic second ambientForm x y) := by
  change frameAdjointCoordinates first (ambientForm x y) =
    normalFrameTransition first second hRange
      (frameAdjointCoordinates second (ambientForm x y))
  exact frameAdjointCoordinates_transition_apply first second hRange
    (ambientForm x y)

/-- Normal coordinates of one ambient vector through one isometric frame. -/
def frameNormalVector
    (frame : Normal →ₗᵢ[ℝ] Ambient)
    (ambientNormal : Ambient) : Normal :=
  frameAdjointCoordinates frame ambientNormal

@[simp]
theorem frameNormalVector_transition
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second)
    (ambientNormal : Ambient) :
    frameNormalVector first ambientNormal =
      normalFrameTransition first second hRange
        (frameNormalVector second ambientNormal) :=
  frameAdjointCoordinates_transition_apply first second hRange ambientNormal

/-- The physical Riesz operator is independent of the normal coordinates used
on a common ambient normal subspace. -/
theorem continuousIIRieszShapeOperator_frame_independent
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (ambientNormal : Ambient) :
    continuousIIRieszShapeOperator
        (frameNormalQuadratic first ambientForm)
        (frameNormalVector first ambientNormal) =
      continuousIIRieszShapeOperator
        (frameNormalQuadratic second ambientForm)
        (frameNormalVector second ambientNormal) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [continuousIIRieszShapeOperator_inner,
    continuousIIRieszShapeOperator_inner,
    frameNormalQuadratic_transition_apply first second hRange ambientForm x y,
    frameNormalVector_transition first second hRange ambientNormal]
  exact (normalFrameTransition first second hRange).inner_map_map _ _

/-- Open-domain version of the adjoint-coordinate transition law. -/
theorem openFrameAdjointCoordinates_transition_apply
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Normal Ambient domain)
    (hRange : ∀ base, base ∈ domain →
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base))
    (base : Base) (hBase : base ∈ domain) (ambient : Ambient) :
    frameAdjointCoordinates (first.frame base) ambient =
      (openCanonicalFrameTransition first second hRange).frame base
        (frameAdjointCoordinates (second.frame base) ambient) := by
  change frameAdjointCoordinates (first.frame base) ambient =
    openCanonicalFrameTransitionValue first second hRange base
      (frameAdjointCoordinates (second.frame base) ambient)
  rw [openCanonicalFrameTransitionValue]
  simp only [hBase]
  exact frameAdjointCoordinates_transition_apply
    (first.frame base) (second.frame base) (hRange base hBase) ambient

/-- Open-domain coordinate independence of the Riesz operator. -/
theorem openContinuousIIRieszShapeOperator_frame_independent
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Normal Ambient domain)
    (hRange : ∀ base, base ∈ domain →
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base))
    (base : Base) (hBase : base ∈ domain)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (ambientNormal : Ambient) :
    continuousIIRieszShapeOperator
        (frameNormalQuadratic (first.frame base) ambientForm)
        (frameNormalVector (first.frame base) ambientNormal) =
      continuousIIRieszShapeOperator
        (frameNormalQuadratic (second.frame base) ambientForm)
        (frameNormalVector (second.frame base) ambientNormal) :=
  continuousIIRieszShapeOperator_frame_independent
    (first.frame base) (second.frame base) (hRange base hBase)
    ambientForm ambientNormal

/-- Two valid point-centered projected-seed normal frames have the same ambient
range because both equal the orthogonal complement of the same tangent span. -/
theorem projectedSeedNormalFrames_sameRange
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (firstCenter secondCenter base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) firstCenter base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) secondCenter base) :
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData firstCenter).frame base) =
      normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData secondCenter).frame base) := by
  calc
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData firstCenter).frame base) =
      projectedSeedNormalSpan basisData firstCenter base :=
        pointwiseBasisSmoothNormalFrameFamilyOn_range normalBasis
          hNormalBasis basisData firstCenter base hFirst
    _ = (tangentFrameSpan basisData base)ᗮ :=
      projectedSeedNormalSpan_eq_tangentFrameSpan_orthogonal
        basisData hDimension firstCenter base hFirst
    _ = projectedSeedNormalSpan basisData secondCenter base :=
      (projectedSeedNormalSpan_eq_tangentFrameSpan_orthogonal
        basisData hDimension secondCenter base hSecond).symm
    _ = normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData secondCenter).frame base) :=
      (pointwiseBasisSmoothNormalFrameFamilyOn_range normalBasis
        hNormalBasis basisData secondCenter base hSecond).symm

/-- Projected-seed adjoint coordinates on two valid charts differ by their
canonical normal transition. -/
theorem projectedSeedChartNormalAdjoint_transition_apply
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (firstCenter secondCenter base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) firstCenter base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) secondCenter base)
    (ambient : Ambient) :
    projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
        basisData firstCenter base ambient =
      normalFrameTransition
          ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
            hNormalBasis basisData firstCenter).frame base)
          ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
            hNormalBasis basisData secondCenter).frame base)
          (projectedSeedNormalFrames_sameRange normalBasis hNormalBasis
            basisData hDimension firstCenter secondCenter base hFirst hSecond)
        (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
          basisData secondCenter base ambient) := by
  change frameAdjointCoordinates
      ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData firstCenter).frame base) ambient = _
  exact frameAdjointCoordinates_transition_apply
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData firstCenter).frame base)
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData secondCenter).frame base)
    (projectedSeedNormalFrames_sameRange normalBasis hNormalBasis
      basisData hDimension firstCenter secondCenter base hFirst hSecond)
    ambient

/-- For one common ambient corrected coefficient pair, the projected-seed Riesz
operator is identical in the normal coordinates of any two valid charts. -/
theorem projectedSeedRieszOperator_normalChart_independent
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (firstCenter secondCenter base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) firstCenter base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) secondCenter base)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (ambientNormal : Ambient) :
    continuousIIRieszShapeOperator
        (projectedSeedFixedNormalQuadratic
          (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
            basisData firstCenter base) ambientForm)
        (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
          basisData firstCenter base ambientNormal) =
      continuousIIRieszShapeOperator
        (projectedSeedFixedNormalQuadratic
          (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
            basisData secondCenter base) ambientForm)
        (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
          basisData secondCenter base ambientNormal) := by
  exact continuousIIRieszShapeOperator_frame_independent
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData firstCenter).frame base)
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData secondCenter).frame base)
    (projectedSeedNormalFrames_sameRange normalBasis hNormalBasis
      basisData hDimension firstCenter secondCenter base hFirst hSecond)
    ambientForm ambientNormal

/-- Audit boundary after normal-coordinate overlap compatibility. -/
structure ProjectedSeedNormalCoefficientOverlapStatus where
  adjointCoordinateTransitionProved : Prop
  secondFundamentalCoefficientTransitionProved : Prop
  physicalNormalTransitionProved : Prop
  pointwiseRieszCoordinateIndependenceProved : Prop
  openDomainTransitionInserted : Prop
  projectedSeedChartRangeCompatibilityProved : Prop
  correctedAmbientJetOverlapCompatibilityProved : Prop
  tangentCoordinateCompatibilityProved : Prop
  globalActualJetDescentProved : Prop

def projectedSeedNormalCoefficientOverlapClosed
    (s : ProjectedSeedNormalCoefficientOverlapStatus) : Prop :=
  s.adjointCoordinateTransitionProved ∧
  s.secondFundamentalCoefficientTransitionProved ∧
  s.physicalNormalTransitionProved ∧
  s.pointwiseRieszCoordinateIndependenceProved ∧
  s.openDomainTransitionInserted ∧
  s.projectedSeedChartRangeCompatibilityProved ∧
  s.correctedAmbientJetOverlapCompatibilityProved ∧
  s.tangentCoordinateCompatibilityProved ∧
  s.globalActualJetDescentProved

theorem missing_corrected_ambient_overlap_blocks_descent
    (s : ProjectedSeedNormalCoefficientOverlapStatus)
    (hMissing : Not s.correctedAmbientJetOverlapCompatibilityProved) :
    Not (projectedSeedNormalCoefficientOverlapClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusProjectedSeedNormalCoefficientOverlap
end JanusFormal
