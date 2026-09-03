import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

/-!
# Covariant derivative of a general symmetric tensor

The canonical holonomic atlas already carries the genuine coordinate
transition, its first two derivatives, and the proved nonlinear
Levi--Civita transformation law.  This gate uses those bricks to define the
local covariant derivative of any genuine smooth symmetric covariant
two-tensor.  The final overlap theorem states its tensorial transformation
law; no new compatibility datum is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Index4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Components of a genuine symmetric tensor in a supplied holonomic frame. -/
def localSymmetricTensorCoefficient
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) (coordinate : Vector4) : Real :=
  tensor (patch.coordinateMap coordinate)
    (patch.frame coordinate first) (patch.frame coordinate second)

theorem localSymmetricTensorCoefficient_contDiff
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞
      (localSymmetricTensorCoefficient period hPeriod tensor patch
        first second) := by
  exact patch.tensorCoefficient_contDiff tensor first second

/-- Matrix of a genuine symmetric tensor in a supplied holonomic frame. -/
def localSymmetricTensorMatrix
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Matrix4 :=
  fun first second =>
    localSymmetricTensorCoefficient period hPeriod tensor patch first second
      coordinate

theorem localSymmetricTensorMatrix_contDiff
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localSymmetricTensorMatrix period hPeriod tensor patch) := by
  have hFormula :
      localSymmetricTensorMatrix period hPeriod tensor patch =
        fun coordinate => ∑ first : Index4, ∑ second : Index4,
          localSymmetricTensorCoefficient period hPeriod tensor patch
              first second coordinate •
            Matrix.single first second (1 : Real) := by
    funext coordinate
    simpa [localSymmetricTensorMatrix] using
      (Matrix.matrix_eq_sum_single
        (localSymmetricTensorMatrix period hPeriod tensor patch coordinate))
  rw [hFormula]
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  exact
    (localSymmetricTensorCoefficient_contDiff period hPeriod tensor patch
      first second).smul_const _

/-- Coordinate bilinear form of a genuine symmetric tensor. -/
def localSymmetricTensorCoordinateForm
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : LinearMap.BilinForm Real Vector4 :=
  Matrix.toBilin'
    (localSymmetricTensorMatrix period hPeriod tensor patch coordinate)

/-- The coordinate form evaluates the intrinsic tensor on the two coordinate
derivatives. -/
theorem localSymmetricTensorCoordinateForm_apply
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : Vector4) :
    localSymmetricTensorCoordinateForm period hPeriod tensor patch coordinate
        firstVector secondVector =
      tensor (patch.coordinateMap coordinate)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate firstVector)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate secondVector) := by
  let frameEquiv :=
    (Pi.basisFun Real Index4).equiv (patch.frame coordinate)
      (Equiv.refl Index4)
  let coordinateTensor : LinearMap.BilinForm Real Vector4 :=
    (tensor (patch.coordinateMap coordinate)).toBilinForm.comp
      frameEquiv.toLinearMap frameEquiv.toLinearMap
  have hMatrix :
      localSymmetricTensorMatrix period hPeriod tensor patch coordinate =
        LinearMap.BilinForm.toMatrix' coordinateTensor := by
    ext first second
    have hFirst :
        frameEquiv (Pi.single first 1) =
          patch.frame coordinate first := by
      have hApply :
          frameEquiv ((Pi.basisFun Real Index4) first) =
            patch.frame coordinate first := by
        exact Module.Basis.equiv_apply _ _ _ _
      simpa only [Pi.basisFun_apply] using hApply
    have hSecond :
        frameEquiv (Pi.single second 1) =
          patch.frame coordinate second := by
      have hApply :
          frameEquiv ((Pi.basisFun Real Index4) second) =
            patch.frame coordinate second := by
        exact Module.Basis.equiv_apply _ _ _ _
      simpa only [Pi.basisFun_apply] using hApply
    change
      tensor (patch.coordinateMap coordinate)
          (patch.frame coordinate first) (patch.frame coordinate second) =
        coordinateTensor (Pi.single first 1) (Pi.single second 1)
    dsimp only [coordinateTensor]
    rw [LinearMap.BilinForm.comp_apply]
    change
      tensor (patch.coordinateMap coordinate)
          (patch.frame coordinate first) (patch.frame coordinate second) =
        tensor (patch.coordinateMap coordinate)
          (frameEquiv (Pi.single first 1))
          (frameEquiv (Pi.single second 1))
    rw [hFirst, hSecond]
  rw [localSymmetricTensorCoordinateForm, hMatrix,
    Matrix.toBilin'_toMatrix']
  change
    tensor (patch.coordinateMap coordinate)
        (frameEquiv firstVector) (frameEquiv secondVector) = _
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch]

private theorem symmetricTensor_evaluation_eq_of_heq
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    {firstPoint secondPoint : EffectiveQuotient period hPeriod}
    (firstLeft firstRight :
      TangentSpace coverModelWithCorners firstPoint)
    (secondLeft secondRight :
      TangentSpace coverModelWithCorners secondPoint)
    (hPoint : firstPoint = secondPoint)
    (hLeft : HEq firstLeft secondLeft)
    (hRight : HEq firstRight secondRight) :
    tensor firstPoint firstLeft firstRight =
      tensor secondPoint secondLeft secondRight := by
  subst secondPoint
  rw [eq_of_heq hLeft, eq_of_heq hRight]

/-- The coordinate form of any genuine tensor obeys the actual atlas
transition law on arbitrary vectors. -/
theorem localSymmetricTensorCoordinateForm_transition
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate firstVector secondVector : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localSymmetricTensorCoordinateForm period hPeriod tensor firstPatch
        firstCoordinate firstVector secondVector =
      localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
        secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint firstVector)
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          secondVector) := by
  rw [localSymmetricTensorCoordinateForm_apply,
    localSymmetricTensorCoordinateForm_apply]
  exact symmetricTensor_evaluation_eq_of_heq period hPeriod tensor
    _ _ _ _ samePoint
    (holonomicCoordinateMap_mfderiv_transition_heq period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate firstVector samePoint)
    (holonomicCoordinateMap_mfderiv_transition_heq period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate secondVector samePoint)

/-- On the genuine local inverse domain, first-chart coefficients are the
pullback of the second-chart tensor by the varying transition derivative. -/
theorem localSymmetricTensorCoefficient_eq_transitionPullback_of_mem
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint)
    (first second : Index4) :
    localSymmetricTensorCoefficient period hPeriod tensor firstPatch first
        second current =
      localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint current)
        (fderiv Real
          (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint) current
          (Pi.single first 1))
        (fderiv Real
          (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint) current
          (Pi.single second 1)) := by
  have hPoint :=
    holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current samePoint
      hCurrent
  have hFirst :=
    holonomicCoordinateMap_mfderiv_transition_heq_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current
      (Pi.single first 1) samePoint hCurrent
  have hSecond :=
    holonomicCoordinateMap_mfderiv_transition_heq_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current
      (Pi.single second 1) samePoint hCurrent
  rw [localSymmetricTensorCoordinateForm_apply]
  unfold localSymmetricTensorCoefficient
  rw [firstPatch.frame_eq_coordinateDerivative,
    firstPatch.frame_eq_coordinateDerivative]
  exact symmetricTensor_evaluation_eq_of_heq period hPeriod tensor
    _ _ _ _ hPoint.symm hFirst hSecond

/-- Germ-level pullback identity for every genuine symmetric tensor. -/
theorem localSymmetricTensorCoefficient_transitionPullback_eventuallyEq
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    localSymmetricTensorCoefficient period hPeriod tensor firstPatch first
        second =ᶠ[𝓝 firstCoordinate]
      fun current =>
        localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
          (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint current)
          (fderiv Real
            (holonomicCoordinateTransitionAt period hPeriod firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint) current
            (Pi.single first 1))
          (fderiv Real
            (holonomicCoordinateTransitionAt period hPeriod firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint) current
            (Pi.single second 1)) := by
  filter_upwards [
    (holonomicCoordinateTransitionDomainAt_isOpen period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).mem_nhds
      (firstCoordinate_mem_holonomicCoordinateTransitionDomainAt period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)]
    with current hCurrent
  exact
    localSymmetricTensorCoefficient_eq_transitionPullback_of_mem period hPeriod
      tensor firstPatch secondPatch firstCoordinate secondCoordinate current
      samePoint hCurrent first second

/-- First coordinate derivative of a genuine tensor coefficient. -/
def localSymmetricTensorDerivative
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative first second : Index4) : Real :=
  fderiv Real
      (localSymmetricTensorCoefficient period hPeriod tensor patch first second)
      coordinate (Pi.single derivative 1)

theorem localSymmetricTensorDerivative_contDiff
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (derivative first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localSymmetricTensorDerivative period hPeriod tensor patch coordinate
        derivative first second) := by
  have hDerivative : ContDiff Real ∞
      (fderiv Real
        (localSymmetricTensorCoefficient period hPeriod tensor patch
          first second)) :=
    (localSymmetricTensorCoefficient_contDiff period hPeriod tensor patch
      first second).fderiv_right (m := ∞) (by simp)
  exact hDerivative.clm_apply contDiff_const

private def tensorMatrixEntryContinuousLinearMap
    (first second : Index4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix first second
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp]
private theorem tensorMatrixEntryContinuousLinearMap_apply
    (first second : Index4) (matrix : Matrix4) :
    tensorMatrixEntryContinuousLinearMap first second matrix =
      matrix first second :=
  rfl

private theorem fderiv_tensor_matrix_entry_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (matrix : E → Matrix4) (point direction : E)
    (hMatrix : DifferentiableAt Real matrix point)
    (first second : Index4) :
    fderiv Real (fun current => matrix current first second)
        point direction =
      fderiv Real matrix point direction first second := by
  have hDerivativeMap :
      fderiv Real
          (tensorMatrixEntryContinuousLinearMap first second ∘ matrix) point =
        (tensorMatrixEntryContinuousLinearMap first second).comp
          (fderiv Real matrix point) :=
    ((tensorMatrixEntryContinuousLinearMap first second).hasFDerivAt.comp point
      hMatrix.hasFDerivAt).fderiv
  have hEntryFunction :
      tensorMatrixEntryContinuousLinearMap first second ∘ matrix =
        fun current => matrix current first second := by
    funext current
    rfl
  rw [hEntryFunction] at hDerivativeMap
  have hDerivative := congrArg
    (fun derivative : E →L[Real] Real => derivative direction)
    hDerivativeMap
  simpa only [ContinuousLinearMap.comp_apply,
    tensorMatrixEntryContinuousLinearMap_apply] using hDerivative

/-- The coordinate derivative of a symmetric tensor, bundled as a
trilinear form. -/
def localSymmetricTensorDerivativeTrilinearForm
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real where
  toFun direction :=
    Matrix.toBilin'
      (fderiv Real
        (localSymmetricTensorMatrix period hPeriod tensor patch) coordinate
        direction)
  map_add' first second := by
    simp
  map_smul' scalar direction := by
    simp

@[simp]
theorem localSymmetricTensorDerivativeTrilinearForm_apply
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate direction firstVector secondVector : Vector4) :
    localSymmetricTensorDerivativeTrilinearForm period hPeriod tensor patch
        coordinate direction firstVector secondVector =
      Matrix.toBilin'
        (fderiv Real
          (localSymmetricTensorMatrix period hPeriod tensor patch) coordinate
          direction)
        firstVector secondVector :=
  rfl

@[simp]
theorem localSymmetricTensorDerivativeTrilinearForm_basis
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    localSymmetricTensorDerivativeTrilinearForm period hPeriod tensor patch
        coordinate (Pi.single derivative 1) (Pi.single first 1)
        (Pi.single second 1) =
      localSymmetricTensorDerivative period hPeriod tensor patch coordinate
        derivative first second := by
  rw [localSymmetricTensorDerivativeTrilinearForm_apply,
    Matrix.toBilin'_single]
  unfold localSymmetricTensorDerivative
  have hMatrix :
      DifferentiableAt Real
        (localSymmetricTensorMatrix period hPeriod tensor patch) coordinate :=
    (localSymmetricTensorMatrix_contDiff period hPeriod tensor patch)
      |>.differentiable (by simp) coordinate
  simpa only [localSymmetricTensorMatrix] using
    (fderiv_tensor_matrix_entry_apply
      (localSymmetricTensorMatrix period hPeriod tensor patch) coordinate
      (Pi.single derivative 1) hMatrix first second).symm

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApply := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApply

/-- Exact first-derivative transformation of an arbitrary symmetric tensor.
The two inhomogeneous second-transition-derivative terms are displayed
explicitly; they will cancel against the Levi--Civita corrections. -/
theorem localSymmetricTensorDerivative_transition
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (derivative first second : Index4) :
    localSymmetricTensorDerivative period hPeriod tensor firstPatch
        firstCoordinate derivative first second =
      localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
            firstPatch secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single derivative 1) (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        localSymmetricTensorDerivativeTrilinearForm period hPeriod tensor
          secondPatch secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single derivative 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
            firstPatch secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single derivative 1) (Pi.single second 1)) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let secondTensorMatrix :=
    localSymmetricTensorMatrix period hPeriod tensor secondPatch
  let left : Vector4 → Vector4 := fun current =>
    fderiv Real transition current (Pi.single first 1)
  let right : Vector4 → Vector4 := fun current =>
    fderiv Real transition current (Pi.single second 1)
  have hTransitionC2 :
      ContDiffAt Real 2 transition firstCoordinate := by
    simpa only [transition] using
      (((holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
          |>.contMDiffAt.contDiffAt).of_le (by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top))
  have hTransition :
      DifferentiableAt Real transition firstCoordinate :=
    hTransitionC2.differentiableAt (by norm_num)
  have hTransitionDerivative :
      DifferentiableAt Real (fderiv Real transition) firstCoordinate :=
    (hTransitionC2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hLeft : DifferentiableAt Real left firstCoordinate := by
    apply differentiableAt_pi.mpr
    intro upper
    let evaluation : (Vector4 →L[Real] Vector4) →L[Real] Real :=
      (ContinuousLinearMap.proj upper).comp
        (ContinuousLinearMap.apply Real Vector4 (Pi.single first 1))
    have hComposition :=
      evaluation.differentiableAt.comp firstCoordinate hTransitionDerivative
    have hFunction :
        evaluation ∘ fderiv Real transition =
          fun current =>
            fderiv Real transition current (Pi.single first 1) upper := by
      funext current
      rfl
    rw [hFunction] at hComposition
    exact hComposition
  have hRight : DifferentiableAt Real right firstCoordinate := by
    apply differentiableAt_pi.mpr
    intro upper
    let evaluation : (Vector4 →L[Real] Vector4) →L[Real] Real :=
      (ContinuousLinearMap.proj upper).comp
        (ContinuousLinearMap.apply Real Vector4 (Pi.single second 1))
    have hComposition :=
      evaluation.differentiableAt.comp firstCoordinate hTransitionDerivative
    have hFunction :
        evaluation ∘ fderiv Real transition =
          fun current =>
            fderiv Real transition current (Pi.single second 1) upper := by
      funext current
      rfl
    rw [hFunction] at hComposition
    exact hComposition
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition] using
      holonomicCoordinateTransitionAt_apply period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hSecondTensor :
      DifferentiableAt Real secondTensorMatrix secondCoordinate :=
    (localSymmetricTensorMatrix_contDiff period hPeriod tensor secondPatch)
      |>.differentiable (by simp) secondCoordinate
  have hSecondTensorAtTransition :
      DifferentiableAt Real secondTensorMatrix
        (transition firstCoordinate) := by
    simpa only [hTransitionAt] using hSecondTensor
  have hMatrixComposition :
      DifferentiableAt Real (secondTensorMatrix ∘ transition)
        firstCoordinate :=
    hSecondTensorAtTransition.comp firstCoordinate hTransition
  have hPullbackFunction :
      (fun current =>
        localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
          (transition current)
          (fderiv Real transition current (Pi.single first 1))
          (fderiv Real transition current (Pi.single second 1))) =
        fun current =>
          Matrix.toBilin' ((secondTensorMatrix ∘ transition) current)
            (left current) (right current) := by
    funext current
    rfl
  have hDerivativeEquality :
      fderiv Real
          (localSymmetricTensorCoefficient period hPeriod tensor firstPatch
            first second)
          firstCoordinate =
        fderiv Real
          (fun current =>
            localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
              (transition current)
              (fderiv Real transition current (Pi.single first 1))
              (fderiv Real transition current (Pi.single second 1)))
          firstCoordinate :=
    Filter.EventuallyEq.fderiv_eq
      (localSymmetricTensorCoefficient_transitionPullback_eventuallyEq
        period hPeriod tensor firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint first second)
  have hDerivativeApply := congrArg
    (fun derivativeMap : Vector4 →L[Real] Real =>
      derivativeMap (Pi.single derivative 1))
    hDerivativeEquality
  change
      fderiv Real
          (localSymmetricTensorCoefficient period hPeriod tensor firstPatch
            first second)
          firstCoordinate (Pi.single derivative 1) =
        fderiv Real
          (fun current =>
            localSymmetricTensorCoordinateForm period hPeriod tensor secondPatch
              (transition current)
              (fderiv Real transition current (Pi.single first 1))
              (fderiv Real transition current (Pi.single second 1)))
          firstCoordinate (Pi.single derivative 1)
    at hDerivativeApply
  rw [hPullbackFunction] at hDerivativeApply
  rw [fderiv_matrix_toBilin_dynamic_apply
    (secondTensorMatrix ∘ transition) left right firstCoordinate
    (Pi.single derivative 1) hMatrixComposition hLeft hRight]
    at hDerivativeApply
  have hLinearDerivative :
      (transitionLinear : Vector4 →L[Real] Vector4) =
        fderiv Real transition firstCoordinate := by
    simpa only [transitionLinear, transition] using
      holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hLeftAt :
      left firstCoordinate =
        transitionLinear (Pi.single first 1) := by
    dsimp only [left]
    rw [← hLinearDerivative]
    exact ContinuousLinearEquiv.coe_apply transitionLinear _
  have hRightAt :
      right firstCoordinate =
        transitionLinear (Pi.single second 1) := by
    dsimp only [right]
    rw [← hLinearDerivative]
    exact ContinuousLinearEquiv.coe_apply transitionLinear _
  have hLeftDerivative :
      fderiv Real left firstCoordinate (Pi.single derivative 1) =
        holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
          firstPatch secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single derivative 1) (Pi.single first 1) := by
    simpa only [left, transition,
      holonomicCoordinateTransitionSecondDerivativeAt] using
      fderiv_continuousLinearMap_apply_const
        (fderiv Real transition) firstCoordinate (Pi.single derivative 1)
        (Pi.single first 1) hTransitionDerivative
  have hRightDerivative :
      fderiv Real right firstCoordinate (Pi.single derivative 1) =
        holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
          firstPatch secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single derivative 1) (Pi.single second 1) := by
    simpa only [right, transition,
      holonomicCoordinateTransitionSecondDerivativeAt] using
      fderiv_continuousLinearMap_apply_const
        (fderiv Real transition) firstCoordinate (Pi.single derivative 1)
        (Pi.single second 1) hTransitionDerivative
  have hMatrixAt :
      (secondTensorMatrix ∘ transition) firstCoordinate =
        secondTensorMatrix secondCoordinate := by
    rw [Function.comp_apply, hTransitionAt]
  have hMatrixDerivative :
      fderiv Real (secondTensorMatrix ∘ transition) firstCoordinate
          (Pi.single derivative 1) =
        fderiv Real secondTensorMatrix secondCoordinate
          (transitionLinear (Pi.single derivative 1)) := by
    have hChain :
        fderiv Real (secondTensorMatrix ∘ transition) firstCoordinate =
          (fderiv Real secondTensorMatrix (transition firstCoordinate)).comp
            (fderiv Real transition firstCoordinate) :=
      (hSecondTensorAtTransition.hasFDerivAt.comp firstCoordinate
        hTransition.hasFDerivAt).fderiv
    have hApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Matrix4 =>
        derivativeMap (Pi.single derivative 1))
      hChain
    rw [hTransitionAt, ← hLinearDerivative] at hApply
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_apply] using hApply
  rw [hMatrixAt, hLeftAt, hRightAt, hLeftDerivative, hRightDerivative,
    hMatrixDerivative] at hDerivativeApply
  simpa only [localSymmetricTensorDerivative,
    localSymmetricTensorCoordinateForm,
    localSymmetricTensorDerivativeTrilinearForm_apply, secondTensorMatrix,
    transitionLinear] using hDerivativeApply

/-- Local Levi--Civita covariant derivative of a symmetric tensor. -/
def localSymmetricTensorCovariantDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative first second : Index4) : Real :=
  localSymmetricTensorDerivative period hPeriod tensor patch coordinate
      derivative first second -
    ∑ upper : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper derivative first *
        localSymmetricTensorCoefficient period hPeriod tensor patch upper
          second coordinate -
    ∑ upper : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper derivative second *
      localSymmetricTensorCoefficient period hPeriod tensor patch first
          upper coordinate

@[simp]
private theorem localLeviCivitaChristoffelApply_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : Vector4) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        (first + second) vector =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          first vector +
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          second vector := by
  change
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
        (first + second) vector = _
  rw [map_add, LinearMap.add_apply]
  simp only [localLeviCivitaChristoffelBilinearMap_apply]

@[simp]
private theorem localLeviCivitaChristoffelApply_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector secondVector : Vector4) (scalar : Real) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        (scalar • vector) secondVector =
      scalar • localLeviCivitaChristoffelApply period hPeriod metric patch
        coordinate vector secondVector := by
  change
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
        (scalar • vector) secondVector = _
  rw [map_smul, LinearMap.smul_apply]
  simp only [localLeviCivitaChristoffelBilinearMap_apply]

@[simp]
private theorem localLeviCivitaChristoffelApply_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate direction first second : Vector4) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        direction (first + second) =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          direction first +
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          direction second := by
  change
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
        direction (first + second) = _
  rw [map_add]
  simp only [localLeviCivitaChristoffelBilinearMap_apply]

@[simp]
private theorem localLeviCivitaChristoffelApply_smul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate direction vector : Vector4) (scalar : Real) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        direction (scalar • vector) =
      scalar • localLeviCivitaChristoffelApply period hPeriod metric patch
        coordinate direction vector := by
  change
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
        direction (scalar • vector) = _
  rw [map_smul]
  simp only [localLeviCivitaChristoffelBilinearMap_apply]

/-- Vector form of the local covariant derivative. -/
def localSymmetricTensorCovariantDerivativeApply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate direction firstVector secondVector : Vector4) : Real :=
  localSymmetricTensorDerivativeTrilinearForm period hPeriod tensor patch
      coordinate direction firstVector secondVector -
    localSymmetricTensorCoordinateForm period hPeriod tensor patch coordinate
      (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        direction firstVector)
      secondVector -
    localSymmetricTensorCoordinateForm period hPeriod tensor patch coordinate
      firstVector
      (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        direction secondVector)

/-- The local covariant derivative as a genuine trilinear form. -/
def localSymmetricTensorCovariantDerivativeTrilinearForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real where
  toFun direction :=
    { toFun := fun firstVector =>
        { toFun := fun secondVector =>
            localSymmetricTensorCovariantDerivativeApply period hPeriod metric
              tensor patch coordinate direction firstVector secondVector
          map_add' := by
            intro first second
            simp [localSymmetricTensorCovariantDerivativeApply]
            ring
          map_smul' := by
            intro scalar vector
            simp [localSymmetricTensorCovariantDerivativeApply]
            ring }
      map_add' := by
        intro first second
        ext third
        simp [localSymmetricTensorCovariantDerivativeApply]
        ring
      map_smul' := by
        intro scalar vector
        ext third
        simp [localSymmetricTensorCovariantDerivativeApply]
        ring }
  map_add' := by
    intro first second
    ext middle last
    simp [localSymmetricTensorCovariantDerivativeApply]
    ring
  map_smul' := by
    intro scalar vector
    ext middle last
    simp [localSymmetricTensorCovariantDerivativeApply]
    ring

@[simp]
theorem localSymmetricTensorCovariantDerivativeTrilinearForm_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate direction firstVector secondVector : Vector4) :
    localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod metric
        tensor patch coordinate direction firstVector secondVector =
      localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
        patch coordinate direction firstVector secondVector :=
  rfl

/-- Pullback of a trilinear form by one linear coordinate transition. -/
def trilinearFormPullback
    (form : Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real)
    (linear : Vector4 →ₗ[Real] Vector4) :
    Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real where
  toFun first :=
    { toFun := fun second =>
        { toFun := fun third =>
            form (linear first) (linear second) (linear third)
          map_add' := by simp
          map_smul' := by simp }
      map_add' := by
        intro left right
        ext third
        simp
      map_smul' := by
        intro scalar vector
        ext third
        simp }
  map_add' := by
    intro left right
    ext second third
    simp
  map_smul' := by
    intro scalar vector
    ext second third
    simp

@[simp]
theorem trilinearFormPullback_apply
    (form : Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real)
    (linear : Vector4 →ₗ[Real] Vector4)
    (first second third : Vector4) :
    trilinearFormPullback form linear first second third =
      form (linear first) (linear second) (linear third) :=
  rfl

@[simp]
theorem localSymmetricTensorCovariantDerivativeApply_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative first second : Index4) :
    localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
        patch coordinate (Pi.single derivative 1) (Pi.single first 1)
        (Pi.single second 1) =
      localSymmetricTensorCovariantDerivative period hPeriod metric tensor patch
        coordinate derivative first second := by
  rw [localSymmetricTensorCovariantDerivativeApply,
    localSymmetricTensorDerivativeTrilinearForm_basis]
  have hFirst :
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          (Pi.single derivative 1) (Pi.single first 1) =
        fun upper =>
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper derivative first := by
    simpa only [localLeviCivitaChristoffelBilinearMap_apply] using
      localLeviCivitaChristoffelBilinearMap_basis period hPeriod metric patch
        coordinate derivative first
  have hSecond :
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          (Pi.single derivative 1) (Pi.single second 1) =
        fun upper =>
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper derivative second := by
    simpa only [localLeviCivitaChristoffelBilinearMap_apply] using
      localLeviCivitaChristoffelBilinearMap_basis period hPeriod metric patch
        coordinate derivative second
  rw [hFirst, hSecond]
  simp only [localSymmetricTensorCoordinateForm, Matrix.toBilin'_apply,
    localSymmetricTensorMatrix, localSymmetricTensorCovariantDerivative]
  simp [Pi.single_apply]
  apply Finset.sum_congr rfl
  intro upper _
  ring

/-- The local covariant derivative transforms as a genuine covariant
rank-three tensor on every overlap of the canonical holonomic atlas. -/
theorem localSymmetricTensorCovariantDerivativeApply_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (derivative first second : Index4) :
    localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
        firstPatch firstCoordinate (Pi.single derivative 1)
        (Pi.single first 1) (Pi.single second 1) =
      localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
        secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single derivative 1))
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single first 1))
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single second 1)) := by
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let derivativeVector : Vector4 := Pi.single derivative 1
  let firstVector : Vector4 := Pi.single first 1
  let secondVector : Vector4 := Pi.single second 1
  let firstTransitionSecond : Vector4 :=
    holonomicCoordinateTransitionSecondDerivativeAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint derivativeVector
      firstVector
  let secondTransitionSecond : Vector4 :=
    holonomicCoordinateTransitionSecondDerivativeAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint derivativeVector
      secondVector
  have hConnection :=
    canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint
  have hFirstChristoffel :
      transitionLinear
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate derivativeVector firstVector) =
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate (transitionLinear derivativeVector)
            (transitionLinear firstVector) +
          firstTransitionSecond := by
    simpa only [transitionLinear, derivativeVector, firstVector,
      firstTransitionSecond] using
      hConnection.christoffel_transform derivative first
  have hSecondChristoffel :
      transitionLinear
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate derivativeVector secondVector) =
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate (transitionLinear derivativeVector)
            (transitionLinear secondVector) +
          secondTransitionSecond := by
    simpa only [transitionLinear, derivativeVector, secondVector,
      secondTransitionSecond] using
      hConnection.christoffel_transform derivative second
  rw [localSymmetricTensorCovariantDerivativeApply,
    localSymmetricTensorCovariantDerivativeApply]
  rw [localSymmetricTensorDerivativeTrilinearForm_basis]
  rw [localSymmetricTensorDerivative_transition period hPeriod tensor
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint
    derivative first second]
  rw [localSymmetricTensorCoordinateForm_transition period hPeriod tensor
    firstPatch secondPatch firstCoordinate secondCoordinate
    (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
      firstCoordinate derivativeVector firstVector)
    secondVector samePoint]
  rw [localSymmetricTensorCoordinateForm_transition period hPeriod tensor
    firstPatch secondPatch firstCoordinate secondCoordinate firstVector
    (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
      firstCoordinate derivativeVector secondVector) samePoint]
  rw [hFirstChristoffel, hSecondChristoffel]
  simp only [map_add, LinearMap.add_apply]
  dsimp only [transitionLinear, derivativeVector, firstVector, secondVector,
    firstTransitionSecond, secondTransitionSecond]
  ring

/-- Bundled arbitrary-vector overlap law.  Thus the local formulas are the
coordinate presentations of one covariant rank-three tensor. -/
theorem localSymmetricTensorCovariantDerivativeTrilinearForm_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod metric
        tensor firstPatch firstCoordinate =
      trilinearFormPullback
        (localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod
          metric tensor secondPatch secondCoordinate)
        ((holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint)
            |>.toLinearEquiv.toLinearMap) := by
  apply (Pi.basisFun Real Index4).ext
  intro derivative
  apply (Pi.basisFun Real Index4).ext
  intro first
  apply (Pi.basisFun Real Index4).ext
  intro second
  simpa only [Pi.basisFun_apply,
    localSymmetricTensorCovariantDerivativeTrilinearForm_apply,
    trilinearFormPullback_apply, LinearEquiv.coe_toLinearMap,
    ContinuousLinearEquiv.coe_toLinearEquiv] using
    localSymmetricTensorCovariantDerivativeApply_transition period hPeriod
      metric tensor firstPatch secondPatch firstCoordinate secondCoordinate
      samePoint derivative first second

/-- Component form of the same overlap law. -/
theorem localSymmetricTensorCovariantDerivative_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (derivative first second : Index4) :
    localSymmetricTensorCovariantDerivative period hPeriod metric tensor
        firstPatch firstCoordinate derivative first second =
      localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor
        secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single derivative 1))
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single first 1))
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single second 1)) := by
  rw [← localSymmetricTensorCovariantDerivativeApply_basis]
  exact
    localSymmetricTensorCovariantDerivativeApply_transition period hPeriod
      metric tensor firstPatch secondPatch firstCoordinate secondCoordinate
      samePoint derivative first second

theorem localSymmetricTensorCovariantDerivative_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (derivative first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localSymmetricTensorCovariantDerivative period hPeriod metric tensor
        patch coordinate derivative first second) := by
  apply ContDiff.sub
  · apply ContDiff.sub
    · exact localSymmetricTensorDerivative_contDiff period hPeriod tensor patch
        derivative first second
    · apply ContDiff.sum
      intro upper _
      exact
        (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
          upper derivative first).mul
          (localSymmetricTensorCoefficient_contDiff period hPeriod tensor patch
            upper second)
  · apply ContDiff.sum
    intro upper _
    exact
      (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
        upper derivative second).mul
        (localSymmetricTensorCoefficient_contDiff period hPeriod tensor patch
          first upper)

/-- Covariant differentiation preserves symmetry in the two tensor slots. -/
theorem localSymmetricTensorCovariantDerivative_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative first second : Index4) :
    localSymmetricTensorCovariantDerivative period hPeriod metric tensor patch
        coordinate derivative first second =
      localSymmetricTensorCovariantDerivative period hPeriod metric tensor patch
        coordinate derivative second first := by
  have hCoefficient :
      localSymmetricTensorCoefficient period hPeriod tensor patch first second =
        localSymmetricTensorCoefficient period hPeriod tensor patch second
          first := by
    funext current
    exact tensor.symmetric _ _ _
  have hDerivative := congrArg
    (fun function : Vector4 → Real =>
      fderiv Real function coordinate (Pi.single derivative 1))
    hCoefficient
  simp only [localSymmetricTensorCovariantDerivative,
    localSymmetricTensorDerivative] at hDerivative ⊢
  rw [hDerivative]
  have hFirstUpper :
      ∀ upper : Index4,
        localSymmetricTensorCoefficient period hPeriod tensor patch upper
            first coordinate =
          localSymmetricTensorCoefficient period hPeriod tensor patch first
            upper coordinate := by
    intro upper
    exact tensor.symmetric _ _ _
  have hSecondUpper :
      ∀ upper : Index4,
        localSymmetricTensorCoefficient period hPeriod tensor patch upper
            second coordinate =
          localSymmetricTensorCoefficient period hPeriod tensor patch second
            upper coordinate := by
    intro upper
    exact tensor.symmetric _ _ _
  simp_rw [hFirstUpper, hSecondUpper]
  ring

/-- The constructed derivative is metric-compatible. -/
@[simp]
theorem localSymmetricTensorCovariantDerivative_metric_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative first second : Index4) :
    localSymmetricTensorCovariantDerivative period hPeriod metric metric.tensor
        patch coordinate derivative first second = 0 := by
  have hCompatibility :=
    (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
      |>.metricCompatible derivative first second
  change
    localMetricDerivative period hPeriod metric patch coordinate derivative
          first second =
      (∑ upper : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper derivative first *
          localMetricCoefficient period hPeriod metric patch upper second
            coordinate) +
        ∑ upper : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              upper derivative second *
            localMetricCoefficient period hPeriod metric patch first upper
              coordinate
    at hCompatibility
  change
    localMetricDerivative period hPeriod metric patch coordinate derivative
          first second -
        ∑ upper : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              upper derivative first *
            localMetricCoefficient period hPeriod metric patch upper second
              coordinate -
      ∑ upper : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper derivative second *
          localMetricCoefficient period hPeriod metric patch first upper
            coordinate = 0
  rw [hCompatibility]
  ring

end
end P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D
end JanusFormal
