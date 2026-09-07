import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

/-! # Intrinsic tensor divergence in a redundant finite generating family

The two covariant slots supply their actual connection corrections. The
contraction uses the reconstructed smooth dual and the genuine metric sharp,
not the inverse of the redundant Gram matrix.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameCovariantTensorDivergence4D

set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusRegularFrameMetricTensorTrace4D

private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance
local instance (point : EffectiveQuotient period hPeriod) :
    T2Space (TangentSpace coverModelWithCorners point) := by
  change T2Space CoverCoordinates
  infer_instance

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- Pullback of an actual smooth generator through the holonomic chart. -/
def finiteFramePulledVector
    (frame : SmoothD8Frame period hPeriod) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Fin frame.count) : Vector4 → Vector4 :=
  VectorField.mpullback (modelWithCornersSelf Real Vector4) coverModelWithCorners
    patch.coordinateMap (fun point => frame.vectorAt point index)

private theorem coordinateDerivative_isInvertible
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate).IsInvertible :=
  ⟨patch.coordinateMap_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) coordinate, rfl⟩

theorem coordinateMap_mfderiv_finiteFramePulledVector
    (frame : SmoothD8Frame period hPeriod) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin frame.count) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners patch.coordinateMap coordinate
        (finiteFramePulledVector period hPeriod frame patch index coordinate) =
      frame.vectorAt (patch.coordinateMap coordinate) index := by
  rw [finiteFramePulledVector, VectorField.mpullback_apply]
  exact (coordinateDerivative_isInvertible period hPeriod patch coordinate).self_apply_inverse _

theorem finiteFramePulledVector_contDiff
    (frame : SmoothD8Frame period hPeriod) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Fin frame.count) :
    ContDiff Real ∞ (finiteFramePulledVector period hPeriod frame patch index) := by
  have hBundle := (frame.contMDiff_vector index).mpullback_vectorField patch.coordinateMap_contMDiff
    (fun coordinate => coordinateDerivative_isInvertible period hPeriod patch coordinate) (by simp)
  exact ((contMDiff_snd_tangentBundle_modelSpace Vector4
    (modelWithCornersSelf Real Vector4)).comp hBundle).contDiff

theorem fderiv_comp_coordinateMap_finiteFramePulledVector
    (frame : SmoothD8Frame period hPeriod) (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (direction : Fin frame.count) :
    fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate
        (finiteFramePulledVector period hPeriod frame patch direction coordinate) =
      frameDerivative period hPeriod Real frame field (patch.coordinateMap coordinate) direction := by
  let vector := finiteFramePulledVector period hPeriod frame patch direction coordinate
  have hChain := mfderiv_comp_apply coordinate
    (field.contMDiff_toFun.mdifferentiableAt (by simp))
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp)) vector
  have hChainReal := congrArg
    (NormedSpace.fromTangentSpace (field.toFun (patch.coordinateMap coordinate))) hChain
  have hLeft : fderiv Real (field.toFun ∘ patch.coordinateMap) coordinate vector =
      NormedSpace.fromTangentSpace (field.toFun (patch.coordinateMap coordinate))
        (mfderiv (modelWithCornersSelf Real Vector4) (modelWithCornersSelf Real Real)
          (field.toFun ∘ patch.coordinateMap) coordinate vector) := by
    rw [mfderiv_eq_fderiv]
    rfl
  have hRight : NormedSpace.fromTangentSpace (field.toFun (patch.coordinateMap coordinate))
      (mfderiv coverModelWithCorners (modelWithCornersSelf Real Real) field.toFun
        (patch.coordinateMap coordinate)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate vector)) =
      frameDerivative period hPeriod Real frame field (patch.coordinateMap coordinate) direction := by
    rw [coordinateMap_mfderiv_finiteFramePulledVector, frameDerivative_eq_mfderiv]
    rfl
  exact hLeft.trans (hChainReal.trans hRight)

/-- The supplied metric's actual local covariant derivative of two generators. -/
def finiteFrameLocalCovariantDerivativeVector
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) : Vector4 :=
  fderiv Real (finiteFramePulledVector period hPeriod frame patch second) coordinate
      (finiteFramePulledVector period hPeriod frame patch first coordinate) +
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch first coordinate)
      (finiteFramePulledVector period hPeriod frame patch second coordinate)

/-- Canonical redundant coefficients of that connection vector. -/
def finiteFrameTensorChristoffelCoefficient
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (upper first second : Fin frame.count) : Real :=
  generalMetricFiniteFrameCoefficientAt period hPeriod frame reference
    (patch.coordinateMap coordinate) upper
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners patch.coordinateMap coordinate
      (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate first second))

theorem finiteFrameLocalCovariantDerivativeVector_reconstructs
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) :
    finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate first second =
      ∑ upper : Fin frame.count,
        finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
          upper first second • finiteFramePulledVector period hPeriod frame patch upper coordinate := by
  let e := (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  have hVector (upper : Fin frame.count) :
      e (finiteFramePulledVector period hPeriod frame patch upper coordinate) =
        frame.vectorAt (patch.coordinateMap coordinate) upper :=
    (coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch coordinate _).symm.trans
      (coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate upper)
  have hCoefficient (upper : Fin frame.count) :
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
          upper first second =
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference (patch.coordinateMap coordinate)
          upper (e (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
            first second)) :=
    congrArg (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference
      (patch.coordinateMap coordinate) upper)
      (coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch coordinate _)
  apply e.injective
  rw [map_sum]
  simp_rw [map_smul, hVector, hCoefficient]
  exact generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod frame reference
    (patch.coordinateMap coordinate) _

private theorem tensorForm_frame
    (frame : SmoothD8Frame period hPeriod) (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) :
    localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch coordinate
        (finiteFramePulledVector period hPeriod frame patch first coordinate)
        (finiteFramePulledVector period hPeriod frame patch second coordinate) =
      generalMetricFrameCoefficient period hPeriod frame tensor first second
        (patch.coordinateMap coordinate) := by
  rw [localSymmetricTensorCoordinateForm_apply, coordinateMap_mfderiv_finiteFramePulledVector,
    coordinateMap_mfderiv_finiteFramePulledVector]
  rfl

/-- The actual covariant derivative has both connection corrections in the redundant family. -/
theorem localSymmetricTensorCovariantDerivativeApply_eq_finiteFrame
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (derivative first second : Fin frame.count) :
    localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor.tensor patch coordinate
        (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
        (finiteFramePulledVector period hPeriod frame patch first coordinate)
        (finiteFramePulledVector period hPeriod frame patch second coordinate) =
      frameDerivative period hPeriod Real frame
          (generalMetricFrameCoefficient period hPeriod frame tensor first second)
          (patch.coordinateMap coordinate) derivative -
        (∑ index : Fin frame.count,
          finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
              index derivative first *
            generalMetricFrameCoefficient period hPeriod frame tensor index second (patch.coordinateMap coordinate)) -
        ∑ index : Fin frame.count,
          finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
              index derivative second *
            generalMetricFrameCoefficient period hPeriod frame tensor first index (patch.coordinateMap coordinate) := by
  let left := finiteFramePulledVector period hPeriod frame patch first
  let right := finiteFramePulledVector period hPeriod frame patch second
  let direction := finiteFramePulledVector period hPeriod frame patch derivative coordinate
  let form := localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch coordinate
  let connection := fun index =>
    finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate derivative index
  have hProduct : fderiv Real (fun current =>
      localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch current
        (left current) (right current)) coordinate direction =
      form (fderiv Real left coordinate direction) (right coordinate) +
        localSymmetricTensorDerivativeTrilinearForm period hPeriod tensor.tensor patch coordinate
          direction (left coordinate) (right coordinate) +
        form (left coordinate) (fderiv Real right coordinate direction) := by
    exact fderiv_matrix_toBilin_dynamic_apply
      (localSymmetricTensorMatrix period hPeriod tensor.tensor patch) left right coordinate direction
      ((localSymmetricTensorMatrix_contDiff period hPeriod tensor.tensor patch).differentiable
        (by simp) coordinate)
      ((finiteFramePulledVector_contDiff period hPeriod frame patch first).differentiable (by simp) coordinate)
      ((finiteFramePulledVector_contDiff period hPeriod frame patch second).differentiable (by simp) coordinate)
  have hFunction : (fun current => localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch
      current (left current) (right current)) =
      (generalMetricFrameCoefficient period hPeriod frame tensor first second).toFun ∘ patch.coordinateMap := by
    funext current
    exact tensorForm_frame period hPeriod frame tensor patch current first second
  rw [hFunction, fderiv_comp_coordinateMap_finiteFramePulledVector] at hProduct
  have hLeft : form (connection first) (right coordinate) = ∑ index : Fin frame.count,
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
        index derivative first *
      generalMetricFrameCoefficient period hPeriod frame tensor index second (patch.coordinateMap coordinate) := by
    rw [show connection first = _ from finiteFrameLocalCovariantDerivativeVector_reconstructs
      period hPeriod frame reference metric patch coordinate derivative first]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun value : Real =>
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
        index derivative first * value) (tensorForm_frame period hPeriod frame tensor patch coordinate index second)
  have hRight : form (left coordinate) (connection second) = ∑ index : Fin frame.count,
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
        index derivative second *
      generalMetricFrameCoefficient period hPeriod frame tensor first index (patch.coordinateMap coordinate) := by
    rw [show connection second = _ from finiteFrameLocalCovariantDerivativeVector_reconstructs
      period hPeriod frame reference metric patch coordinate derivative second]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun value : Real =>
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
        index derivative second * value) (tensorForm_frame period hPeriod frame tensor patch coordinate first index)
  rw [← hLeft, ← hRight]
  have hLeftExpand : form (connection first) (right coordinate) =
      form (fderiv Real left coordinate direction) (right coordinate) +
        form (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate direction
          (left coordinate)) (right coordinate) := by
    change form (fderiv Real left coordinate direction + localLeviCivitaChristoffelApply period hPeriod
      metric patch coordinate direction (left coordinate)) (right coordinate) = _
    rw [map_add, LinearMap.add_apply]
  have hRightExpand : form (left coordinate) (connection second) =
      form (left coordinate) (fderiv Real right coordinate direction) +
        form (left coordinate) (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          direction (right coordinate)) := map_add (form (left coordinate)) _ _
  rw [hLeftExpand, hRightExpand]
  unfold localSymmetricTensorCovariantDerivativeApply
  dsimp only [form, left, right, direction] at hProduct ⊢
  linarith [hProduct]

private theorem bilinear_contraction_eq_finiteFrame
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real (TangentFiber period hPeriod point))
    (form : LinearMap.BilinForm Real (TangentFiber period hPeriod point)) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      (LinearMap.BilinForm.toMatrix basis (metric.tensor.tensor point).toBilinForm)⁻¹ first second *
        form (basis first) (basis second)) =
      ∑ first : Fin frame.count, ∑ second : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric first second point *
          form (frame.vectorAt point first) (frame.vectorAt point second) := by
  let covector : TangentFiber period hPeriod point →ₗ[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
    (LinearMap.toContinuousLinearMap :
      (TangentFiber period hPeriod point →ₗ[Real] Real) ≃ₗ[Real]
        (TangentFiber period hPeriod point →L[Real] Real)).toLinearMap.comp form
  let operator := (inverseMetricSharp period hPeriod metric point).toLinearMap.comp covector
  let metricForm : LinearMap.BilinForm Real (TangentFiber period hPeriod point) :=
    (metric.tensor.tensor point).toBilinForm
  have hNondegenerate : metricForm.Nondegenerate := by
    constructor
    · intro vector hVector
      apply metric_nondegenerate_at period hPeriod metric
      apply ContinuousLinearMap.ext
      intro second
      exact (hVector second).trans (by simp only [map_zero, zero_apply])
    · intro vector hVector
      apply metric_nondegenerate_at period hPeriod metric
      apply ContinuousLinearMap.ext
      intro second
      rw [metric.tensor.symmetric]
      exact (hVector second).trans (by simp only [map_zero, zero_apply])
  have hRaised (first second : TangentFiber period hPeriod point) :
      metricForm (operator first) second = form first second := by
    change metric.tensor.tensor point
      (inverseMetricSharp period hPeriod metric point (covector first)) second = _
    rw [← metric.musical_eq_tensor]
    exact congrArg (fun value => value second)
      (metric_flat_inverseMetricSharp period hPeriod metric point (covector first))
  have hBasis := trace_eq_inverse_gram_contraction basis metricForm hNondegenerate
    (fun first second => metric.tensor.symmetric point first second) operator
  have hBasisValue : LinearMap.trace Real (TangentFiber period hPeriod point) operator =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (LinearMap.BilinForm.toMatrix basis metricForm)⁻¹ first second * form (basis first) (basis second) :=
    hBasis.trans (by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      exact congrArg (fun value : Real =>
        (LinearMap.BilinForm.toMatrix basis metricForm)⁻¹ first second * value)
        (hRaised (basis first) (basis second)))
  refine hBasisValue.symm.trans ((finiteFrame_endomorphism_trace period hPeriod frame reference point operator).trans ?_)
  apply Finset.sum_congr rfl
  intro first _
  have hCovector := congrArg
    (fun value : TangentFiber period hPeriod point →L[Real] Real =>
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point first
        (inverseMetricSharp period hPeriod metric point value))
    (finiteFrameCovector_reconstructs period hPeriod frame reference point
      (covector (frame.vectorAt point first)))
  simp only [map_sum, map_smul, smul_eq_mul] at hCovector
  change generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point first
    (inverseMetricSharp period hPeriod metric point (covector (frame.vectorAt point first))) = _
  rw [hCovector]
  apply Finset.sum_congr rfl
  intro second _
  rw [finiteFrameInverseMetricCoefficient_apply]
  exact mul_comm _ _

private theorem modelDivergence_eq_contraction
    (metric : SmoothGeneralLorentzMetric period hPeriod) (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate last : Vector4) :
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch coordinate last =
      matrixEntryContraction (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
        (localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric tensor patch coordinate last) := by
  let contraction : Vector4 →ₗ[Real] Real := ∑ derivative : Fin 4, ∑ first : Fin 4,
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ derivative first •
      localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod metric tensor patch coordinate
        (Pi.single derivative 1) (Pi.single first 1)
  have hMap : (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch
      coordinate).toLinearMap = contraction := by
    apply (Pi.basisFun Real (Fin 4)).ext
    intro index
    rw [Pi.basisFun_apply]
    have hBasis := localSymmetricTensorDivergenceModelCovector_basis period hPeriod metric tensor patch coordinate index
    change localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch coordinate
      (Pi.single index 1) = _ at hBasis
    change localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch coordinate
      (Pi.single index 1) = _
    rw [hBasis]
    simp only [contraction, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      localSymmetricTensorCovariantDerivativeTrilinearForm_apply,
      localSymmetricTensorCovariantDerivativeApply_basis]
    rfl
  calc
    _ = contraction last := congrArg (fun map : Vector4 →ₗ[Real] Real => map last) hMap
    _ = _ := by
      simp only [contraction, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        localSymmetricTensorCovariantDerivativeTrilinearForm_apply, matrixEntryContraction]
      apply Finset.sum_congr rfl
      intro derivative _
      apply Finset.sum_congr rfl
      intro first _
      rw [localSymmetricTensorCovariantDerivativeSliceMatrix_apply]
      rfl

/-- The genuine global divergence, contracted with the reconstructed finite dual. -/
theorem globalGeneralMetricSymmetricTensorDivergence_eq_finiteFrameCovariantTrace
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) (last : Fin frame.count) :
    globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor.tensor
        (patch.coordinateMap coordinate) (frame.vectorAt (patch.coordinateMap coordinate) last) =
      ∑ derivative : Fin frame.count, ∑ first : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric derivative first
          (patch.coordinateMap coordinate) *
        (frameDerivative period hPeriod Real frame
            (generalMetricFrameCoefficient period hPeriod frame tensor first last)
            (patch.coordinateMap coordinate) derivative -
          (∑ index : Fin frame.count,
            finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
              index derivative first * generalMetricFrameCoefficient period hPeriod frame tensor index last
                (patch.coordinateMap coordinate)) -
          ∑ index : Fin frame.count,
            finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
              index derivative last * generalMetricFrameCoefficient period hPeriod frame tensor first index
                (patch.coordinateMap coordinate)) := by
  let e := (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  let vector := finiteFramePulledVector period hPeriod frame patch last coordinate
  let slice := localSymmetricTensorCovariantDerivativeSlice period hPeriod metric tensor.tensor patch coordinate vector
  let form := slice.comp e.symm.toLinearMap e.symm.toLinearMap
  have hFrame (index : Fin 4) : e.symm (patch.frame coordinate index) = Pi.single index 1 := by
    simp [e, Module.Basis.equiv_symm, Pi.basisFun_apply]
  have hPulled (index : Fin frame.count) :
      e.symm (frame.vectorAt (patch.coordinateMap coordinate) index) =
        finiteFramePulledVector period hPeriod frame patch index coordinate := by
    apply e.injective
    rw [e.apply_symm_apply]
    have hPush := coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate index
    rw [coordinateMap_mfderiv_eq_frameEquiv] at hPush
    exact hPush.symm
  have hGram : LinearMap.BilinForm.toMatrix (patch.frame coordinate)
      (metric.tensor.tensor (patch.coordinateMap coordinate)).toBilinForm =
      localMetricMatrix period hPeriod metric patch coordinate := by
    ext first second
    exact LinearMap.BilinForm.toMatrix_apply (b := patch.frame coordinate)
      (metric.tensor.tensor (patch.coordinateMap coordinate)).toBilinForm first second
  have hChange := bilinear_contraction_eq_finiteFrame period hPeriod frame reference metric
    (patch.coordinateMap coordinate) (patch.frame coordinate) form
  have hGramContraction := congrArg (fun matrix : Matrix (Fin 4) (Fin 4) Real =>
    ∑ first : Fin 4, ∑ second : Fin 4, matrix⁻¹ first second *
      form (patch.frame coordinate first) (patch.frame coordinate second)) hGram
  have hChangeLocal := hGramContraction.symm.trans hChange
  have hFormFrame (first second : Fin 4) : form (patch.frame coordinate first)
      (patch.frame coordinate second) = slice (Pi.single first 1) (Pi.single second 1) := by
    exact congrArg₂ (fun first second => slice first second) (hFrame first) (hFrame second)
  have hFormPulled (first second : Fin frame.count) :
      form (frame.vectorAt (patch.coordinateMap coordinate) first)
        (frame.vectorAt (patch.coordinateMap coordinate) second) =
      slice (finiteFramePulledVector period hPeriod frame patch first coordinate)
        (finiteFramePulledVector period hPeriod frame patch second coordinate) := by
    exact congrArg₂ (fun first second => slice first second) (hPulled first) (hPulled second)
  simp only [hFormFrame, hFormPulled] at hChangeLocal
  have hIntrinsic : globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor.tensor
      (patch.coordinateMap coordinate) (frame.vectorAt (patch.coordinateMap coordinate) last) =
      localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor.tensor patch coordinate vector := by
    rw [globalGeneralMetricSymmetricTensorDivergence_apply, globalGeneralMetricSymmetricTensorDivergenceAt_eq_local]
    rw [← coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate last,
      coordinateMap_mfderiv_eq_frameEquiv]
    exact localSymmetricTensorDivergenceIntrinsicCovector_frame period hPeriod metric tensor.tensor patch coordinate vector
  have hLocalSlice (derivative first : Fin 4) :
      localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric tensor.tensor patch
        coordinate vector derivative first = slice (Pi.single derivative 1) (Pi.single first 1) := by
    rw [localSymmetricTensorCovariantDerivativeSliceMatrix_apply]
    rfl
  rw [hIntrinsic, modelDivergence_eq_contraction]
  simp only [matrixEntryContraction, hLocalSlice]
  refine hChangeLocal.trans ?_
  apply Finset.sum_congr rfl
  intro derivative _
  apply Finset.sum_congr rfl
  intro first _
  congr 1
  exact localSymmetricTensorCovariantDerivativeApply_eq_finiteFrame period hPeriod frame reference metric
    tensor patch coordinate derivative first last

end
end P0EFTJanusFiniteFrameCovariantTensorDivergence4D
end JanusFormal
