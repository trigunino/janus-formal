import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameLorenzCovariantTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

/-! # Tensor divergence in an independent regular frame

The genuine covariant derivative supplies both connection corrections.
Changing the two contracted slots to the reference frame leaves their
inverse-metric contraction unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameSymmetricTensorDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusRegularFrameLorenzCovariantTrace4D

private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The actual tensor paired with the two reference-frame vectors. -/
def regularFrameSymmetricTensorCoefficient
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Fin 4) : SmoothScalarField period hPeriod :=
  generalMetricFrameCoefficient period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor first second

@[simp] theorem regularFrameSymmetricTensorCoefficient_apply
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second point =
      tensor.tensor point (reference.frame first point) (reference.frame second point) := rfl

/-- Coefficients of the supplied metric's genuine connection in the reference frame. -/
def regularFrameTensorChristoffelCoefficient
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper first second : Fin 4) : Real :=
  (pulledRegularFrameBasis period hPeriod reference patch coordinate).repr
    (candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod reference metric patch first second coordinate) upper

private theorem tensorForm_frame
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Fin 4) :
    localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch coordinate
        (pulledRegularFrameVector period hPeriod reference patch first coordinate)
        (pulledRegularFrameVector period hPeriod reference patch second coordinate) =
      regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second
        (patch.coordinateMap coordinate) := by
  rw [localSymmetricTensorCoordinateForm_apply,
    coordinateMap_mfderiv_pulledRegularFrameVector,
    coordinateMap_mfderiv_pulledRegularFrameVector]
  rfl

/-- Both tensor slots contribute their connection term to the actual derivative. -/
theorem localSymmetricTensorCovariantDerivativeApply_eq_regularFrame
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Fin 4) :
    localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor.tensor patch
        coordinate (pulledRegularFrameVector period hPeriod reference patch derivative coordinate)
        (pulledRegularFrameVector period hPeriod reference patch first coordinate)
        (pulledRegularFrameVector period hPeriod reference patch second coordinate) =
      frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second)
          (patch.coordinateMap coordinate) derivative -
        (∑ index : Fin 4,
          regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch
              coordinate index derivative first *
            regularFrameSymmetricTensorCoefficient period hPeriod reference tensor index second
              (patch.coordinateMap coordinate)) -
        ∑ index : Fin 4,
          regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch
              coordinate index derivative second *
            regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first index
              (patch.coordinateMap coordinate) := by
  let left := pulledRegularFrameVector period hPeriod reference patch first
  let right := pulledRegularFrameVector period hPeriod reference patch second
  let direction := pulledRegularFrameVector period hPeriod reference patch derivative coordinate
  let form := localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch coordinate
  let basis := pulledRegularFrameBasis period hPeriod reference patch coordinate
  let connection := fun index =>
    candidateANormalBoundaryVariedRegularFrameLocalCovariantDerivativeVector
      period hPeriod reference metric patch derivative index coordinate
  have hProduct :
      fderiv Real (fun current =>
        localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch current
          (left current) (right current)) coordinate direction =
        form (fderiv Real left coordinate direction) (right coordinate) +
          localSymmetricTensorDerivativeTrilinearForm period hPeriod tensor.tensor patch
            coordinate direction (left coordinate) (right coordinate) +
          form (left coordinate) (fderiv Real right coordinate direction) := by
    exact fderiv_matrix_toBilin_dynamic_apply
      (localSymmetricTensorMatrix period hPeriod tensor.tensor patch) left right coordinate direction
      ((localSymmetricTensorMatrix_contDiff period hPeriod tensor.tensor patch).differentiable
        (by simp) coordinate)
      (pulledRegularFrameVector_differentiableAt period hPeriod reference patch coordinate first)
      (pulledRegularFrameVector_differentiableAt period hPeriod reference patch coordinate second)
  have hFunction :
      (fun current => localSymmetricTensorCoordinateForm period hPeriod tensor.tensor patch current
        (left current) (right current)) =
        (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second).toFun
          ∘ patch.coordinateMap := by
    funext current
    exact tensorForm_frame period hPeriod reference tensor patch current first second
  rw [hFunction, fderiv_comp_coordinateMap_pulledRegularFrameVector] at hProduct
  have hLeft : form (connection first) (right coordinate) =
      ∑ index : Fin 4,
        regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch
            coordinate index derivative first *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor index second
            (patch.coordinateMap coordinate) := by
    calc
      _ = form (∑ index : Fin 4, basis.repr (connection first) index • basis index)
          (right coordinate) :=
        congrArg (fun vector => form vector (right coordinate))
          (basis.sum_repr (connection first)).symm
      _ = _ := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro index _
        congr 1
        dsimp only [basis, form, right]
        rw [pulledRegularFrameBasis_apply, tensorForm_frame]
  have hRight : form (left coordinate) (connection second) =
      ∑ index : Fin 4,
        regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch
            coordinate index derivative second *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first index
            (patch.coordinateMap coordinate) := by
    calc
      _ = form (left coordinate)
          (∑ index : Fin 4, basis.repr (connection second) index • basis index) :=
        congrArg (form (left coordinate)) (basis.sum_repr (connection second)).symm
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro index _
        congr 1
        dsimp only [basis, form, left]
        rw [pulledRegularFrameBasis_apply, tensorForm_frame]
  rw [← hLeft, ← hRight]
  have hLeftExpand : form (connection first) (right coordinate) =
      form (fderiv Real left coordinate direction) (right coordinate) +
        form (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          direction (left coordinate)) (right coordinate) := by
    change form (fderiv Real left coordinate direction +
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate direction
        (left coordinate)) (right coordinate) = _
    rw [map_add, LinearMap.add_apply]
  have hRightExpand : form (left coordinate) (connection second) =
      form (left coordinate) (fderiv Real right coordinate direction) +
        form (left coordinate) (localLeviCivitaChristoffelApply period hPeriod metric patch
          coordinate direction (right coordinate)) := by
    exact map_add (form (left coordinate)) _ _
  rw [hLeftExpand, hRightExpand]
  unfold localSymmetricTensorCovariantDerivativeApply
  dsimp only [form, left, right, direction] at hProduct ⊢
  linarith [hProduct]

private theorem modelDivergence_eq_contraction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate last : Vector4) :
    localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch coordinate last =
      matrixEntryContraction (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
        (localSymmetricTensorCovariantDerivativeSliceMatrix period hPeriod metric tensor
          patch coordinate last) := by
  let contraction : Vector4 →ₗ[Real] Real :=
    ∑ derivative : Fin 4, ∑ first : Fin 4,
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ derivative first •
        localSymmetricTensorCovariantDerivativeTrilinearForm period hPeriod metric tensor
          patch coordinate (Pi.single derivative 1) (Pi.single first 1)
  have hMap :
      (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch
        coordinate).toLinearMap = contraction := by
    apply (Pi.basisFun Real (Fin 4)).ext
    intro index
    rw [Pi.basisFun_apply]
    have hBasis := localSymmetricTensorDivergenceModelCovector_basis period hPeriod
      metric tensor patch coordinate index
    change localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch
      coordinate (Pi.single index 1) = _ at hBasis
    change localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor patch
      coordinate (Pi.single index 1) = _
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

private theorem contraction_change_frame
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (metric tensor : LinearMap.BilinForm Real Vector4) :
    matrixEntryContraction (LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) metric)⁻¹
        (LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) tensor) =
      matrixEntryContraction
        (LinearMap.BilinForm.toMatrix
          (pulledRegularFrameBasis period hPeriod reference patch coordinate) metric)⁻¹
        (LinearMap.BilinForm.toMatrix
          (pulledRegularFrameBasis period hPeriod reference patch coordinate) tensor) := by
  have hCongruence := matrixEntryContraction_congruence
    (regularFrameChangeMatrix period hPeriod reference patch coordinate)
    (LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) metric)
    (LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) tensor)
    (regularFrameChangeMatrix_isUnit period hPeriod reference patch coordinate)
  simpa only [regularFrameChangeMatrix, LinearMap.BilinForm.toMatrix_mul_basis_toMatrix]
    using hCongruence.symm

/-- Gate 648: the genuine global divergence has the full fixed-frame tensor formula. -/
theorem globalGeneralMetricSymmetricTensorDivergence_eq_regularFrameCovariantTrace
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (last : Fin 4) :
    globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor.tensor
        (patch.coordinateMap coordinate) (reference.frame last (patch.coordinateMap coordinate)) =
      ∑ derivative : Fin 4, ∑ first : Fin 4,
        (regularFrameLorenzMetricMatrix period hPeriod reference metric
          (patch.coordinateMap coordinate))⁻¹ derivative first *
          (frameDerivative period hPeriod Real
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
              (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first last)
              (patch.coordinateMap coordinate) derivative -
            (∑ index : Fin 4,
              regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch
                  coordinate index derivative first *
                regularFrameSymmetricTensorCoefficient period hPeriod reference tensor index last
                  (patch.coordinateMap coordinate)) -
            ∑ index : Fin 4,
              regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch
                  coordinate index derivative last *
                regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first index
                  (patch.coordinateMap coordinate)) := by
  let basis := pulledRegularFrameBasis period hPeriod reference patch coordinate
  let form := localMetricCoordinateForm period hPeriod metric patch coordinate
  let vector := pulledRegularFrameVector period hPeriod reference patch last coordinate
  let slice := localSymmetricTensorCovariantDerivativeSlice period hPeriod metric tensor.tensor
    patch coordinate vector
  have hLocal : LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form =
      localMetricMatrix period hPeriod metric patch coordinate := by
    exact LinearMap.BilinForm.toMatrix'_toBilin' _
  have hGram : LinearMap.BilinForm.toMatrix basis form =
      regularFrameLorenzMetricMatrix period hPeriod reference metric
        (patch.coordinateMap coordinate) := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    dsimp only [basis, form]
    rw [pulledRegularFrameBasis_apply, pulledRegularFrameBasis_apply,
      localMetricCoordinateForm_apply, coordinateMap_mfderiv_pulledRegularFrameVector,
      coordinateMap_mfderiv_pulledRegularFrameVector]
    rfl
  have hIntrinsic :
      globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor.tensor
          (patch.coordinateMap coordinate)
          (reference.frame last (patch.coordinateMap coordinate)) =
        localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor.tensor
          patch coordinate vector := by
    rw [globalGeneralMetricSymmetricTensorDivergence_apply,
      globalGeneralMetricSymmetricTensorDivergenceAt_eq_local]
    rw [← coordinateMap_mfderiv_pulledRegularFrameVector period hPeriod reference patch
      coordinate last, coordinateMap_mfderiv_eq_frameEquiv]
    exact localSymmetricTensorDivergenceIntrinsicCovector_frame period hPeriod metric
      tensor.tensor patch coordinate vector
  rw [hIntrinsic, modelDivergence_eq_contraction, ← hLocal]
  have hChange := contraction_change_frame period hPeriod reference patch coordinate form slice
  change matrixEntryContraction
    (LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form)⁻¹
    (LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) slice) = _
  refine hChange.trans ?_
  change matrixEntryContraction (LinearMap.BilinForm.toMatrix basis form)⁻¹
    (LinearMap.BilinForm.toMatrix basis slice) = _
  rw [hGram]
  unfold matrixEntryContraction
  apply Finset.sum_congr rfl
  intro derivative _
  apply Finset.sum_congr rfl
  intro first _
  congr 1
  rw [LinearMap.BilinForm.toMatrix_apply]
  change localSymmetricTensorCovariantDerivativeApply period hPeriod metric tensor.tensor
    patch coordinate (basis derivative) (basis first) vector = _
  dsimp only [basis, vector]
  rw [pulledRegularFrameBasis_apply, pulledRegularFrameBasis_apply]
  exact localSymmetricTensorCovariantDerivativeApply_eq_regularFrame period hPeriod reference
    metric tensor patch coordinate derivative first last

end
end P0EFTJanusRegularFrameSymmetricTensorDivergence4D
end JanusFormal
