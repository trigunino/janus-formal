import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D

/-! # Canonical volume on the relative finite-frame C² metric domain

The absolute value of the regular scalar root supplies a positive density.
Its smooth realization uses the intrinsic determinant of `id + g⁻¹h` and
holonomic volume comparisons; no global tangent basis is required.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2CanonicalVolume4D

set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D
open P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D

private theorem bilinear_gram_det_compLeft
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 4) Real V) (base actual : LinearMap.BilinForm Real V)
    (operator : V →ₗ[Real] V)
    (hPairing : ∀ first second, base (operator first) second = actual first second) :
    Matrix.det (LinearMap.BilinForm.toMatrix basis actual) =
      Matrix.det (LinearMap.BilinForm.toMatrix basis base) * LinearMap.det operator := by
  have hForm : base.compLeft operator = actual := by
    apply LinearMap.ext
    intro first
    apply LinearMap.ext
    intro second
    exact hPairing first second
  have hMatrix := LinearMap.BilinForm.toMatrix_compLeft (b := basis) base operator
  rw [hForm] at hMatrix
  have hDet := congrArg Matrix.det hMatrix
  rw [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hDet
  exact hDet.trans (mul_comm _ _)

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- Scalar Sylvester regularity forces every continuous value to be nonzero. -/
theorem regularScalarC2Root_continuous_ne_zero (root : C2Scalar period hPeriod)
    (hRegular : root ∈ c2ScalarSylvesterRegularSet period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod root point ≠ 0 := by
  rcases hRegular with ⟨equiv, hEquiv⟩
  have hOne : c2ScalarSylvesterFamily period hPeriod root
      (equiv.symm (c2ScalarOne period hPeriod)) = c2ScalarOne period hPeriod := by
    rw [← hEquiv]
    exact equiv.apply_symm_apply _
  have hValue := congrArg (fun value : C2Scalar period hPeriod =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod value point) hOne
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod root point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (equiv.symm (c2ScalarOne period hPeriod)) point +
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (equiv.symm (c2ScalarOne period hPeriod)) point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod root point = 1 at hValue
  intro hZero
  rw [hZero] at hValue
  norm_num at hValue

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "Domain" => generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric

theorem finiteFrameVolumeRoot_continuous_ne_zero
    (variation : Model) (hVariation : variation ∈ Domain) (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric variation) point ≠ 0 := by
  have hSource := (c2ScalarLocalSquareChart period hPeriod).map_target hVariation.2
  rw [c2ScalarLocalSquareChart, OpenPartialHomeomorph.restrOpen_source] at hSource
  exact regularScalarC2Root_continuous_ne_zero period hPeriod _ hSource.2 point

/-- Canonical base density times the positive relative volume factor. -/
def finiteFrameCanonicalVolumeC0 (variation : Model) : C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (globalSmoothMetricVolumeRatio period hPeriod baseMetric) *
    continuousScalarAbs (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric variation))

theorem finiteFrameCanonicalVolumeC0_contDiffOn_two :
    ContDiffOn Real 2 (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric) Domain := by
  have hRoot := (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp_contDiffOn
    (generalMetricRelativeC2VolumeRatio_contDiffOn_two period hPeriod frame baseMetric)
  intro variation hVariation
  apply ContDiffWithinAt.mul contDiffWithinAt_const
  exact (continuousScalarAbs_contDiffAt 2 _
    (finiteFrameVolumeRoot_continuous_ne_zero period hPeriod frame baseMetric variation hVariation)).comp_contDiffWithinAt
      variation (hRoot variation hVariation)

theorem finiteFrameCanonicalVolumeC0_pos
    (variation : Model) (hVariation : variation ∈ Domain) (point : EffectiveQuotient period hPeriod) :
    0 < finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point :=
  mul_pos (globalMetricVolumeRatio_pos period hPeriod baseMetric point)
    (abs_pos.mpr (finiteFrameVolumeRoot_continuous_ne_zero period hPeriod frame baseMetric
      variation hVariation point))

theorem finiteFrameCanonicalVolumeC0_zero :
    finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric 0 =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod (globalSmoothMetricVolumeRatio period hPeriod baseMetric) := by
  apply ContinuousMap.ext
  intro point
  unfold finiteFrameCanonicalVolumeC0
  rw [generalMetricRelativeC2VolumeRatio_zero]
  change globalMetricVolumeRatio period hPeriod baseMetric point * |(1 : Real)| = _
  simp only [abs_one, mul_one]
  rfl

/-- The completed determinant on smooth inputs is the genuine tangent determinant. -/
theorem finiteFrameRelativeC2Determinant_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2Determinant period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor)) point =
    LinearMap.det ((ContinuousLinearMap.id Real (TangentFiber period hPeriod point) +
      raisedGeneralMetricTensorAt period hPeriod baseMetric tensor point).toLinearMap) := by
  let raised := raisedGeneralMetricTensorAt period hPeriod baseMetric tensor point
  let operator := ContinuousLinearMap.id Real (TangentFiber period hPeriod point) + raised
  have hReadout : Matrix.of (fun row column => canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2ExtendedMatrix period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) row column) point) =
      (1 : Matrix (Fin frame.count) (Fin frame.count) Real) +
        Matrix.of (fun row column => smoothGeneralMetricRelativeEndomorphismMatrix
          period hPeriod frame baseMetric tensor row column point) := by
    ext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (c2FiniteMatrixIdentity period hPeriod frame.count row column +
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame baseMetric tensor row column)) point = _
    rw [map_add]
    rfl
  have hExtended := hReadout.trans (congrArg
    (fun matrix : Matrix (Fin frame.count) (Fin frame.count) Real => 1 + matrix)
      (smoothGeneralMetricRelativeEndomorphismMatrix_apply period hPeriod frame baseMetric tensor point))
  have hEncoding : 1 - finiteFrameProjectorMatrixAt period hPeriod frame baseMetric point +
      finiteFrameEndomorphismMatrixAt period hPeriod frame baseMetric point operator =
      (1 : Matrix (Fin frame.count) (Fin frame.count) Real) +
        finiteFrameEndomorphismMatrixAt period hPeriod frame baseMetric point raised := by
    ext row column
    change (1 : Matrix (Fin frame.count) (Fin frame.count) Real) row column -
        generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric point row (frame.vectorAt point column) +
      generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric point row
        (frame.vectorAt point column + raised (frame.vectorAt point column)) = _
    rw [map_add]
    ring_nf
    rfl
  have hDet := (congrArg Matrix.det hEncoding).symm.trans
    (finiteFrameEndomorphismMatrixAt_extended_det period hPeriod frame baseMetric point operator)
  unfold generalMetricRelativeC2Determinant
  rw [c2FiniteMatrixDeterminant_continuous_apply]
  exact (congrArg Matrix.det hExtended).trans hDet

/-- Exact canonical volume for every smooth admissible affine metric. -/
theorem finiteFrameCanonicalVolumeC0_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor ∈ Domain) :
    finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) =
    smoothToCanonicalPhysicalContinuousScalar period hPeriod (globalSmoothMetricVolumeRatio period hPeriod metric) := by
  apply ContinuousMap.ext
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with ⟨patch, coordinate, hPoint⟩
  rw [← hPoint]
  let current := patch.coordinateMap coordinate
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor
  let operator := ContinuousLinearMap.id Real (TangentFiber period hPeriod current) +
    raisedGeneralMetricTensorAt period hPeriod baseMetric tensor current
  let root := canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric variation) current
  have hSquare := congrArg (fun value : C2Scalar period hPeriod =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod value current)
      (generalMetricRelativeC2VolumeRatio_square period hPeriod frame baseMetric variation hVariation)
  have hRootSquare : root * root = LinearMap.det operator.toLinearMap :=
    hSquare.trans (finiteFrameRelativeC2Determinant_smooth period hPeriod frame baseMetric tensor current)
  let baseForm : LinearMap.BilinForm Real (TangentFiber period hPeriod current) :=
    (baseMetric.tensor.tensor current).toBilinForm
  let actualForm : LinearMap.BilinForm Real (TangentFiber period hPeriod current) :=
    (metric.tensor.tensor current).toBilinForm
  have hPairing (first second : TangentFiber period hPeriod current) :
      baseForm (operator first) second = actualForm first second := by
    have hRaised : baseMetric.tensor.tensor current
        (raisedGeneralMetricTensorAt period hPeriod baseMetric tensor current first) second =
        tensor.tensor current first second := by
      rw [← baseMetric.musical_eq_tensor]
      exact congrArg (fun value => value second)
        ((baseMetric.musical current).apply_symm_apply (tensor.tensor current first))
    change baseMetric.tensor.tensor current
      (first + raisedGeneralMetricTensorAt period hPeriod baseMetric tensor current first) second = _
    rw [map_add, add_apply, hRaised]
    exact (congrArg (fun value : SmoothSymmetricCovariantTwoTensor period hPeriod =>
      value.tensor current first second) hMetric).symm
  have hGram (value : SmoothGeneralLorentzMetric period hPeriod) :
      LinearMap.BilinForm.toMatrix (patch.frame coordinate) (value.tensor.tensor current).toBilinForm =
        localMetricMatrix period hPeriod value patch coordinate := by
    ext first second
    exact LinearMap.BilinForm.toMatrix_apply (b := patch.frame coordinate)
      (value.tensor.tensor current).toBilinForm first second
  have hDetForm := bilinear_gram_det_compLeft (patch.frame coordinate) baseForm actualForm
    operator.toLinearMap hPairing
  have hDet : Matrix.det (localMetricMatrix period hPeriod metric patch coordinate) =
      Matrix.det (localMetricMatrix period hPeriod baseMetric patch coordinate) * (root * root) :=
    (congrArg Matrix.det (hGram metric)).symm.trans (hDetForm.trans
      ((congrArg (fun value : Real => value * LinearMap.det operator.toLinearMap)
        (congrArg Matrix.det (hGram baseMetric))).trans
          (congrArg (fun value : Real =>
            Matrix.det (localMetricMatrix period hPeriod baseMetric patch coordinate) * value) hRootSquare.symm)))
  have hDensity : |root| * localMetricVolumeFactor period hPeriod baseMetric patch coordinate =
      localMetricVolumeFactor period hPeriod metric patch coordinate := by
    unfold localMetricVolumeFactor
    rw [hDet, abs_mul, abs_of_nonneg (mul_self_nonneg root),
      Real.sqrt_mul (abs_nonneg _), Real.sqrt_mul_self_eq_abs]
    exact mul_comm _ _
  have hBase := globalMetricVolumeRatio_mul_intrinsic_density period hPeriod baseMetric patch coordinate
  have hActual := globalMetricVolumeRatio_mul_intrinsic_density period hPeriod metric patch coordinate
  simp only [← localMetricVolumeFactor_eq_metricVolumeDensity] at hBase hActual
  change globalMetricVolumeRatio period hPeriod baseMetric current * |root| =
    globalMetricVolumeRatio period hPeriod metric current
  apply mul_right_cancel₀
    (localMetricVolumeFactor_ne_zero period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
  calc
    _ = |root| * (globalMetricVolumeRatio period hPeriod baseMetric current *
        localMetricVolumeFactor period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate) := by ring
    _ = |root| * localMetricVolumeFactor period hPeriod baseMetric patch coordinate := by rw [hBase]
    _ = localMetricVolumeFactor period hPeriod metric patch coordinate := hDensity
    _ = _ := hActual.symm

end
end P0EFTJanusFiniteFrameC2CanonicalVolume4D
end JanusFormal
