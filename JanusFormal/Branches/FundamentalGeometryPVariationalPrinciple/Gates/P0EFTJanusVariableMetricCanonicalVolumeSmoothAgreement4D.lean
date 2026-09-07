import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricCanonicalVolumeRatio4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalReferenceDensity4D

/-! # Exact canonical-volume realization on smooth metric variations

The relative determinant multiplies the base Gram determinant to give the actual
Gram determinant. Its absolute square root therefore gives the true canonical
volume ratio, independently of the stored regular-frame volume.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameCanonicalReferenceDensity4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CommMonoid (C2Scalar period hPeriod) where
  mul := fun first second => canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second
  one := c2ScalarOne period hPeriod
  mul_assoc := c2ScalarProduct_assoc period hPeriod
  one_mul := c2ScalarOne_mul period hPeriod
  mul_one := c2Scalar_mul_one period hPeriod
  mul_comm := c2ScalarProduct_comm period hPeriod

/-- Evaluation commutes with the completed finite determinant polynomial. -/
theorem c2FiniteMatrixDeterminant_continuous_apply (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2FiniteMatrixDeterminant period hPeriod dimension matrix) point =
      Matrix.det (fun row column =>
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (matrix row column) point) := by
  classical
  let evaluate : C2Scalar period hPeriod →* Real :=
    { toFun := fun value => canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod value point
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  rw [Matrix.det_apply']
  simp only [c2FiniteMatrixDeterminant, map_sum, ContinuousMap.sum_apply,
    map_smul, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro permutation _
  change _ * evaluate (∏ index : Fin dimension, matrix (permutation index) index) = _
  rw [map_prod]
  rfl

private theorem relativeExtendedMatrix_continuous_apply
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod reference)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (generalMetricRelativeC2ExtendedMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          reference.metric variation row column) point =
      (1 : Matrix4) row column +
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (variation.1 row column) point := by
  unfold generalMetricRelativeC2ExtendedMatrix
  rw [Pi.add_apply, Pi.add_apply, map_add]
  simp only [ContinuousMap.add_apply]
  congr 1

/-- The canonical-volume comparison holds for a supplied metric in any fixed regular frame. -/
theorem globalMetricVolumeRatio_mul_fixedRegularFrameIntrinsicDensity
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod metric point *
        metricVolumeDensity period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          point (fun index => reference.frame index point) =
      metricVolumeDensity period hPeriod metric point
        (fun index => reference.frame index point) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  rw [metricVolumeDensity_regularFrame_eq_jacobian_mul_local period hPeriod
      reference (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate,
    metricVolumeDensity_regularFrame_eq_jacobian_mul_local period hPeriod
      reference metric patch coordinate]
  calc
    _ = regularFrameHolonomicJacobianWeight period hPeriod reference patch coordinate *
        (globalMetricVolumeRatio period hPeriod metric (patch.coordinateMap coordinate) *
          localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate) := by ring
    _ = _ := by
      rw [localMetricVolumeFactor_eq_metricVolumeDensity period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate,
        localMetricVolumeFactor_eq_metricVolumeDensity period hPeriod metric patch coordinate,
        globalMetricVolumeRatio_mul_intrinsic_density period hPeriod]

/-- The positive completed feature is exactly the true canonical ratio at every smooth metric. -/
theorem variableMetricCanonicalVolumeRatio_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference) :
    variableMetricCanonicalVolumeRatio period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothMetricVolumeRatio period hPeriod metric) := by
  apply ContinuousMap.ext
  intro point
  let variation := regularGeneralMetricSmoothC2Variation period hPeriod reference tensor
  let base := regularFrameMetricMatrixMap period hPeriod reference point
  let actual := regularFrameMetricMatrixFor period hPeriod reference metric point
  let relative : Matrix4 := fun row column =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (variation.1 row column) point
  let root := canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (generalMetricRelativeC2VolumeRatio period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
      reference.metric variation) point
  have hMatrix : base * (1 + relative) = actual := by
    ext row column
    exact (regularGeneralMetricC0MetricCoefficient_apply_expansion period hPeriod
      reference variation row column point).symm.trans
        ((candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
          period hPeriod reference tensor row column point).trans
            (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
              period hPeriod reference tensor metric hMetric row column point))
  have hSquare := congrArg (fun value : C2Scalar period hPeriod =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod value point)
      (generalMetricRelativeC2VolumeRatio_square period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        reference.metric variation hVariation)
  change root * root = canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (c2FiniteMatrixDeterminant period hPeriod 4
      (generalMetricRelativeC2ExtendedMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        reference.metric variation)) point at hSquare
  rw [c2FiniteMatrixDeterminant_continuous_apply] at hSquare
  have hExtended : (fun row column =>
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (generalMetricRelativeC2ExtendedMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          reference.metric variation row column) point) = (1 : Matrix4) + relative := by
    ext row column
    exact relativeExtendedMatrix_continuous_apply period hPeriod reference variation
      row column point
  have hSquareRelative : root * root = Matrix.det ((1 : Matrix4) + relative) :=
    hSquare.trans (congrArg (fun matrix : Matrix4 => matrix.det) hExtended)
  have hDeterminant : actual.det = base.det * (root * root) := by
    rw [← hMatrix, Matrix.det_mul, hSquareRelative]
  have hDensity : |root| * Real.sqrt |base.det| = Real.sqrt |actual.det| := by
    rw [hDeterminant, abs_mul, abs_of_nonneg (mul_self_nonneg root),
      Real.sqrt_mul (abs_nonneg _), Real.sqrt_mul_self_eq_abs]
    exact mul_comm _ _
  let referenceDensity := metricVolumeDensity period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
      (fun index => reference.frame index point)
  have hBase := globalMetricVolumeRatio_mul_fixedRegularFrameIntrinsicDensity period hPeriod
    reference reference.metric point
  have hActual := globalMetricVolumeRatio_mul_fixedRegularFrameIntrinsicDensity period hPeriod
    reference metric point
  change globalMetricVolumeRatio period hPeriod reference.metric point * referenceDensity =
    Real.sqrt |base.det| at hBase
  change globalMetricVolumeRatio period hPeriod metric point * referenceDensity =
    Real.sqrt |actual.det| at hActual
  have hReferenceNonzero : referenceDensity ≠ 0 := by
    intro hZero
    rw [hZero, mul_zero] at hBase
    exact (ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr
      (regularFrameMetricMatrix_det_ne_zero period hPeriod reference point)))) hBase.symm
  change globalMetricVolumeRatio period hPeriod reference.metric point * |root| =
    globalMetricVolumeRatio period hPeriod metric point
  apply mul_right_cancel₀ hReferenceNonzero
  calc
    _ = |root| * (globalMetricVolumeRatio period hPeriod reference.metric point *
      referenceDensity) := by ring
    _ = |root| * Real.sqrt |base.det| := by rw [hBase]
    _ = Real.sqrt |actual.det| := hDensity
    _ = _ := hActual.symm

end
end P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D
end JanusFormal
