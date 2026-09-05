import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D

/-! # Spatial compatibility of the smooth linearized Christoffel field -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialCompatibility4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseSpatialVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulSpatialVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Index4 := Fin 4

private abbrev Matrix4 := Matrix Index4 Index4 Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

private theorem frameDerivativeComponentField_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (0 : SmoothScalarField period hPeriod) derivative = 0 := by
  simpa using frameDerivativeComponentField_smul period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (0 : Real) (0 : SmoothScalarField period hPeriod) derivative

private theorem frameDerivativeComponentField_sub
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (first - second) derivative =
      frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          first derivative -
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          second derivative := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    show -second = (-1 : Real) • second by simp,
    frameDerivativeComponentField_add,
    frameDerivativeComponentField_smul]
  simp

private theorem frameDerivativeComponentField_mul_regular
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (smoothScalarFieldMul period hPeriod first second) derivative =
      smoothScalarFieldMul period hPeriod first
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            second derivative) +
        smoothScalarFieldMul period hPeriod second
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            first derivative) :=
  frameDerivativeComponentField_mul period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) first second
      derivative

private theorem frameDerivativeComponentField_finset_sum
    {ι : Type*} (metric : RegularGeneralLorentzMetric period hPeriod)
    (set : Finset ι) (fields : ι → SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (∑ index ∈ set, fields index) derivative =
      ∑ index ∈ set,
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (fields index) derivative := by
  classical
  induction set using Finset.induction_on with
  | empty =>
      simpa using frameDerivativeComponentField_zero period hPeriod metric
        derivative
  | @insert index set hIndex induction =>
      simp only [Finset.sum_insert hIndex]
      rw [frameDerivativeComponentField_add, induction]

private theorem frameDerivativeComponentField_univ_sum
    {ι : Type*} [Fintype ι]
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (fields : ι → SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (∑ index : ι, fields index) derivative =
      ∑ index : ι,
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (fields index) derivative := by
  simpa using frameDerivativeComponentField_finset_sum period hPeriod metric
    (Finset.univ : Finset ι) fields derivative

private theorem sum_product_rule_comm
    {ι : Type*} [Fintype ι]
    (first firstDerivative second secondDerivative : ι → Real) :
    (∑ index : ι,
        (first index * secondDerivative index +
          second index * firstDerivative index)) =
      ∑ index : ι,
        (firstDerivative index * second index +
          first index * secondDerivative index) := by
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- The explicit stored background inverse jet is the actual derivative of
the smooth inverse-metric coefficient. -/
theorem regularFrameMetricInverseMatrix_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative row column : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameMetricInverseMatrix period hPeriod metric row column)
        derivative =
      regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
        derivative row column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalTotalHolonomicAtlasCover_covers period hPeriod point with
    ⟨patch, _hPatch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  have hZero :
      smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) = 0 := by
    rw [map_zero]
  have hDomain :
      smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) ∈
      regularGeneralMetricC2Domain period hPeriod metric := by
    rw [hZero]
    exact zero_mem_regularGeneralMetricC2Domain period hPeriod metric
  have hLocal :=
    regularGeneralMetricC0InverseMetricCoefficient_smooth_local_fderiv
      period hPeriod metric 0 hDomain patch coordinate derivative row column
  rw [hZero] at hLocal
  have hFunction :
      (fun current =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
          row column (patch.coordinateMap current)) =
        (regularFrameMetricInverseMatrix period hPeriod metric row column).toFun ∘
          patch.coordinateMap := by
    funext current
    exact regularGeneralMetricC0InverseMetricCoefficient_zero_apply
      period hPeriod metric row column (patch.coordinateMap current)
  rw [hFunction,
    fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (regularFrameMetricInverseMatrix period hPeriod metric row column) patch
        coordinate derivative] at hLocal
  change frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameMetricInverseMatrix period hPeriod metric row column)
      (patch.coordinateMap coordinate) derivative = _
  rw [hLocal]
  have hStored := congrArg
    (fun field : C0Scalar period hPeriod => field (patch.coordinateMap coordinate))
    (regularGeneralMetricC0InverseMetricDerivative_zero_smooth period hPeriod
      metric derivative row column)
  exact hStored

private theorem regularFrameSmoothCovariantVariationCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric
          tensor row column) derivative =
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
        tensor derivative row column :=
  rfl

private theorem
    regularFrameSmoothCovariantVariationFirstDerivative_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod
          metric tensor inner row column) outer =
      regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
        tensor outer inner row column :=
  rfl

private theorem regularFrameStructureCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second upper : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameStructureCoefficient period hPeriod metric first second
          upper) derivative =
      regularFrameSmoothStructureCoefficientDerivative period hPeriod metric
        derivative first second upper :=
  rfl

/-- The stored spatial inverse velocity is the actual frame derivative of the
smooth inverse-metric velocity. -/
theorem regularFrameSmoothInverseVariationCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothInverseVariationCoefficient period hPeriod metric
          tensor row column) derivative =
      regularFrameSmoothInverseSpatialVariationCoefficient period hPeriod metric
        tensor derivative row column := by
  classical
  unfold regularFrameSmoothInverseVariationCoefficient
  rw [frameDerivativeComponentField_smul,
    frameDerivativeComponentField_univ_sum]
  simp_rw [frameDerivativeComponentField_mul_regular,
    frameDerivativeComponentField_univ_sum,
    frameDerivativeComponentField_mul_regular,
    regularFrameMetricInverseMatrix_frameDerivative,
    regularFrameSmoothCovariantVariationCoefficient_frameDerivative]
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change (-1 : Real) *
      (∑ second : Index4,
        ((∑ first : Index4,
            regularFrameMetricInverseMatrix period hPeriod metric row first point *
              regularFrameSmoothCovariantVariationCoefficient period hPeriod
                metric tensor first second point) *
            regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
              derivative second column point +
          regularFrameMetricInverseMatrix period hPeriod metric second column
              point *
            ∑ first : Index4,
              (regularFrameMetricInverseMatrix period hPeriod metric row first
                    point *
                  regularFrameSmoothCovariantVariationFirstDerivative period
                    hPeriod metric tensor derivative first second point +
                regularFrameSmoothCovariantVariationCoefficient period hPeriod
                    metric tensor first second point *
                  regularFrameSmoothInverseDerivativeCoefficient period hPeriod
                    metric derivative row first point))) =
    (-1 : Real) *
      ∑ first : Index4, ∑ second : Index4,
        (regularFrameSmoothInverseVariationCoefficient period hPeriod metric
              tensor row first point *
            regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod
              metric derivative first second point *
            regularFrameMetricInverseMatrix period hPeriod metric second column
              point +
          regularFrameMetricInverseMatrix period hPeriod metric row first point *
            regularFrameSmoothCovariantVariationFirstDerivative period hPeriod
              metric tensor derivative first second point *
            regularFrameMetricInverseMatrix period hPeriod metric second column
              point +
          regularFrameMetricInverseMatrix period hPeriod metric row first point *
            regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod
              metric derivative first second point *
            regularFrameSmoothInverseVariationCoefficient period hPeriod metric
              tensor second column point)
  let inverse : Matrix4 := fun first second =>
    regularFrameMetricInverseMatrix period hPeriod metric first second point
  let metricDerivative : Matrix4 := fun first second =>
    regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod metric
      derivative first second point
  let variation : Matrix4 := fun first second =>
    regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor
      first second point
  let variationDerivative : Matrix4 := fun first second =>
    regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
      tensor derivative first second point
  let inverseDerivative : Matrix4 := fun first second =>
    regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
      derivative first second point
  let inverseVariation : Matrix4 := fun first second =>
    regularFrameSmoothInverseVariationCoefficient period hPeriod metric tensor
      first second point
  have hInverseDerivative :
      inverseDerivative = -(inverse * metricDerivative * inverse) := by
    apply Matrix.ext
    intro first second
    change
      ((smoothToCanonicalPhysicalContinuousScalar period hPeriod)
          (regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
            derivative first second)) point = _
    have hMetricDerivative (currentRow currentColumn : Index4) :
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
            derivative currentRow currentColumn point =
          regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod
            metric derivative currentRow currentColumn point := by
      rw [regularGeneralMetricC0MetricFirstDerivative_zero_apply]
      rfl
    rw [← regularGeneralMetricC0InverseMetricDerivative_zero_smooth period hPeriod
      metric derivative first second]
    simp only [regularGeneralMetricC0InverseMetricDerivative,
      regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
      hMetricDerivative, Matrix.neg_apply, Matrix.mul_apply,
      ContinuousMap.neg_apply, ContinuousMap.sum_apply,
      ContinuousMap.mul_apply, inverse, metricDerivative]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  have hInverseVariation :
      inverseVariation = -(inverse * variation * inverse) := by
    ext first second
    simp only [inverseVariation, inverse, variation,
      regularFrameSmoothInverseVariationCoefficient_apply,
      regularFrameSmoothCovariantVariationCoefficient_apply,
      Matrix.neg_apply, Matrix.mul_apply]
  have hMatrix :
      -(inverseDerivative * variation * inverse +
          inverse * variationDerivative * inverse +
          inverse * variation * inverseDerivative) =
        -(inverseVariation * (metricDerivative * inverse) +
          inverse * (variationDerivative * inverse) +
          inverse * (metricDerivative * inverseVariation)) := by
    rw [hInverseDerivative, hInverseVariation]
    noncomm_ring
  have hEntry := congrFun (congrFun hMatrix row) column
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply] at hEntry
  change (-1 : Real) *
      (∑ second : Index4,
        ((∑ first : Index4,
            inverse row first * variation first second) *
            inverseDerivative second column +
          inverse second column *
            ∑ first : Index4,
              (inverse row first * variationDerivative first second +
                variation first second * inverseDerivative row first))) =
    (-1 : Real) *
      ∑ first : Index4, ∑ second : Index4,
        (inverseVariation row first * metricDerivative first second *
            inverse second column +
          inverse row first * variationDerivative first second *
            inverse second column +
          inverse row first * metricDerivative first second *
            inverseVariation second column)
  have hVariationDerivativeComm (second : Index4) :
      inverse second column *
          (∑ first : Index4,
            inverse row first * variationDerivative first second) =
        (∑ first : Index4,
            inverse row first * variationDerivative first second) *
          inverse second column := by
    ring
  have hInverseDerivativeVariationComm (second : Index4) :
      inverse second column *
          (∑ first : Index4,
            variation first second * inverseDerivative row first) =
        (∑ first : Index4,
            inverseDerivative row first * variation first second) *
          inverse second column := by
    have hSum :
        (∑ first : Index4,
            variation first second * inverseDerivative row first) =
          ∑ first : Index4,
            inverseDerivative row first * variation first second := by
      apply Finset.sum_congr rfl
      intro first _
      ring
    rw [hSum]
    ring
  simp only [Finset.sum_add_distrib, mul_add]
  simp_rw [hVariationDerivativeComm, hInverseDerivativeVariationComm]
  simp only [Finset.mul_sum] at hEntry
  ring_nf at hEntry ⊢
  exact hEntry

/-- The stored background spatial Koszul jet is the actual frame derivative
of the smooth lowered Koszul coefficient. -/
theorem regularFrameSmoothKoszulLowerCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second lower : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric
          first second lower) derivative =
      regularFrameSmoothKoszulLowerDerivativeCoefficient period hPeriod metric
        derivative first second lower := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalTotalHolonomicAtlasCover_covers period hPeriod point with
    ⟨patch, _hPatch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  have hZero :
      smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) = 0 := by
    rw [map_zero]
  have hLocal := regularGeneralMetricC0KoszulLower_smooth_local_fderiv
    period hPeriod metric 0 patch coordinate derivative first second lower
  rw [hZero] at hLocal
  have hFunction :
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric 0 first second
          lower (patch.coordinateMap current)) =
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric first
            second lower).toFun ∘ patch.coordinateMap := by
    funext current
    have hStored := congrArg
      (fun field : C0Scalar period hPeriod => field (patch.coordinateMap current))
      (regularGeneralMetricC0KoszulLower_zero_smooth period hPeriod metric first
        second lower)
    exact hStored
  rw [hFunction,
    fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric first
        second lower) patch coordinate derivative] at hLocal
  change frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric first
        second lower) (patch.coordinateMap coordinate) derivative = _
  rw [hLocal]
  have hStored := congrArg
    (fun field : C0Scalar period hPeriod => field (patch.coordinateMap coordinate))
    (regularGeneralMetricC0KoszulLowerDerivative_zero_smooth period hPeriod
      metric derivative first second lower)
  exact hStored

/-- The stored spatial Koszul velocity is the actual frame derivative of the
smooth lowered-Koszul velocity. -/
theorem regularFrameSmoothKoszulLowerVariationCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative first second lower : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothKoszulLowerVariationCoefficient period hPeriod
          metric tensor first second lower) derivative =
      regularFrameSmoothKoszulLowerSpatialVariationCoefficient period hPeriod
        metric tensor derivative first second lower := by
  classical
  unfold regularFrameSmoothKoszulLowerVariationCoefficient
  rw [frameDerivativeComponentField_smul]
  simp_rw [frameDerivativeComponentField_add,
    frameDerivativeComponentField_sub,
    frameDerivativeComponentField_univ_sum,
    frameDerivativeComponentField_mul_regular,
    regularFrameSmoothCovariantVariationCoefficient_frameDerivative,
    regularFrameSmoothCovariantVariationFirstDerivative_frameDerivative,
    regularFrameStructureCoefficient_frameDerivative]
  unfold regularFrameSmoothKoszulLowerSpatialVariationCoefficient
  simp_rw [frameDerivativeComponentField_add,
    regularFrameSmoothCovariantVariationFirstDerivative_frameDerivative]
  change _ = (1 / 2 : Real) •
    (regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
          tensor derivative first second lower +
      regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
          tensor derivative second lower first -
      regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
          tensor derivative lower first second -
      ∑ contracted : Index4,
        (smoothScalarFieldMul period hPeriod
            (regularFrameSmoothStructureCoefficientDerivative period hPeriod
              metric derivative second lower contracted)
            (regularFrameSmoothCovariantVariationCoefficient period hPeriod
              metric tensor first contracted) +
          smoothScalarFieldMul period hPeriod
            (regularFrameStructureCoefficient period hPeriod metric second
              lower contracted)
            (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod
              metric tensor derivative first contracted)) +
      ∑ contracted : Index4,
        (smoothScalarFieldMul period hPeriod
            (regularFrameSmoothStructureCoefficientDerivative period hPeriod
              metric derivative lower first contracted)
            (regularFrameSmoothCovariantVariationCoefficient period hPeriod
              metric tensor second contracted) +
          smoothScalarFieldMul period hPeriod
            (regularFrameStructureCoefficient period hPeriod metric lower first
              contracted)
            (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod
              metric tensor derivative second contracted)) +
      ∑ contracted : Index4,
        (smoothScalarFieldMul period hPeriod
            (regularFrameSmoothStructureCoefficientDerivative period hPeriod
              metric derivative first second contracted)
            (regularFrameSmoothCovariantVariationCoefficient period hPeriod
              metric tensor lower contracted) +
          smoothScalarFieldMul period hPeriod
            (regularFrameStructureCoefficient period hPeriod metric first
              second contracted)
            (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod
              metric tensor derivative lower contracted)))
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldSmul_toFun, smoothScalarFieldAdd_apply,
    smoothScalarFieldSub_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  have hFirstStructure := sum_product_rule_comm
    (fun contracted => regularFrameStructureCoefficient period hPeriod metric
      second lower contracted point)
    (fun contracted => regularFrameSmoothStructureCoefficientDerivative period
      hPeriod metric derivative second lower contracted point)
    (fun contracted => regularFrameSmoothCovariantVariationCoefficient period
      hPeriod metric tensor first contracted point)
    (fun contracted =>
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
        tensor derivative first contracted point)
  have hSecondStructure := sum_product_rule_comm
    (fun contracted => regularFrameStructureCoefficient period hPeriod metric
      lower first contracted point)
    (fun contracted => regularFrameSmoothStructureCoefficientDerivative period
      hPeriod metric derivative lower first contracted point)
    (fun contracted => regularFrameSmoothCovariantVariationCoefficient period
      hPeriod metric tensor second contracted point)
    (fun contracted =>
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
        tensor derivative second contracted point)
  have hThirdStructure := sum_product_rule_comm
    (fun contracted => regularFrameStructureCoefficient period hPeriod metric
      first second contracted point)
    (fun contracted => regularFrameSmoothStructureCoefficientDerivative period
      hPeriod metric derivative first second contracted point)
    (fun contracted => regularFrameSmoothCovariantVariationCoefficient period
      hPeriod metric tensor lower contracted point)
    (fun contracted =>
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
        tensor derivative lower contracted point)
  conv_lhs =>
    rw [hFirstStructure, hSecondStructure, hThirdStructure]

/-- The stored background spatial Christoffel jet is the actual frame
derivative of the smooth Christoffel coefficient. -/
theorem regularFrameSmoothChristoffelCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothChristoffelCoefficient period hPeriod metric upper
          first second) derivative =
      regularFrameSmoothChristoffelDerivativeCoefficient period hPeriod metric
        derivative upper first second := by
  classical
  unfold regularFrameSmoothChristoffelCoefficient
  rw [frameDerivativeComponentField_univ_sum]
  simp_rw [frameDerivativeComponentField_mul_regular,
    regularFrameMetricInverseMatrix_frameDerivative,
    regularFrameSmoothKoszulLowerCoefficient_frameDerivative]
  unfold regularFrameSmoothChristoffelDerivativeCoefficient
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldAdd_apply,
    smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro contracted _
  ring

/-- The stored spatial Christoffel velocity is the actual frame derivative of
the smooth Christoffel velocity. -/
theorem regularFrameSmoothChristoffelVariationCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper first second : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothChristoffelVariationCoefficient period hPeriod
          metric tensor upper first second) derivative =
      regularFrameSmoothChristoffelSpatialVariationCoefficient period hPeriod
        metric tensor derivative upper first second := by
  classical
  unfold regularFrameSmoothChristoffelVariationCoefficient
  rw [frameDerivativeComponentField_univ_sum]
  simp_rw [frameDerivativeComponentField_add,
    frameDerivativeComponentField_mul_regular,
    regularFrameSmoothInverseVariationCoefficient_frameDerivative,
    regularFrameSmoothKoszulLowerCoefficient_frameDerivative,
    regularFrameMetricInverseMatrix_frameDerivative,
    regularFrameSmoothKoszulLowerVariationCoefficient_frameDerivative]
  unfold regularFrameSmoothChristoffelSpatialVariationCoefficient
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldAdd_apply,
    smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro contracted _
  ring

/-- Gate marker for spatial compatibility of the smooth Christoffel velocity. -/
theorem regular_general_metric_c2_smooth_christoffel_spatial_compatibility_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper first second : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothChristoffelVariationCoefficient period hPeriod
          metric tensor upper first second) derivative =
      regularFrameSmoothChristoffelSpatialVariationCoefficient period hPeriod
        metric tensor derivative upper first second :=
  regularFrameSmoothChristoffelVariationCoefficient_frameDerivative period
    hPeriod metric tensor derivative upper first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialCompatibility4D
end JanusFormal
