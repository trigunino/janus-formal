import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D

/-!
# Exact derivative of smooth varied-metric Christoffel coefficients

The completed first and second metric jets determine the genuine spatial
derivative of the inverse metric and hence of every Christoffel coefficient
at any admissible smooth variation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricSecondDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev CoordinateMatrix :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Local derivative of a genuine smooth varied-metric coefficient. -/
theorem regularGeneralMetricC0MetricCoefficient_smooth_local_fderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative row column : Fin 4) :
    fderiv Real
        (fun current =>
          candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric tensor row column
              (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative row column (patch.coordinateMap coordinate) := by
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth]
  exact
    (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor row column)
      patch coordinate derivative)

/-- Local derivative of every completed inverse-metric coefficient at an
admissible smooth, not necessarily zero, variation. -/
theorem regularGeneralMetricC0InverseMetricCoefficient_smooth_local_fderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative row column : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            row column (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative row column (patch.coordinateMap coordinate) := by
  classical
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let matrix : CoordinateVector → CoordinateMatrix := fun current row column =>
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period
      hPeriod metric tensor row column (patch.coordinateMap current)
  let inverse : CoordinateVector → CoordinateMatrix := fun current row column =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      variation row column (patch.coordinateMap current)
  have hMatrixContDiff : ContDiff Real ∞ matrix := by
    have hFormula : matrix = fun current =>
        ∑ currentRow : Fin 4, ∑ currentColumn : Fin 4,
          matrix current currentRow currentColumn •
            Matrix.single currentRow currentColumn (1 : Real) := by
      funext current
      simpa using (Matrix.matrix_eq_sum_single (matrix current))
    rw [hFormula]
    apply ContDiff.sum
    intro currentRow _
    apply ContDiff.sum
    intro currentColumn _
    exact
      (((candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor currentRow currentColumn).contMDiff_toFun.comp
        patch.coordinateMap_contMDiff).contDiff).smul_const _
  have hMatrix : DifferentiableAt Real matrix coordinate :=
    hMatrixContDiff.differentiable (by simp) coordinate
  have hMatrixDerivative :
      fderiv Real matrix coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        fun currentRow currentColumn =>
          regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
            variation derivative currentRow currentColumn
              (patch.coordinateMap coordinate) := by
    ext currentRow currentColumn
    rw [← fderiv_matrix_entry_apply matrix coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate) hMatrix currentRow currentColumn]
    exact regularGeneralMetricC0MetricCoefficient_smooth_local_fderiv
      period hPeriod metric tensor patch coordinate derivative currentRow
        currentColumn
  have hLeft (current : CoordinateVector) :
      inverse current * matrix current = 1 := by
    ext currentRow currentColumn
    exact
      regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
        period hPeriod metric tensor hVariation (patch.coordinateMap current)
          currentRow currentColumn
  have hUnit (current : CoordinateVector) : IsUnit (matrix current) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_left_inverse (hLeft current)
  have hFunction : inverse = Ring.inverse ∘ matrix := by
    funext current
    change inverse current = Ring.inverse (matrix current)
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    exact (Matrix.inv_eq_left_inv (hLeft current)).symm
  let unitMetric : CoordinateMatrixˣ := (hUnit coordinate).unit
  have hUnitSpec : (unitMetric : CoordinateMatrix) = matrix coordinate :=
    (hUnit coordinate).unit_spec
  have hInverseDerivative :
      fderiv Real inverse coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        -(inverse coordinate *
            fderiv Real matrix coordinate
              (pulledRegularFrameVector period hPeriod metric patch derivative
                coordinate) *
            inverse coordinate) := by
    rw [hFunction]
    have hDerivative :=
      ((hasFDerivAt_ringInverse (𝕜 := Real) unitMetric).comp coordinate
        hMatrix.hasFDerivAt).fderiv
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] CoordinateMatrix =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hDerivative
    have hUnitInverse :
        (↑(unitMetric⁻¹) : CoordinateMatrix) =
          Ring.inverse (matrix coordinate) := by
      calc
        (↑(unitMetric⁻¹) : CoordinateMatrix) =
            Ring.inverse (unitMetric : CoordinateMatrix) :=
          (Ring.inverse_unit unitMetric).symm
        _ = Ring.inverse (matrix coordinate) := by rw [hUnitSpec]
    rw [hUnitInverse] at hApplied
    change fderiv Real (Ring.inverse ∘ matrix) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      -(Ring.inverse (matrix coordinate) *
        fderiv Real matrix coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) *
        Ring.inverse (matrix coordinate)) at hApplied
    exact hApplied
  have hInverse : DifferentiableAt Real inverse coordinate := by
    rw [hFunction]
    exact
      ((hasFDerivAt_ringInverse (𝕜 := Real) unitMetric).comp coordinate
        hMatrix.hasFDerivAt).differentiableAt
  calc
    fderiv Real
        (fun current =>
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
            variation row column (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      fderiv Real inverse coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) row column := by
        simpa only [inverse] using
          (fderiv_matrix_entry_apply inverse coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate) hInverse row column)
    _ = (-(inverse coordinate *
          fderiv Real matrix coordinate
            (pulledRegularFrameVector period hPeriod metric patch derivative
              coordinate) *
          inverse coordinate)) row column := by rw [hInverseDerivative]
    _ = regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
        variation derivative row column
          (patch.coordinateMap coordinate) := by
      rw [hMatrixDerivative]
      unfold regularGeneralMetricC0InverseMetricDerivative
      change
        (-((inverse coordinate *
            (show CoordinateMatrix from fun currentRow currentColumn =>
              regularGeneralMetricC0MetricFirstDerivative period hPeriod
                metric variation derivative currentRow currentColumn
                  (patch.coordinateMap coordinate)) *
            inverse coordinate) row column)) =
          -(∑ first : Fin 4, ∑ second : Fin 4,
            inverse coordinate row first *
              regularGeneralMetricC0MetricFirstDerivative period hPeriod
                metric variation derivative first second
                  (patch.coordinateMap coordinate) *
              inverse coordinate second column)
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]

private theorem fderiv_regularFrameStructureCoefficient_smooth_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second upper : Fin 4) :
    fderiv Real
        (fun current =>
          regularFrameStructureCoefficientContinuous period hPeriod metric
            first second upper (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularFrameStructureCoefficientDerivativeContinuous period hPeriod
        metric derivative first second upper
          (patch.coordinateMap coordinate) := by
  change fderiv Real
      ((regularFrameStructureCoefficient period hPeriod metric first second
        upper).toFun ∘ patch.coordinateMap) coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate) =
    frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameStructureCoefficient period hPeriod metric first second upper)
      (patch.coordinateMap coordinate) derivative
  exact
    (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod metric
      (regularFrameStructureCoefficient period hPeriod metric first second
        upper) patch coordinate derivative)

private theorem
    regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (inner row column : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          inner row column (patch.coordinateMap current)) coordinate := by
  let field := frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period
      hPeriod metric tensor row column) inner
  have hFunction :
      (fun current =>
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          inner row column (patch.coordinateMap current)) =
        field.toFun ∘ patch.coordinateMap := by
    funext current
    exact
      candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth
        period hPeriod metric tensor inner row column
          (patch.coordinateMap current)
  rw [hFunction]
  exact ((((field.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
    patch.coordinateMap_contMDiff).contDiff.differentiable
      (by simp)).differentiableAt)

private theorem fderiv_regularFrameStructureMetricProduct_smooth_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative bracketFirst bracketSecond contracted row column : Fin 4) :
    fderiv Real
        (fun current =>
          regularFrameStructureCoefficientContinuous period hPeriod metric
              bracketFirst bracketSecond contracted
                (patch.coordinateMap current) *
            regularGeneralMetricC0MetricCoefficient period hPeriod metric
              (smoothToGeneralMetricRelativeC2Core period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor)
              row column (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularFrameStructureMetricDerivativeTerm period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative bracketFirst bracketSecond contracted row column
          (patch.coordinateMap coordinate) := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let structureField :=
    regularFrameStructureCoefficient period hPeriod metric bracketFirst
      bracketSecond contracted
  let metricField :=
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period
      hPeriod metric tensor row column
  have hStructure : DifferentiableAt Real
      (structureField.toFun ∘ patch.coordinateMap) coordinate :=
    ((((structureField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
      patch.coordinateMap_contMDiff).contDiff.differentiable
        (by simp)).differentiableAt)
  have hMetric : DifferentiableAt Real
      (metricField.toFun ∘ patch.coordinateMap) coordinate :=
    ((((metricField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
      patch.coordinateMap_contMDiff).contDiff.differentiable
        (by simp)).differentiableAt)
  have hFunction :
      (fun current =>
        regularFrameStructureCoefficientContinuous period hPeriod metric
            bracketFirst bracketSecond contracted (patch.coordinateMap current) *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric
            variation row column (patch.coordinateMap current)) =
        (structureField.toFun ∘ patch.coordinateMap) *
          (metricField.toFun ∘ patch.coordinateMap) := by
    funext current
    simp only [structureField,
      regularFrameStructureCoefficientContinuous_apply,
      Function.comp_apply, Pi.mul_apply]
    exact congrArg
      (fun value =>
        regularFrameStructureCoefficient period hPeriod metric bracketFirst
            bracketSecond contracted (patch.coordinateMap current) * value)
      (candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
        period hPeriod metric tensor row column
          (patch.coordinateMap current))
  rw [hFunction]
  change fderiv Real
      ((structureField.toFun ∘ patch.coordinateMap) *
        (metricField.toFun ∘ patch.coordinateMap)) coordinate
      (pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate) = _
  rw [fderiv_mul hStructure hMetric]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [show fderiv Real (structureField.toFun ∘ patch.coordinateMap) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularFrameStructureCoefficientDerivativeContinuous period hPeriod
        metric derivative bracketFirst bracketSecond contracted
          (patch.coordinateMap coordinate) by
    exact fderiv_regularFrameStructureCoefficient_smooth_local period hPeriod
      metric patch coordinate derivative bracketFirst bracketSecond contracted]
  rw [show fderiv Real (metricField.toFun ∘ patch.coordinateMap) coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        variation derivative row column (patch.coordinateMap coordinate) by
    exact regularGeneralMetricC0MetricCoefficient_smooth_local_fderiv period
      hPeriod metric tensor patch coordinate derivative row column]
  unfold regularFrameStructureMetricDerivativeTerm
  change _ =
    regularFrameStructureCoefficientDerivativeContinuous period hPeriod metric
          derivative bracketFirst bracketSecond contracted
            (patch.coordinateMap coordinate) *
        regularGeneralMetricC0MetricCoefficient period hPeriod metric variation
          row column (patch.coordinateMap coordinate) +
      regularFrameStructureCoefficientContinuous period hPeriod metric
          bracketFirst bracketSecond contracted (patch.coordinateMap coordinate) *
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
          variation derivative row column (patch.coordinateMap coordinate)
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix]
  simp only [regularFrameStructureCoefficientContinuous_apply]
  dsimp only [structureField, metricField, Function.comp_apply]
  ring

private theorem
    regularFrameStructureMetricProduct_smooth_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (bracketFirst bracketSecond contracted row column : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularFrameStructureCoefficientContinuous period hPeriod metric
            bracketFirst bracketSecond contracted (patch.coordinateMap current) *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            row column (patch.coordinateMap current)) coordinate := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let structureField :=
    regularFrameStructureCoefficient period hPeriod metric bracketFirst
      bracketSecond contracted
  let metricField :=
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period
      hPeriod metric tensor row column
  have hFunction :
      (fun current =>
        regularFrameStructureCoefficientContinuous period hPeriod metric
            bracketFirst bracketSecond contracted (patch.coordinateMap current) *
          regularGeneralMetricC0MetricCoefficient period hPeriod metric
            variation row column (patch.coordinateMap current)) =
        (structureField.toFun ∘ patch.coordinateMap) *
          (metricField.toFun ∘ patch.coordinateMap) := by
    funext current
    simp only [structureField,
      regularFrameStructureCoefficientContinuous_apply,
      Function.comp_apply, Pi.mul_apply]
    exact congrArg
      (fun value =>
        regularFrameStructureCoefficient period hPeriod metric bracketFirst
            bracketSecond contracted (patch.coordinateMap current) * value)
      (candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
        period hPeriod metric tensor row column
          (patch.coordinateMap current))
  rw [hFunction]
  exact
    (((((structureField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
        patch.coordinateMap_contMDiff).contDiff.differentiable
          (by simp)).differentiableAt).mul
      ((((metricField.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
        patch.coordinateMap_contMDiff).contDiff.differentiable
          (by simp)).differentiableAt))

/-- Local derivative of the completed lowered Koszul coefficient at every
smooth nonzero variation. -/
theorem regularGeneralMetricC0KoszulLower_smooth_local_fderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative first second lower : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0KoszulLower period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            first second lower (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative first second lower (patch.coordinateMap coordinate) := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let metricTerm (inner row column : Fin 4) : CoordinateVector → Real :=
    fun current =>
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        variation inner row column (patch.coordinateMap current)
  let structureTerm
      (bracketFirst bracketSecond contracted row column : Fin 4) :
      CoordinateVector → Real := fun current =>
    regularFrameStructureCoefficientContinuous period hPeriod metric
        bracketFirst bracketSecond contracted (patch.coordinateMap current) *
      regularGeneralMetricC0MetricCoefficient period hPeriod metric variation
        row column (patch.coordinateMap current)
  let firstMetric := metricTerm first second lower
  let secondMetric := metricTerm second lower first
  let thirdMetric := metricTerm lower first second
  let firstStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm second lower contracted first contracted current
  let secondStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm lower first contracted second contracted current
  let thirdStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm first second contracted lower contracted current
  let firstPair := firstMetric + secondMetric
  let subtractMetric := firstPair - thirdMetric
  let subtractStructure := subtractMetric - firstStructure
  let addSecondStructure := subtractStructure + secondStructure
  let inside := addSecondStructure + thirdStructure
  have hFirstMetric : DifferentiableAt Real firstMetric coordinate := by
    exact
      regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
        period hPeriod metric tensor patch coordinate first second lower
  have hSecondMetric : DifferentiableAt Real secondMetric coordinate := by
    exact
      regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
        period hPeriod metric tensor patch coordinate second lower first
  have hThirdMetric : DifferentiableAt Real thirdMetric coordinate := by
    exact
      regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
        period hPeriod metric tensor patch coordinate lower first second
  have hFirstStructure : DifferentiableAt Real firstStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate second lower contracted
        first contracted
  have hSecondStructure : DifferentiableAt Real secondStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate lower first contracted
        second contracted
  have hThirdStructure : DifferentiableAt Real thirdStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate first second contracted
        lower contracted
  have hFirstPair : DifferentiableAt Real firstPair coordinate :=
    hFirstMetric.add hSecondMetric
  have hSubtractMetric : DifferentiableAt Real subtractMetric coordinate :=
    hFirstPair.sub hThirdMetric
  have hSubtractStructure : DifferentiableAt Real subtractStructure coordinate :=
    hSubtractMetric.sub hFirstStructure
  have hAddSecondStructure : DifferentiableAt Real addSecondStructure coordinate :=
    hSubtractStructure.add hSecondStructure
  have hInside : DifferentiableAt Real inside coordinate :=
    hAddSecondStructure.add hThirdStructure
  have hFirstStructureDerivative :
      fderiv Real firstStructure coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        ∑ contracted : Fin 4,
          regularFrameStructureMetricDerivativeTerm period hPeriod metric
            variation derivative second lower contracted first contracted
              (patch.coordinateMap coordinate) := by
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun contracted _ =>
        regularFrameStructureMetricProduct_smooth_local_differentiableAt
          period hPeriod metric tensor patch coordinate second lower contracted
            first contracted)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hSum
    change fderiv Real firstStructure coordinate _ = _
    rw [hApplied]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro contracted _
    exact fderiv_regularFrameStructureMetricProduct_smooth_local period hPeriod
      metric tensor patch coordinate derivative second lower contracted first
        contracted
  have hSecondStructureDerivative :
      fderiv Real secondStructure coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        ∑ contracted : Fin 4,
          regularFrameStructureMetricDerivativeTerm period hPeriod metric
            variation derivative lower first contracted second contracted
              (patch.coordinateMap coordinate) := by
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun contracted _ =>
        regularFrameStructureMetricProduct_smooth_local_differentiableAt
          period hPeriod metric tensor patch coordinate lower first contracted
            second contracted)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hSum
    change fderiv Real secondStructure coordinate _ = _
    rw [hApplied]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro contracted _
    exact fderiv_regularFrameStructureMetricProduct_smooth_local period hPeriod
      metric tensor patch coordinate derivative lower first contracted second
        contracted
  have hThirdStructureDerivative :
      fderiv Real thirdStructure coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        ∑ contracted : Fin 4,
          regularFrameStructureMetricDerivativeTerm period hPeriod metric
            variation derivative first second contracted lower contracted
              (patch.coordinateMap coordinate) := by
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun contracted _ =>
        regularFrameStructureMetricProduct_smooth_local_differentiableAt
          period hPeriod metric tensor patch coordinate first second contracted
            lower contracted)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hSum
    change fderiv Real thirdStructure coordinate _ = _
    rw [hApplied]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro contracted _
    exact fderiv_regularFrameStructureMetricProduct_smooth_local period hPeriod
      metric tensor patch coordinate derivative first second contracted lower
        contracted
  have hFirstPairDerivative :
      fderiv Real firstPair coordinate =
        fderiv Real firstMetric coordinate +
          fderiv Real secondMetric coordinate :=
    fderiv_add hFirstMetric hSecondMetric
  have hSubtractMetricDerivative :
      fderiv Real subtractMetric coordinate =
        fderiv Real firstPair coordinate -
          fderiv Real thirdMetric coordinate :=
    fderiv_sub hFirstPair hThirdMetric
  have hSubtractStructureDerivative :
      fderiv Real subtractStructure coordinate =
        fderiv Real subtractMetric coordinate -
          fderiv Real firstStructure coordinate :=
    fderiv_sub hSubtractMetric hFirstStructure
  have hAddSecondStructureDerivative :
      fderiv Real addSecondStructure coordinate =
        fderiv Real subtractStructure coordinate +
          fderiv Real secondStructure coordinate :=
    fderiv_add hSubtractStructure hSecondStructure
  have hInsideDerivative :
      fderiv Real inside coordinate =
        fderiv Real addSecondStructure coordinate +
          fderiv Real thirdStructure coordinate :=
    fderiv_add hAddSecondStructure hThirdStructure
  have hInsideApplied :
      fderiv Real inside coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
              variation derivative first second lower
                (patch.coordinateMap coordinate) +
          regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
              variation derivative second lower first
                (patch.coordinateMap coordinate) -
          regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
              variation derivative lower first second
                (patch.coordinateMap coordinate) -
          (∑ contracted : Fin 4,
            regularFrameStructureMetricDerivativeTerm period hPeriod metric
              variation derivative second lower contracted first contracted
                (patch.coordinateMap coordinate)) +
          (∑ contracted : Fin 4,
            regularFrameStructureMetricDerivativeTerm period hPeriod metric
              variation derivative lower first contracted second contracted
                (patch.coordinateMap coordinate)) +
          ∑ contracted : Fin 4,
            regularFrameStructureMetricDerivativeTerm period hPeriod metric
              variation derivative first second contracted lower contracted
                (patch.coordinateMap coordinate) := by
    rw [hInsideDerivative, add_apply, hAddSecondStructureDerivative, add_apply,
      hSubtractStructureDerivative, sub_apply, hSubtractMetricDerivative,
      sub_apply, hFirstPairDerivative, add_apply]
    rw [show fderiv Real firstMetric coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation derivative first second lower
            (patch.coordinateMap coordinate) by
      exact regularGeneralMetricC0MetricFirstDerivative_smooth_local_fderiv
        period hPeriod metric tensor patch coordinate derivative first second
          lower]
    rw [show fderiv Real secondMetric coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation derivative second lower first
            (patch.coordinateMap coordinate) by
      exact regularGeneralMetricC0MetricFirstDerivative_smooth_local_fderiv
        period hPeriod metric tensor patch coordinate derivative second lower
          first]
    rw [show fderiv Real thirdMetric coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0MetricSecondDerivative period hPeriod metric
          variation derivative lower first second
            (patch.coordinateMap coordinate) by
      exact regularGeneralMetricC0MetricFirstDerivative_smooth_local_fderiv
        period hPeriod metric tensor patch coordinate derivative lower first
          second]
    rw [hFirstStructureDerivative, hSecondStructureDerivative,
      hThirdStructureDerivative]
  have hFunction :
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric variation first
          second lower (patch.coordinateMap current)) =
        fun current => (1 / 2 : Real) * inside current := by
    funext current
    unfold regularGeneralMetricC0KoszulLower
    change (1 / 2 : Real) *
        (metricTerm first second lower current +
          metricTerm second lower first current -
          metricTerm lower first second current -
          (∑ contracted : Fin 4,
            structureTerm second lower contracted first contracted current) +
          (∑ contracted : Fin 4,
            structureTerm lower first contracted second contracted current) +
          ∑ contracted : Fin 4,
            structureTerm first second contracted lower contracted current) = _
    rfl
  rw [hFunction]
  have hScaledDerivative :
      fderiv Real (fun current => (1 / 2 : Real) * inside current) coordinate =
        (1 / 2 : Real) • fderiv Real inside coordinate := by
    change fderiv Real ((1 / 2 : Real) • inside) coordinate = _
    exact congrFun
      (fderiv_const_smul_field (𝕜 := Real) (R := Real) (f := inside)
        (1 / 2 : Real)) coordinate
  rw [hScaledDerivative]
  simp only [smul_apply, smul_eq_mul]
  rw [hInsideApplied]
  unfold regularGeneralMetricC0KoszulLowerDerivative
  change (1 / 2 : Real) * _ = (1 / 2 : Real) * _
  rfl

private theorem
    regularGeneralMetricC0InverseMetricCoefficient_smooth_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (row column : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          row column (patch.coordinateMap current)) coordinate := by
  classical
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let matrix : CoordinateVector → CoordinateMatrix := fun current row column =>
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period
      hPeriod metric tensor row column (patch.coordinateMap current)
  let inverse : CoordinateVector → CoordinateMatrix := fun current row column =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      variation row column (patch.coordinateMap current)
  have hMatrixContDiff : ContDiff Real ∞ matrix := by
    have hFormula : matrix = fun current =>
        ∑ currentRow : Fin 4, ∑ currentColumn : Fin 4,
          matrix current currentRow currentColumn •
            Matrix.single currentRow currentColumn (1 : Real) := by
      funext current
      simpa using (Matrix.matrix_eq_sum_single (matrix current))
    rw [hFormula]
    apply ContDiff.sum
    intro currentRow _
    apply ContDiff.sum
    intro currentColumn _
    exact
      (((candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
          period hPeriod metric tensor currentRow currentColumn).contMDiff_toFun.comp
        patch.coordinateMap_contMDiff).contDiff).smul_const _
  have hMatrix : DifferentiableAt Real matrix coordinate :=
    hMatrixContDiff.differentiable (by simp) coordinate
  have hLeft (current : CoordinateVector) :
      inverse current * matrix current = 1 := by
    ext currentRow currentColumn
    exact
      regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
        period hPeriod metric tensor hVariation (patch.coordinateMap current)
          currentRow currentColumn
  have hUnit : IsUnit (matrix coordinate) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_left_inverse (hLeft coordinate)
  have hFunction : inverse = Ring.inverse ∘ matrix := by
    funext current
    change inverse current = Ring.inverse (matrix current)
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    exact (Matrix.inv_eq_left_inv (hLeft current)).symm
  let unitMetric : CoordinateMatrixˣ := hUnit.unit
  have hInverse : DifferentiableAt Real inverse coordinate := by
    rw [hFunction]
    exact
      ((hasFDerivAt_ringInverse (𝕜 := Real) unitMetric).comp coordinate
        hMatrix.hasFDerivAt).differentiableAt
  simpa only [inverse] using
    (differentiableAt_pi.mp (differentiableAt_pi.mp hInverse row) column)

private theorem
    regularGeneralMetricC0KoszulLower_smooth_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second lower : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          first second lower (patch.coordinateMap current)) coordinate := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let metricTerm (inner row column : Fin 4) : CoordinateVector → Real :=
    fun current =>
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        variation inner row column (patch.coordinateMap current)
  let structureTerm
      (bracketFirst bracketSecond contracted row column : Fin 4) :
      CoordinateVector → Real := fun current =>
    regularFrameStructureCoefficientContinuous period hPeriod metric
        bracketFirst bracketSecond contracted (patch.coordinateMap current) *
      regularGeneralMetricC0MetricCoefficient period hPeriod metric variation
        row column (patch.coordinateMap current)
  let firstStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm second lower contracted first contracted current
  let secondStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm lower first contracted second contracted current
  let thirdStructure : CoordinateVector → Real := fun current =>
    ∑ contracted : Fin 4,
      structureTerm first second contracted lower contracted current
  let inside : CoordinateVector → Real := fun current =>
    metricTerm first second lower current +
      metricTerm second lower first current -
      metricTerm lower first second current -
      firstStructure current + secondStructure current + thirdStructure current
  have hFirstMetric : DifferentiableAt Real
      (metricTerm first second lower) coordinate :=
    regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate first second lower
  have hSecondMetric : DifferentiableAt Real
      (metricTerm second lower first) coordinate :=
    regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate second lower first
  have hThirdMetric : DifferentiableAt Real
      (metricTerm lower first second) coordinate :=
    regularGeneralMetricC0MetricFirstDerivative_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate lower first second
  have hFirstStructure : DifferentiableAt Real firstStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate second lower contracted
        first contracted
  have hSecondStructure : DifferentiableAt Real secondStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate lower first contracted
        second contracted
  have hThirdStructure : DifferentiableAt Real thirdStructure coordinate := by
    apply DifferentiableAt.fun_sum
    intro contracted _
    exact regularFrameStructureMetricProduct_smooth_local_differentiableAt
      period hPeriod metric tensor patch coordinate first second contracted
        lower contracted
  have hInside : DifferentiableAt Real inside coordinate :=
    (((hFirstMetric.add hSecondMetric).sub hThirdMetric).sub hFirstStructure).add
      hSecondStructure |>.add hThirdStructure
  have hFunction :
      (fun current =>
        regularGeneralMetricC0KoszulLower period hPeriod metric variation first
          second lower (patch.coordinateMap current)) =
        fun current => (1 / 2 : Real) * inside current := by
    funext current
    unfold regularGeneralMetricC0KoszulLower
    change (1 / 2 : Real) *
        (metricTerm first second lower current +
          metricTerm second lower first current -
          metricTerm lower first second current - firstStructure current +
          secondStructure current + thirdStructure current) = _
    rfl
  rw [hFunction]
  exact hInside.const_mul (1 / 2 : Real)

/-- Smooth admissible Christoffel coefficients are locally differentiable in
every pulled regular-frame direction. -/
theorem regularGeneralMetricC0Christoffel_smooth_local_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (upper first second : Fin 4) :
    DifferentiableAt Real
      (fun current =>
        regularGeneralMetricC0Christoffel period hPeriod metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor)
          upper first second (patch.coordinateMap current)) coordinate := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let inverseTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      variation upper lower (patch.coordinateMap current)
  let koszulTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0KoszulLower period hPeriod metric variation first
      second lower (patch.coordinateMap current)
  have hFunction :
      (fun current =>
        regularGeneralMetricC0Christoffel period hPeriod metric variation upper
          first second (patch.coordinateMap current)) =
        fun current => ∑ lower : Fin 4,
          inverseTerm lower current * koszulTerm lower current := by
    funext current
    rfl
  rw [hFunction]
  apply DifferentiableAt.fun_sum
  intro lower _
  exact
    (regularGeneralMetricC0InverseMetricCoefficient_smooth_local_differentiableAt
      period hPeriod metric tensor hVariation patch coordinate upper lower).mul
    (regularGeneralMetricC0KoszulLower_smooth_local_differentiableAt period
      hPeriod metric tensor patch coordinate first second lower)

/-- The completed Christoffel derivative is the actual directional derivative
of the completed Christoffel coefficient at every admissible smooth variation. -/
theorem regularGeneralMetricC0Christoffel_smooth_local_fderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative upper first second : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0Christoffel period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            upper first second (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0ChristoffelDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative upper first second (patch.coordinateMap coordinate) := by
  let variation := smoothToGeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor
  let inverseTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      variation upper lower (patch.coordinateMap current)
  let koszulTerm (lower : Fin 4) : CoordinateVector → Real := fun current =>
    regularGeneralMetricC0KoszulLower period hPeriod metric variation first
      second lower (patch.coordinateMap current)
  let productTerm (lower : Fin 4) : CoordinateVector → Real :=
    inverseTerm lower * koszulTerm lower
  let christoffel : CoordinateVector → Real := fun current =>
    ∑ lower : Fin 4, productTerm lower current
  have hInverse (lower : Fin 4) :
      DifferentiableAt Real (inverseTerm lower) coordinate :=
    regularGeneralMetricC0InverseMetricCoefficient_smooth_local_differentiableAt
      period hPeriod metric tensor hVariation patch coordinate upper lower
  have hKoszul (lower : Fin 4) :
      DifferentiableAt Real (koszulTerm lower) coordinate :=
    regularGeneralMetricC0KoszulLower_smooth_local_differentiableAt period
      hPeriod metric tensor patch coordinate first second lower
  have hProduct (lower : Fin 4) :
      DifferentiableAt Real (productTerm lower) coordinate :=
    (hInverse lower).mul (hKoszul lower)
  have hProductDerivative (lower : Fin 4) :
      fderiv Real (productTerm lower) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
              variation derivative upper lower
                (patch.coordinateMap coordinate) *
            regularGeneralMetricC0KoszulLower period hPeriod metric variation
              first second lower (patch.coordinateMap coordinate) +
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
              variation upper lower (patch.coordinateMap coordinate) *
            regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric
              variation derivative first second lower
                (patch.coordinateMap coordinate) := by
    have hDerivative := fderiv_mul (hInverse lower) (hKoszul lower)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] Real =>
        derivativeMap
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) hDerivative
    change fderiv Real (productTerm lower) coordinate _ = _
    rw [hApplied]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show fderiv Real (inverseTerm lower) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0InverseMetricDerivative period hPeriod metric
          variation derivative upper lower (patch.coordinateMap coordinate) by
      exact
        regularGeneralMetricC0InverseMetricCoefficient_smooth_local_fderiv
          period hPeriod metric tensor hVariation patch coordinate derivative
            upper lower]
    rw [show fderiv Real (koszulTerm lower) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) =
        regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric
          variation derivative first second lower
            (patch.coordinateMap coordinate) by
      exact regularGeneralMetricC0KoszulLower_smooth_local_fderiv period
        hPeriod metric tensor patch coordinate derivative first second lower]
    simp only [inverseTerm, koszulTerm]
    ring
  have hFunction :
      (fun current =>
        regularGeneralMetricC0Christoffel period hPeriod metric variation upper
          first second (patch.coordinateMap current)) = christoffel := by
    funext current
    rfl
  rw [hFunction]
  have hSum := fderiv_fun_sum (u := Finset.univ)
    (fun lower _ => hProduct lower)
  have hApplied := congrArg
    (fun derivativeMap : CoordinateVector →L[Real] Real =>
      derivativeMap
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate)) hSum
  change fderiv Real christoffel coordinate _ = _
  rw [hApplied]
  simp only [sum_apply]
  unfold regularGeneralMetricC0ChristoffelDerivative
  simp only [ContinuousMap.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.mul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  exact hProductDerivative lower

/-- Gate marker: the completed Christoffel first spatial jet is exact at every
admissible smooth general-metric variation. -/
theorem regular_general_metric_c2_smooth_christoffel_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector)
    (derivative upper first second : Fin 4) :
    fderiv Real
        (fun current =>
          regularGeneralMetricC0Christoffel period hPeriod metric
            (smoothToGeneralMetricRelativeC2Core period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor)
            upper first second (patch.coordinateMap current))
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      regularGeneralMetricC0ChristoffelDerivative period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        derivative upper first second (patch.coordinateMap coordinate) := by
  exact regularGeneralMetricC0Christoffel_smooth_local_fderiv period hPeriod
    metric tensor hVariation patch coordinate derivative upper first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D
end JanusFormal
