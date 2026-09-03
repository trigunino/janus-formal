import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothRiemann4D

/-!
# Exact scalar curvature of a smooth varied metric

The exact smooth Riemann bridge identifies the completed Ricci and scalar
curvatures with the intrinsic curvatures of the genuine affine metric.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothRiemann4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev CoordinateMatrix := Matrix (Fin 4) (Fin 4) Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The completed regular-frame Ricci contraction is the intrinsic Ricci form
of the genuine varied metric. -/
theorem regularGeneralMetricC0Ricci_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    regularGeneralMetricC0Ricci period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        first second (patch.coordinateMap coordinate) =
      localRicciCurvatureBilinearMap period hPeriod variedMetric patch
        coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second
          coordinate) := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  unfold regularGeneralMetricC0Ricci
  change (∑ contracted : Fin 4,
      regularGeneralMetricC0Riemann period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        contracted first contracted second (patch.coordinateMap coordinate)) = _
  change _ = localRicciCurvatureVector period hPeriod variedMetric patch
    coordinate
    (pulledRegularFrameVector period hPeriod metric patch first coordinate)
    (pulledRegularFrameVector period hPeriod metric patch second coordinate)
  unfold localRicciCurvatureVector
  rw [LinearMap.trace_eq_matrix_trace Real basis]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (∑ contracted : Fin 4,
      regularGeneralMetricC0Riemann period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        contracted first contracted second (patch.coordinateMap coordinate)) =
    ∑ contracted : Fin 4,
      basis.repr
        (localLeviCivitaRiemannVector period hPeriod variedMetric patch
          coordinate (basis contracted)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate)
          (pulledRegularFrameVector period hPeriod metric patch first
            coordinate)) contracted
  apply Finset.sum_congr rfl
  intro contracted _
  rw [show basis contracted =
      pulledRegularFrameVector period hPeriod metric patch contracted
        coordinate by
    exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      contracted]
  exact regularGeneralMetricC0Riemann_smooth_apply period hPeriod metric tensor
    variedMetric hVaried hVariation patch coordinate contracted first contracted
      second

/-- Pointwise matrix of the completed inverse coefficients. -/
def regularGeneralMetricC0SmoothInverseMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : CoordinateMatrix :=
  fun row column =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor)
      row column point

/-- Pointwise matrix of the smooth actual varied-metric coefficients. -/
def regularGeneralMetricC0SmoothActualMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : CoordinateMatrix :=
  fun row column =>
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
      period hPeriod metric tensor row column point

/-- The completed inverse coefficients are the matrix inverse of the smooth
actual varied-metric coefficients. -/
theorem regularGeneralMetricC0InverseMetricMatrix_smooth_eq_inv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0SmoothInverseMatrix period hPeriod metric tensor point =
      (regularGeneralMetricC0SmoothActualMatrix period hPeriod metric tensor
        point)⁻¹ := by
  have hLeft :
      regularGeneralMetricC0SmoothInverseMatrix period hPeriod metric tensor point *
        regularGeneralMetricC0SmoothActualMatrix period hPeriod metric tensor
          point = 1 := by
    ext row column
    exact
      regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
        period hPeriod metric tensor hVariation point row column
  exact (Matrix.inv_eq_left_inv hLeft).symm

/-- Matrix view of the genuine varied Ricci form in the fixed regular frame. -/
def regularGeneralMetricC0SmoothRicciMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) : CoordinateMatrix :=
  fun first second =>
    localRicciCurvatureBilinearMap period hPeriod variedMetric patch coordinate
      (pulledRegularFrameVector period hPeriod metric patch first coordinate)
      (pulledRegularFrameVector period hPeriod metric patch second coordinate)

theorem smoothActualMetricMatrix_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) :
    regularGeneralMetricC0SmoothActualMatrix period hPeriod metric tensor
        (patch.coordinateMap coordinate) =
      (regularFrameChangeMatrix period hPeriod metric patch coordinate).transpose *
        localMetricMatrix period hPeriod variedMetric patch coordinate *
        regularFrameChangeMatrix period hPeriod metric patch coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let form := localMetricCoordinateForm period hPeriod variedMetric patch coordinate
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun Real (Fin 4)) basis form
  have hLocal :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form =
        localMetricMatrix period hPeriod variedMetric patch coordinate := by
    change LinearMap.BilinForm.toMatrix'
        (Matrix.toBilin'
          (localMetricMatrix period hPeriod variedMetric patch coordinate)) = _
    exact LinearMap.BilinForm.toMatrix'_toBilin'
      (localMetricMatrix period hPeriod variedMetric patch coordinate)
  have hMatrix :
      LinearMap.BilinForm.toMatrix basis form =
        regularGeneralMetricC0SmoothActualMatrix period hPeriod metric tensor
          (patch.coordinateMap coordinate) := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show basis first =
        pulledRegularFrameVector period hPeriod metric patch first coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        first]
    rw [show basis second =
        pulledRegularFrameVector period hPeriod metric patch second coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        second]
    exact
      candidateANormalBoundaryLocalMetricCoordinateForm_pulledRegularFrameVector
        period hPeriod metric tensor variedMetric hVaried patch coordinate first
          second
  rw [hLocal, hMatrix] at hCongruence
  change regularGeneralMetricC0SmoothActualMatrix period hPeriod metric tensor
      (patch.coordinateMap coordinate) =
    ((Pi.basisFun Real (Fin 4)).toMatrix basis).transpose *
      localMetricMatrix period hPeriod variedMetric patch coordinate *
      (Pi.basisFun Real (Fin 4)).toMatrix basis
  exact hCongruence.symm

private theorem smoothRicciMatrix_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) :
    regularGeneralMetricC0SmoothRicciMatrix period hPeriod metric variedMetric
        patch coordinate =
      (regularFrameChangeMatrix period hPeriod metric patch coordinate).transpose *
        localRicciCurvatureMatrix period hPeriod variedMetric patch coordinate *
        regularFrameChangeMatrix period hPeriod metric patch coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let form := localRicciCurvatureBilinearMap period hPeriod variedMetric patch
    coordinate
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun Real (Fin 4)) basis form
  have hLocal :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form =
        localRicciCurvatureMatrix period hPeriod variedMetric patch
          coordinate := by
    exact localRicciCurvatureBilinearMap_toMatrix period hPeriod variedMetric
      patch coordinate
  have hMatrix :
      LinearMap.BilinForm.toMatrix basis form =
        regularGeneralMetricC0SmoothRicciMatrix period hPeriod metric variedMetric
          patch coordinate := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show basis first =
        pulledRegularFrameVector period hPeriod metric patch first coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        first]
    rw [show basis second =
        pulledRegularFrameVector period hPeriod metric patch second coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        second]
    rfl
  rw [hLocal, hMatrix] at hCongruence
  change regularGeneralMetricC0SmoothRicciMatrix period hPeriod metric variedMetric
      patch coordinate =
    ((Pi.basisFun Real (Fin 4)).toMatrix basis).transpose *
      localRicciCurvatureMatrix period hPeriod variedMetric patch coordinate *
      (Pi.basisFun Real (Fin 4)).toMatrix basis
  exact hCongruence.symm

/-- The completed scalar curvature is the intrinsic local scalar curvature of
the genuine varied metric. -/
theorem regularGeneralMetricC0ScalarCurvature_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor)
        (patch.coordinateMap coordinate) =
      localScalarCurvature period hPeriod variedMetric patch coordinate := by
  unfold regularGeneralMetricC0ScalarCurvature localScalarCurvature
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  simp_rw [regularGeneralMetricC0Ricci_smooth_apply period hPeriod metric tensor
    variedMetric hVaried hVariation patch coordinate]
  change matrixEntryContraction
      (regularGeneralMetricC0SmoothInverseMatrix period hPeriod metric tensor
        (patch.coordinateMap coordinate))
      (regularGeneralMetricC0SmoothRicciMatrix period hPeriod metric variedMetric
        patch coordinate) =
    matrixEntryContraction
      (localMetricMatrix period hPeriod variedMetric patch coordinate)⁻¹
      (localRicciCurvatureMatrix period hPeriod variedMetric patch coordinate)
  have hInvariant := matrixEntryContraction_congruence
    (regularFrameChangeMatrix period hPeriod metric patch coordinate)
    (localMetricMatrix period hPeriod variedMetric patch coordinate)
    (localRicciCurvatureMatrix period hPeriod variedMetric patch coordinate)
    (regularFrameChangeMatrix_isUnit period hPeriod metric patch coordinate)
  rw [← smoothActualMetricMatrix_congruence period hPeriod metric tensor
      variedMetric hVaried patch coordinate,
    ← smoothRicciMatrix_congruence period hPeriod metric variedMetric patch
      coordinate] at hInvariant
  rw [regularGeneralMetricC0InverseMetricMatrix_smooth_eq_inv period hPeriod
    metric tensor hVariation (patch.coordinateMap coordinate)]
  exact hInvariant

/-- The completed scalar-curvature field is the genuine global smooth scalar
curvature of every admissible affine metric. -/
theorem regularGeneralMetricC0ScalarCurvature_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothScalarCurvature period hPeriod variedMetric) := by
  apply ContinuousMap.ext
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  change regularGeneralMetricC0ScalarCurvature period hPeriod metric
      (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor)
      (patch.coordinateMap coordinate) =
    globalSmoothScalarCurvature period hPeriod variedMetric
      (patch.coordinateMap coordinate)
  rw [regularGeneralMetricC0ScalarCurvature_smooth_apply period hPeriod metric
      tensor variedMetric hVaried hVariation patch coordinate,
    globalSmoothScalarCurvature_apply_local period hPeriod variedMetric patch
      coordinate]

/-- Gate marker: the completed scalar curvature is exactly the intrinsic global
scalar curvature on every admissible smooth affine metric. -/
theorem regular_general_metric_c2_smooth_scalar_curvature_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈
      regularGeneralMetricC2Domain period hPeriod metric) :
    regularGeneralMetricC0ScalarCurvature period hPeriod metric
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothScalarCurvature period hPeriod variedMetric) := by
  exact regularGeneralMetricC0ScalarCurvature_smooth period hPeriod metric tensor
    variedMetric hVaried hVariation

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
end JanusFormal
