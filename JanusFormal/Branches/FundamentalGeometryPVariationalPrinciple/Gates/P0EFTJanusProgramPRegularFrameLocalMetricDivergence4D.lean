import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalReferenceDensity4D

/-!
# Local metric divergence of a regular-frame vector

In every genuine holonomic chart, the density-weighted coordinate divergence
of a pulled regular-frame vector is the trace of its Levi--Civita covariant
derivative.  Trace invariance then identifies it with the already constructed
regular-frame Christoffel trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Coordinate representative of `direction ↦ ∇_direction e_b`. -/
def regularFrameLocalCovariantDerivativeEndomorphism
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) : Vector4 →ₗ[Real] Vector4 where
  toFun := fun direction =>
    fderiv Real
        (pulledRegularFrameVector period hPeriod metric patch vector)
        coordinate direction +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric patch
        coordinate direction
        (pulledRegularFrameVector period hPeriod metric patch vector coordinate)
  map_add' := by
    intro first second
    simp only [map_add, LinearMap.add_apply]
    abel
  map_smul' := by
    intro scalar direction
    simp only [map_smul, RingHom.id_apply, smul_add,
      LinearMap.smul_apply]

/-- Standard coordinate formula for the covariant divergence of `e_b`. -/
def regularFrameLocalCoordinateCovariantDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) : Real :=
  (∑ derivative : Index4,
      fderiv Real
        (fun current =>
          pulledRegularFrameVector period hPeriod metric patch vector current
            derivative)
        coordinate (Pi.single derivative 1)) +
    ∑ component : Index4,
      (∑ contracted : Index4,
        localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          contracted contracted component) *
        pulledRegularFrameVector period hPeriod metric patch vector coordinate
          component

/-- The explicit coordinate expression is the invariant trace of the local
covariant derivative endomorphism. -/
theorem regularFrameLocalCoordinateCovariantDivergence_eq_trace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameLocalCoordinateCovariantDivergence period hPeriod metric patch
        vector coordinate =
      LinearMap.trace Real Vector4
        (regularFrameLocalCovariantDerivativeEndomorphism period hPeriod metric
          patch vector coordinate) := by
  rw [LinearMap.trace_eq_matrix_trace Real (Pi.basisFun Real Index4)]
  unfold regularFrameLocalCoordinateCovariantDivergence Matrix.trace
  have hConnection :
      (∑ component : Index4,
          (∑ contracted : Index4,
            localLeviCivitaChristoffel period hPeriod metric.metric patch
              coordinate contracted contracted component) *
            pulledRegularFrameVector period hPeriod metric patch vector
              coordinate component) =
        ∑ derivative : Index4, ∑ component : Index4,
          localLeviCivitaChristoffel period hPeriod metric.metric patch
              coordinate derivative derivative component *
            pulledRegularFrameVector period hPeriod metric patch vector
              coordinate component := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hConnection, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  simp only [regularFrameLocalCovariantDerivativeEndomorphism]
  congr 1
  · have hDifferentiable : DifferentiableAt Real
        (pulledRegularFrameVector period hPeriod metric patch vector)
        coordinate :=
      (pulledRegularFrameVector_contDiff period hPeriod metric patch vector)
        |>.differentiable (by simp) coordinate
    have hComponent := fderiv_apply hDifferentiable derivative
    have hApplied := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hComponent
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hApplied
  · simp [localLeviCivitaChristoffelBilinearMap,
      localLeviCivitaChristoffelApply,
      localLeviCivitaChristoffelMatrix, Matrix.toBilin'_apply,
      Pi.single_apply]

/-- Computing the same trace in the pulled regular basis gives the global
regular-frame Christoffel trace. -/
theorem regularFrameLocalCovariantDerivative_trace_eq_leviCivitaTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    LinearMap.trace Real Vector4
        (regularFrameLocalCovariantDerivativeEndomorphism period hPeriod metric
          patch vector coordinate) =
      regularFrameLeviCivitaTrace period hPeriod metric vector
        (patch.coordinateMap coordinate) := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  rw [LinearMap.trace_eq_matrix_trace Real basis]
  unfold Matrix.trace regularFrameLeviCivitaTrace
  simp only [
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [show basis derivative =
      pulledRegularFrameVector period hPeriod metric patch derivative coordinate by
    exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      derivative]
  have hChristoffel :
      regularGeneralMetricC0Christoffel period hPeriod metric 0 derivative
          derivative vector (patch.coordinateMap coordinate) =
        regularFrameSmoothChristoffelCoefficient period hPeriod metric derivative
          derivative vector (patch.coordinateMap coordinate) := by
    exact congrArg (fun field => field (patch.coordinateMap coordinate))
      (regularGeneralMetricC0Christoffel_zero_smooth period hPeriod metric
        derivative derivative vector)
  rw [← hChristoffel]
  change
    basis.repr
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          derivative vector coordinate) derivative =
      regularGeneralMetricC0Christoffel period hPeriod metric 0 derivative
        derivative vector (patch.coordinateMap coordinate)
  exact (regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric patch
    coordinate derivative derivative vector).symm

/-- Thus the coordinate covariant divergence of each regular-frame vector is
the global regular-frame Levi--Civita trace. -/
theorem regularFrameLocalCoordinateCovariantDivergence_eq_leviCivitaTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameLocalCoordinateCovariantDivergence period hPeriod metric patch
        vector coordinate =
      regularFrameLeviCivitaTrace period hPeriod metric vector
        (patch.coordinateMap coordinate) := by
  rw [regularFrameLocalCoordinateCovariantDivergence_eq_trace,
    regularFrameLocalCovariantDerivative_trace_eq_leviCivitaTrace]

/-- Coordinate divergence with respect to an arbitrary nonzero scalar
density. -/
def regularFrameLocalDensityDivergence
    (density : Vector4 → Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) : Real :=
  (∑ derivative : Index4,
      fderiv Real
        (fun current =>
          density current *
            pulledRegularFrameVector period hPeriod metric patch vector current
              derivative)
        coordinate (Pi.single derivative 1)) /
    density coordinate

/-- For the genuine metric density, the density formula equals the
coordinate covariant divergence. -/
theorem regularFrameLocalMetricVolumeDivergence_eq_coordinateCovariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod metric.metric patch)
        metric patch vector coordinate =
      regularFrameLocalCoordinateCovariantDivergence period hPeriod metric patch
        vector coordinate := by
  let density := localMetricVolumeFactor period hPeriod metric.metric patch
  let field := pulledRegularFrameVector period hPeriod metric patch vector
  have hDensity : DifferentiableAt Real density coordinate :=
    (localMetricVolumeFactor_contDiff period hPeriod metric.metric patch)
      |>.differentiable (by simp) coordinate
  have hField : DifferentiableAt Real field coordinate :=
    (pulledRegularFrameVector_contDiff period hPeriod metric patch vector)
      |>.differentiable (by simp) coordinate
  have hComponent (derivative : Index4) : DifferentiableAt Real
      (fun current => field current derivative) coordinate := by
    fun_prop
  have hProduct (derivative : Index4) :
      fderiv Real
          (fun current => density current * field current derivative)
          coordinate (Pi.single derivative 1) =
        fderiv Real density coordinate (Pi.single derivative 1) *
            field coordinate derivative +
          density coordinate *
            fderiv Real (fun current => field current derivative) coordinate
              (Pi.single derivative 1) := by
    have hDerivative := fderiv_mul hDensity (hComponent derivative)
    have hApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hDerivative
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hApply
    rw [show (fun current => density current * field current derivative) =
      density * (fun current => field current derivative) by rfl]
    rw [hApply]
    ring
  have hGammaSymmetric (upper first second : Index4) :
      localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          upper first second =
        localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          upper second first := by
    have hTorsion :=
      (localLeviCivitaConnectionJet period hPeriod metric.metric patch
        coordinate).torsionFree upper first second
    change
      localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          upper first second =
        localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          upper second first at hTorsion
    exact hTorsion
  have hComponentDerivative (derivative : Index4) :
      fderiv Real (fun current => field current derivative) coordinate
          (Pi.single derivative 1) =
        (fderiv Real field coordinate (Pi.single derivative 1)) derivative := by
    have hDerivative := fderiv_apply hField derivative
    have hApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hDerivative
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hApply
  have hDensityNe : density coordinate ≠ 0 :=
    localMetricVolumeFactor_ne_zero period hPeriod metric.metric patch coordinate
  unfold regularFrameLocalDensityDivergence
    regularFrameLocalCoordinateCovariantDivergence
  change
    (∑ derivative : Index4,
        fderiv Real
          (fun current => density current * field current derivative)
          coordinate (Pi.single derivative 1)) / density coordinate = _
  field_simp [hDensityNe]
  simp_rw [hProduct]
  dsimp only [density]
  simp_rw [
    localMetricVolumeFactor_fderiv_basis_eq_christoffelTrace period hPeriod,
    hGammaSymmetric]
  rw [Finset.sum_add_distrib]
  dsimp only [field]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_add]
  rw [← Finset.mul_sum]
  ring

/-- The metric-density divergence has now been identified with the global
regular-frame connection trace in every chart. -/
theorem regularFrameLocalMetricVolumeDivergence_eq_leviCivitaTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    regularFrameLocalDensityDivergence period hPeriod
        (localMetricVolumeFactor period hPeriod metric.metric patch)
        metric patch vector coordinate =
      regularFrameLeviCivitaTrace period hPeriod metric vector
        (patch.coordinateMap coordinate) := by
  rw [regularFrameLocalMetricVolumeDivergence_eq_coordinateCovariant,
    regularFrameLocalCoordinateCovariantDivergence_eq_leviCivitaTrace]

/-- Gate marker for the local density/connection trace identification. -/
theorem regular_frame_local_metric_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (vector : Index4) (coordinate : Vector4),
      regularFrameLocalDensityDivergence period hPeriod
          (localMetricVolumeFactor period hPeriod metric.metric patch)
          metric patch vector coordinate =
        regularFrameLeviCivitaTrace period hPeriod metric vector
          (patch.coordinateMap coordinate) :=
  regularFrameLocalMetricVolumeDivergence_eq_leviCivitaTrace
    period hPeriod metric

end
end P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
end JanusFormal
