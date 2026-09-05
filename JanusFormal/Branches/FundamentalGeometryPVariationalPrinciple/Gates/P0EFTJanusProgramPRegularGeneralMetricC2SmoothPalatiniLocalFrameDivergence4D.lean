import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalDivergenceDensity4D

/-! # Frame invariance of the smooth Palatini divergence -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalFrameDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalDivergenceDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Coordinate covariant derivative of the genuine Palatini vector, bundled
as an endomorphism. -/
def regularGeneralMetricC2PalatiniLocalCovariantDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 →ₗ[Real] Vector4 where
  toFun := fun direction =>
    fderiv Real
        (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
          patch) coordinate direction +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric patch
        coordinate direction
        (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
          patch coordinate)
  map_add' := by
    intro first second
    simp only [map_add, LinearMap.add_apply]
    abel
  map_smul' := by
    intro scalar direction
    simp only [map_smul, RingHom.id_apply, smul_add,
      LinearMap.smul_apply]

/-- The explicit holonomic formula is the invariant trace of the local
covariant derivative. -/
theorem regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_trace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
        metric tensor patch coordinate =
      LinearMap.trace Real Vector4
        (regularGeneralMetricC2PalatiniLocalCovariantDerivative period hPeriod
          metric tensor patch coordinate) := by
  rw [LinearMap.trace_eq_matrix_trace Real (Pi.basisFun Real Index4)]
  unfold regularGeneralMetricC2PalatiniLocalCovariantDivergence Matrix.trace
  have hConnection :
      (∑ vector : Index4,
          (∑ contracted : Index4,
            localLeviCivitaChristoffel period hPeriod metric.metric patch
              coordinate contracted contracted vector) *
            regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric
              tensor patch coordinate vector) =
        ∑ derivative : Index4, ∑ vector : Index4,
          localLeviCivitaChristoffel period hPeriod metric.metric patch
              coordinate derivative derivative vector *
            regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric
              tensor patch coordinate vector := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hConnection, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  simp only [regularGeneralMetricC2PalatiniLocalCovariantDerivative]
  congr 1
  simp [localLeviCivitaChristoffelBilinearMap,
    localLeviCivitaChristoffelApply,
    localLeviCivitaChristoffelMatrix, Matrix.toBilin'_apply,
    Pi.single_apply]

private theorem regularGeneralMetricC2PalatiniLocalCovariantDerivative_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) :
    regularGeneralMetricC2PalatiniLocalCovariantDerivative period hPeriod
        metric tensor patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch derivative
          coordinate) =
      (∑ vector : Index4,
        regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
            tensor derivative vector (patch.coordinateMap coordinate) •
          pulledRegularFrameVector period hPeriod metric patch vector
            coordinate) +
        ∑ auxiliary : Index4,
          regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              auxiliary (patch.coordinateMap coordinate) •
            regularFrameLocalCovariantDerivativeVector period hPeriod metric
              patch derivative auxiliary coordinate := by
  let coefficient (vector : Index4) : Vector4 → Real :=
    (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector
      ).toFun ∘ patch.coordinateMap
  let frame (vector : Index4) : Vector4 → Vector4 :=
    pulledRegularFrameVector period hPeriod metric patch vector
  let term (vector : Index4) : Vector4 → Vector4 := fun current =>
    coefficient vector current • frame vector current
  have hCoefficient (vector : Index4) :
      DifferentiableAt Real (coefficient vector) coordinate :=
    (((((regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
          vector).contMDiff_toFun.of_le (m := ∞) (by simp)).comp
        patch.coordinateMap_contMDiff).contDiff.differentiable
          (by simp)).differentiableAt)
  have hFrame (vector : Index4) :
      DifferentiableAt Real (frame vector) coordinate :=
    pulledRegularFrameVector_differentiableAt period hPeriod metric patch
      coordinate vector
  have hTerm (vector : Index4) :
      DifferentiableAt Real (term vector) coordinate :=
    (hCoefficient vector).smul (hFrame vector)
  have hCoefficientDerivative (vector : Index4) :
      fderiv Real (coefficient vector) coordinate
          (frame derivative coordinate) =
        regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
          tensor derivative vector (patch.coordinateMap coordinate) := by
    change fderiv Real
        ((regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
          vector).toFun ∘ patch.coordinateMap) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) = _
    rw [fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
      metric (regularFrameSmoothPalatiniCoefficient period hPeriod metric
        tensor vector) patch coordinate derivative]
    exact congrArg
      (fun field : SmoothScalarField period hPeriod =>
        field (patch.coordinateMap coordinate))
      (regularFrameSmoothPalatiniCoefficient_frameDerivative period hPeriod
        metric tensor derivative vector)
  have hTermDerivative (vector : Index4) :
      fderiv Real (term vector) coordinate (frame derivative coordinate) =
        coefficient vector coordinate •
            fderiv Real (frame vector) coordinate (frame derivative coordinate) +
          regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
              tensor derivative vector (patch.coordinateMap coordinate) •
            frame vector coordinate := by
    have hProduct := fderiv_smul (hCoefficient vector) (hFrame vector)
    have hApplied := congrArg
      (fun derivativeMap : Vector4 →L[Real] Vector4 =>
        derivativeMap (frame derivative coordinate)) hProduct
    change fderiv Real (coefficient vector • frame vector) coordinate _ = _
    rw [hApplied]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [hCoefficientDerivative]
  have hVectorFunction :
      regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
          patch =
        fun current => ∑ vector : Index4, term vector current := by
    funext current
    unfold regularGeneralMetricC2PalatiniVectorLocal
    apply Finset.sum_congr rfl
    intro vector _
    change
      regularGeneralMetricC2PalatiniFrameCoefficient period hPeriod metric
            tensor (patch.coordinateMap current) vector •
          frame vector current =
        coefficient vector current • frame vector current
    dsimp only [coefficient, Function.comp_apply]
    rw [regularFrameSmoothPalatiniCoefficient_apply]
  have hVectorDerivative :
      fderiv Real
          (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
            patch) coordinate (frame derivative coordinate) =
        ∑ vector : Index4,
          (coefficient vector coordinate •
              fderiv Real (frame vector) coordinate
                (frame derivative coordinate) +
            regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod
                metric tensor derivative vector
                  (patch.coordinateMap coordinate) • frame vector coordinate) := by
    rw [hVectorFunction]
    have hSum := fderiv_fun_sum (u := Finset.univ)
      (fun vector _ => hTerm vector)
    have hApplied := congrArg
      (fun derivativeMap : Vector4 →L[Real] Vector4 =>
        derivativeMap (frame derivative coordinate)) hSum
    rw [hApplied]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro vector _
    exact hTermDerivative vector
  have hVectorPoint :
      regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
          patch coordinate =
        ∑ vector : Index4,
          coefficient vector coordinate • frame vector coordinate := by
    rw [hVectorFunction]
  have hConnection :
      localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric patch
          coordinate (frame derivative coordinate)
          (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
            patch coordinate) =
        ∑ vector : Index4,
          coefficient vector coordinate •
            localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric
              patch coordinate (frame derivative coordinate)
                (frame vector coordinate) := by
    rw [hVectorPoint, map_sum]
    apply Finset.sum_congr rfl
    intro vector _
    rw [map_smul]
  change
    fderiv Real
          (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
            patch) coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate) +
        localLeviCivitaChristoffelBilinearMap period hPeriod metric.metric patch
          coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)
          (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
            patch coordinate) = _
  rw [hVectorDerivative, hConnection]
  simp only [regularFrameLocalCovariantDerivativeVector,
    localLeviCivitaChristoffelBilinearMap_apply, smul_add,
    Finset.sum_add_distrib]
  dsimp only [coefficient, frame]
  simp only [Function.comp_apply]
  abel

private theorem regularGeneralMetricC2PalatiniLocalCovariantDerivative_frame_repr
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative vector : Index4) :
    (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (regularGeneralMetricC2PalatiniLocalCovariantDerivative period hPeriod
          metric tensor patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch derivative
            coordinate)) vector =
      regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
          tensor derivative vector (patch.coordinateMap coordinate) +
        ∑ auxiliary : Index4,
          regularFrameSmoothChristoffelCoefficient period hPeriod metric vector
              derivative auxiliary (patch.coordinateMap coordinate) *
      regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              auxiliary (patch.coordinateMap coordinate) := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  have hReconstruction := congrArg (fun value => basis.repr value vector)
    (regularGeneralMetricC2PalatiniLocalCovariantDerivative_frame period
      hPeriod metric tensor patch coordinate derivative)
  rw [map_add, map_sum, map_sum] at hReconstruction
  simp_rw [map_smul] at hReconstruction
  have hFrame (upper : Index4) :
      basis.repr
          (pulledRegularFrameVector period hPeriod metric patch upper
            coordinate) vector = if upper = vector then 1 else 0 := by
    rw [← pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      upper]
    exact basis.repr_self_apply upper vector
  have hConnection (auxiliary : Index4) :
      basis.repr
          (regularFrameLocalCovariantDerivativeVector period hPeriod metric
            patch derivative auxiliary coordinate) vector =
        regularFrameSmoothChristoffelCoefficient period hPeriod metric vector
          derivative auxiliary (patch.coordinateMap coordinate) := by
    rw [regularFrameSmoothChristoffelCoefficient_eq_connection period hPeriod
      metric tensor (patch.coordinateMap coordinate) vector derivative
        auxiliary]
    change basis.repr
        (regularFrameLocalCovariantDerivativeVector period hPeriod metric patch
          derivative auxiliary coordinate) vector =
      regularGeneralMetricC0Christoffel period hPeriod metric 0 vector
        derivative auxiliary (patch.coordinateMap coordinate)
    exact (regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric
      patch coordinate vector derivative auxiliary).symm
  rw [hReconstruction]
  change
    (∑ upper : Index4,
        regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
            tensor derivative upper (patch.coordinateMap coordinate) *
          basis.repr
            (pulledRegularFrameVector period hPeriod metric patch upper
              coordinate) vector) +
      ∑ auxiliary : Index4,
        regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
            auxiliary (patch.coordinateMap coordinate) *
          basis.repr
            (regularFrameLocalCovariantDerivativeVector period hPeriod metric
              patch derivative auxiliary coordinate) vector = _
  simp_rw [hFrame, hConnection]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  apply congrArg
    (regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
      tensor derivative vector (patch.coordinateMap coordinate) + ·)
  apply Finset.sum_congr rfl
  intro auxiliary _
  ring

/-- The local covariant derivative has the same trace in the pulled regular
frame as in the coordinate basis. -/
theorem regularGeneralMetricC2PalatiniLocalCovariantDerivative_trace_eq_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LinearMap.trace Real Vector4
        (regularGeneralMetricC2PalatiniLocalCovariantDerivative period hPeriod
          metric tensor patch coordinate) =
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        (patch.coordinateMap coordinate) := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  rw [LinearMap.trace_eq_matrix_trace Real basis]
  unfold Matrix.trace regularFrameSmoothPalatiniCovariantDivergence
  simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldAdd_apply,
    smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [show basis derivative =
      pulledRegularFrameVector period hPeriod metric patch derivative
        coordinate by
    exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      derivative]
  exact
    regularGeneralMetricC2PalatiniLocalCovariantDerivative_frame_repr period
      hPeriod metric tensor patch coordinate derivative derivative

/-- The actual holonomic divergence equals the smooth regular-frame Palatini
divergence pointwise. -/
theorem regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
        metric tensor patch coordinate =
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        (patch.coordinateMap coordinate) := by
  rw [regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_trace,
    regularGeneralMetricC2PalatiniLocalCovariantDerivative_trace_eq_smooth]

/-- Gate marker for the holonomic/regular-frame divergence bridge. -/
theorem regular_general_metric_c2_smooth_palatini_local_frame_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
        metric tensor patch coordinate =
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        (patch.coordinateMap coordinate) :=
  regularGeneralMetricC2PalatiniLocalCovariantDivergence_eq_smooth period
    hPeriod metric tensor patch coordinate

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalFrameDivergence4D
end JanusFormal
