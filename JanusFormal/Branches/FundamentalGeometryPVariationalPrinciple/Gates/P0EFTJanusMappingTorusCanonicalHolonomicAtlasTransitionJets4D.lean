import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold

/-!
# Canonical quotient-atlas transitions and rebased local jets

The actual reflected-sphere quotient atlas is induced by local sections of the
covering projection.  Its transitions are analytic: locally they are genuine
deck transformations.  This gate exposes that exact transition map and its
`contDiffGroupoid` regularity.

`SmoothHolonomicFrameChart4` is still a supplied total coordinate-map/frame
package and is not constructed by the quotient-atlas API.  Moreover raw metric
and scalar coordinate arrays do not agree literally under a nontrivial change
of coordinates.  The equality interface consumed by the existing overlap gate
is therefore valid only after both jets have been rebased into one common
frame.  This gate proves the reflexive, symmetric and transitive laws of those
rebased agreements, propagates them to Levi--Civita/scalar/stress objects, and
packages the exact residual bridge needed by a future global conservation
gate.  No false equality of unre-based coordinate components is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

/-- Second-order chain rule, stated pointwise so it applies to a local
diffeomorphism germ without requiring a globally smooth inverse extension. -/
private theorem secondFDeriv_comp_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inner : E → F) (outer : F → G) (point : E)
    (hInner : ContDiffAt Real 2 inner point)
    (hOuter : ContDiffAt Real 2 outer (inner point))
    (first second : E) :
    fderiv Real (fderiv Real (outer ∘ inner)) point first second =
      fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real inner point first)
          (fderiv Real inner point second) +
        fderiv Real outer (inner point)
          (fderiv Real (fderiv Real inner) point first second) := by
  have hInnerDiff : DifferentiableAt Real inner point :=
    hInner.differentiableAt (by norm_num)
  have hInnerNear := hInner.eventually (by norm_num)
  have hOuterNearAt := hOuter.eventually (by norm_num)
  have hOuterNear := hInner.continuousAt.eventually hOuterNearAt
  have hFirstDerivative :
      Filter.EventuallyEq (𝓝 point)
        (fderiv Real (outer ∘ inner))
        (fun current =>
          (fderiv Real outer (inner current)).comp
            (fderiv Real inner current)) := by
    filter_upwards [hInnerNear, hOuterNear] with current hCurrentInner
      hCurrentOuter
    exact fderiv_comp current
      (hCurrentOuter.differentiableAt (by norm_num))
      (hCurrentInner.differentiableAt (by norm_num))
  have hSecondDerivative :
      fderiv Real (fderiv Real (outer ∘ inner)) point =
        fderiv Real
          (fun current =>
            (fderiv Real outer (inner current)).comp
              (fderiv Real inner current))
          point :=
    Filter.EventuallyEq.fderiv_eq hFirstDerivative
  rw [hSecondDerivative]
  have hOuterDerivative :
      ContDiffAt Real 1 (fderiv Real outer) (inner point) :=
    hOuter.fderiv_right (m := 1) (by norm_num)
  have hInnerDerivative :
      ContDiffAt Real 1 (fderiv Real inner) point :=
    hInner.fderiv_right (m := 1) (by norm_num)
  have hComposedOuterDerivative :
      DifferentiableAt Real
        (fun current => fderiv Real outer (inner current)) point :=
    (hOuterDerivative.differentiableAt (by norm_num)).comp point hInnerDiff
  have hInnerDerivativeDiff :
      DifferentiableAt Real (fderiv Real inner) point :=
    hInnerDerivative.differentiableAt (by norm_num)
  rw [fderiv_clm_comp hComposedOuterDerivative hInnerDerivativeDiff]
  have hComposedOuterFDeriv :
      fderiv Real (fun current => fderiv Real outer (inner current)) point =
        (fderiv Real (fderiv Real outer) (inner point)).comp
          (fderiv Real inner point) :=
    fderiv_comp point
      (hOuterDerivative.differentiableAt (by norm_num)) hInnerDiff
  rw [hComposedOuterFDeriv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  abel

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

private def matrixEntryContinuousLinearMap
    (first second : Index4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix first second
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp]
private theorem matrixEntryContinuousLinearMap_apply
    (first second : Index4) (matrix : Matrix4) :
    matrixEntryContinuousLinearMap first second matrix =
      matrix first second := rfl

private theorem fderiv_matrix_entry_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (matrix : E → Matrix4) (point direction : E)
    (hMatrix : DifferentiableAt Real matrix point)
    (first second : Index4) :
    fderiv Real (fun current => matrix current first second)
        point direction =
      fderiv Real matrix point direction first second := by
  have hDerivativeMap :
      fderiv Real
          (matrixEntryContinuousLinearMap first second ∘ matrix) point =
        (matrixEntryContinuousLinearMap first second).comp
          (fderiv Real matrix point) :=
    ((matrixEntryContinuousLinearMap first second).hasFDerivAt.comp point
      hMatrix.hasFDerivAt).fderiv
  have hEntryFunction :
      (matrixEntryContinuousLinearMap first second ∘ matrix) =
        fun current => matrix current first second := by
    funext current
    rfl
  rw [hEntryFunction] at hDerivativeMap
  have hDerivative := congrArg
    (fun derivative : E →L[Real] Real => derivative direction)
    hDerivativeMap
  simpa only [ContinuousLinearMap.comp_apply,
    matrixEntryContinuousLinearMap_apply] using hDerivative

set_option backward.isDefEq.respectTransparency false in
/-- Product rule for a matrix-valued bilinear form whose matrix and two vector
arguments all vary. -/
theorem fderiv_matrix_toBilin_dynamic_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (matrix : E → Matrix4) (left right : E → Vector4)
    (point direction : E)
    (hMatrix : DifferentiableAt Real matrix point)
    (hLeft : DifferentiableAt Real left point)
    (hRight : DifferentiableAt Real right point) :
    fderiv Real
        (fun current => Matrix.toBilin' (matrix current)
          (left current) (right current))
        point direction =
      Matrix.toBilin' (matrix point) (fderiv Real left point direction)
          (right point) +
        Matrix.toBilin' (fderiv Real matrix point direction)
          (left point) (right point) +
        Matrix.toBilin' (matrix point) (left point)
          (fderiv Real right point direction) := by
  have hLeftEntry (index : Index4) :
      DifferentiableAt Real (fun current => left current index) point :=
    (differentiableAt_pi.mp hLeft) index
  have hRightEntry (index : Index4) :
      DifferentiableAt Real (fun current => right current index) point :=
    (differentiableAt_pi.mp hRight) index
  have hMatrixEntry (first second : Index4) :
      DifferentiableAt Real (fun current => matrix current first second) point :=
    (differentiableAt_pi.mp ((differentiableAt_pi.mp hMatrix) first)) second
  have hFunction :
      (fun current => Matrix.toBilin' (matrix current)
        (left current) (right current)) =
        (fun current =>
          ∑ first : Index4, ∑ second : Index4,
            left current first * matrix current first second *
              right current second) := by
    funext current
    exact Matrix.toBilin'_apply _ _ _
  rw [hFunction]
  simp only [Matrix.toBilin'_apply]
  rw [fderiv_fun_sum (u := Finset.univ) (fun first _ => by
    exact DifferentiableAt.fun_sum (u := Finset.univ) fun second _ =>
      ((hLeftEntry first).mul (hMatrixEntry first second)).mul
        (hRightEntry second))]
  change
    ContinuousLinearMap.apply Real Real direction
        (∑ first : Index4,
          fderiv Real
            (fun current =>
              ∑ second : Index4,
                left current first * matrix current first second *
                  right current second)
            point) = _
  rw [map_sum]
  simp only [ContinuousLinearMap.apply_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first _
  have hInnerDerivative :
      fderiv Real
          (fun current =>
            ∑ second : Index4,
              left current first * matrix current first second *
                right current second)
          point =
        ∑ second : Index4,
          fderiv Real
            (fun current =>
              left current first * matrix current first second *
                right current second)
            point := by
    apply fderiv_fun_sum
    intro second _
    exact ((hLeftEntry first).mul (hMatrixEntry first second)).mul
      (hRightEntry second)
  rw [hInnerDerivative]
  change
    ContinuousLinearMap.apply Real Real direction
        (∑ second : Index4,
          fderiv Real
            (fun current =>
              left current first * matrix current first second *
                right current second)
            point) = _
  rw [map_sum]
  simp only [ContinuousLinearMap.apply_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro second _
  let leftScalar : E → Real := fun current => left current first
  let matrixScalar : E → Real :=
    fun current => matrix current first second
  let rightScalar : E → Real := fun current => right current second
  have hLeftScalar : DifferentiableAt Real leftScalar point :=
    hLeftEntry first
  have hMatrixScalar : DifferentiableAt Real matrixScalar point :=
    hMatrixEntry first second
  have hRightScalar : DifferentiableAt Real rightScalar point :=
    hRightEntry second
  have hProductDerivative :
      fderiv Real ((leftScalar * matrixScalar) * rightScalar)
          point direction =
        fderiv Real leftScalar point direction *
              matrixScalar point * rightScalar point +
          leftScalar point * fderiv Real matrixScalar point direction *
              rightScalar point +
            leftScalar point * matrixScalar point *
              fderiv Real rightScalar point direction := by
    rw [fderiv_mul (hLeftScalar.mul hMatrixScalar) hRightScalar,
      fderiv_mul hLeftScalar hMatrixScalar]
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hLeftDerivative :
      fderiv Real leftScalar point direction =
        fderiv Real left point direction first := by
    have hDerivative := congrArg
      (fun derivative : E →L[Real] Real => derivative direction)
      (fderiv_apply hLeft first)
    simpa only [leftScalar, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hDerivative
  have hMatrixDerivative :
      fderiv Real matrixScalar point direction =
        fderiv Real matrix point direction first second := by
    exact fderiv_matrix_entry_apply matrix point direction hMatrix first second
  have hRightDerivative :
      fderiv Real rightScalar point direction =
        fderiv Real right point direction second := by
    have hDerivative := congrArg
      (fun derivative : E →L[Real] Real => derivative direction)
      (fderiv_apply hRight second)
    simpa only [rightScalar, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hDerivative
  have hFunctionProduct :
      (fun current =>
        left current first * matrix current first second *
          right current second) =
        (leftScalar * matrixScalar) * rightScalar := by
    funext current
    rfl
  rw [hFunctionProduct, hProductDerivative, hLeftDerivative,
    hMatrixDerivative, hRightDerivative]

/-- Entrywise contraction of two finite covariant matrices. -/
private def matrixEntryContraction (first second : Matrix4) : Real :=
  ∑ i : Index4, ∑ j : Index4, first i j * second i j

private theorem matrixEntryContraction_eq_trace
    (first second : Matrix4) (hSecond : second.transpose = second) :
    matrixEntryContraction first second = Matrix.trace (first * second) := by
  unfold matrixEntryContraction Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hEntry := congrFun (congrFun hSecond j) i
  simp only [Matrix.transpose_apply] at hEntry
  rw [hEntry]

/-- Inverse-metric contraction is invariant when both covariant matrices are
changed by the same invertible congruence. -/
private theorem matrixEntryContraction_congruence
    (transition metric hessian : Matrix4)
    (hTransition : IsUnit transition)
    (hHessian : hessian.transpose = hessian) :
    matrixEntryContraction
        (transition.transpose * metric * transition)⁻¹
        (transition.transpose * hessian * transition) =
      matrixEntryContraction metric⁻¹ hessian := by
  have hTransformedHessian :
      (transition.transpose * hessian * transition).transpose =
        transition.transpose * hessian * transition := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hHessian]
    noncomm_ring
  rw [matrixEntryContraction_eq_trace _ _ hTransformedHessian,
    matrixEntryContraction_eq_trace _ _ hHessian]
  have hTransposeDet : IsUnit transition.transpose.det :=
    Matrix.isUnit_det_transpose transition
      ((Matrix.isUnit_iff_isUnit_det transition).mp hTransition)
  calc
    Matrix.trace
        ((transition.transpose * metric * transition)⁻¹ *
          (transition.transpose * hessian * transition)) =
      Matrix.trace (transition⁻¹ * (metric⁻¹ * hessian) * transition) := by
        congr 1
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
        calc
          (transition⁻¹ * (metric⁻¹ * transition.transpose⁻¹)) *
                (transition.transpose * hessian * transition) =
              transition⁻¹ *
                (metric⁻¹ *
                  (transition.transpose⁻¹ *
                    (transition.transpose * (hessian * transition)))) := by
                      noncomm_ring
          _ = transition⁻¹ * (metric⁻¹ * (hessian * transition)) := by
            rw [Matrix.nonsing_inv_mul_cancel_left transition.transpose
              (hessian * transition) hTransposeDet]
          _ = transition⁻¹ * (metric⁻¹ * hessian) * transition := by
            noncomm_ring
    _ = Matrix.trace (metric⁻¹ * hessian) :=
      Matrix.trace_conj' hTransition (metric⁻¹ * hessian)

/-- Coordinate wave contractions agree under coherent invertible
transformations of the metric and covariant Hessian. -/
theorem covariantScalarJetWave_eq_of_congruence
    (firstMetric secondMetric : FixedSignMetric4)
    (firstJet secondJet : CovariantScalarJet2)
    (transition : Matrix4)
    (hTransition : IsUnit transition)
    (hMetric :
      firstMetric.metric =
        transition.transpose * secondMetric.metric * transition)
    (hHessian :
      firstJet.hessian =
        transition.transpose * secondJet.hessian * transition) :
    covariantScalarJetWave firstMetric firstJet =
      covariantScalarJetWave secondMetric secondJet := by
  unfold covariantScalarJetWave
  rw [hMetric, hHessian]
  exact matrixEntryContraction_congruence transition secondMetric.metric
    secondJet.hessian hTransition secondJet.hessian_symmetric

/-- A torsion-free metric-compatible coordinate connection is uniquely the
Levi--Civita one. -/
theorem christoffel_eq_leviCivita_of_metricCompatible
    (metric : FixedSignMetric4)
    (metricDerivative :
      P0EFTJanusScalarStressLeviCivitaConnectionJet4D.MetricDerivative4)
    (christoffel : Index4 → Index4 → Index4 → Real)
    (torsionFree :
      ∀ upper first second,
        christoffel upper first second =
          christoffel upper second first)
    (metricCompatible :
      ∀ derivative first second,
        metricDerivative derivative first second =
          (∑ upper : Index4,
            christoffel upper derivative first * metric.metric upper second) +
          ∑ upper : Index4,
            christoffel upper derivative second * metric.metric first upper) :
    christoffel = leviCivitaChristoffel metric metricDerivative := by
  funext upper first second
  let candidateVector : Vector4 :=
    fun current => christoffel current first second
  let leviCivitaVector : Vector4 :=
    fun current => leviCivitaChristoffel metric metricDerivative
      current first second
  have hLower (contracted : Index4) :
      (candidateVector ᵥ* metric.metric) contracted =
        (leviCivitaVector ᵥ* metric.metric) contracted := by
    have hFirst := metricCompatible first second contracted
    have hSecond := metricCompatible second first contracted
    have hContracted := metricCompatible contracted first second
    have hMetricFirst (current : Index4) :
        metric.metric second current = metric.metric current second :=
      metric_entry_symmetric metric second current
    have hMetricSecond (current : Index4) :
        metric.metric first current = metric.metric current first :=
      metric_entry_symmetric metric first current
    have hCandidate :
        (candidateVector ᵥ* metric.metric) contracted =
          (1 / 2 : Real) *
            (metricDerivative first second contracted +
              metricDerivative second first contracted -
              metricDerivative contracted first second) := by
      simp only [Matrix.vecMul, dotProduct, candidateVector]
      rw [hFirst, hSecond, hContracted]
      simp_rw [torsionFree _ second first,
        torsionFree _ contracted first,
        torsionFree _ contracted second,
        hMetricFirst, hMetricSecond]
      ring
    have hLeviCivita :=
      leviCivitaChristoffel_contract_metric metric metricDerivative
        first second contracted
    simp only [Matrix.vecMul, dotProduct, leviCivitaVector]
    exact hCandidate.trans hLeviCivita.symm
  have hVectors :
      candidateVector ᵥ* metric.metric =
        leviCivitaVector ᵥ* metric.metric := by
    funext contracted
    exact hLower contracted
  have hCandidateEq :
      candidateVector = leviCivitaVector :=
    Matrix.vecMul_injective_of_isUnit metric.metric_isUnit hVectors
  exact congrFun hCandidateEq upper

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover :=
  MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem symmetricTensor_evaluation_eq_of_heq
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    {firstPoint secondPoint : EffectiveQuotient period hPeriod}
    (hPoint : firstPoint = secondPoint)
    (firstLeft firstRight :
      TangentSpace coverModelWithCorners firstPoint)
    (secondLeft secondRight :
      TangentSpace coverModelWithCorners secondPoint)
    (hLeft : HEq firstLeft secondLeft)
    (hRight : HEq firstRight secondRight) :
    tensor.tensor firstPoint firstLeft firstRight =
      tensor.tensor secondPoint secondLeft secondRight := by
  subst secondPoint
  rw [eq_of_heq hLeft, eq_of_heq hRight]

/-- The genuine quotient chart based at one cover representative. -/
def canonicalQuotientLocalSectionChart
    (anchor : EffectiveCover period hPeriod) :
    OpenPartialHomeomorph (EffectiveQuotient period hPeriod) CoverModel :=
  let hf :=
    (mappingTorusMk_isCoveringMap (sphereData period hPeriod)).isLocalHomeomorph
  (hf.localInverseAt anchor).trans (chartAt CoverModel anchor)

/-- Actual change of coordinates between two local-section charts of the
covering-induced quotient atlas. -/
def canonicalQuotientLocalSectionTransition
    (firstAnchor secondAnchor : EffectiveCover period hPeriod) :
    OpenPartialHomeomorph CoverModel CoverModel :=
  (canonicalQuotientLocalSectionChart
    period hPeriod firstAnchor).symm.trans
      (canonicalQuotientLocalSectionChart period hPeriod secondAnchor)

/-- The raw quotient-atlas transition is analytic.  In particular all first
and second transition jets required by tensorial coordinate laws exist on its
source. -/
theorem canonicalQuotientLocalSectionTransition_mem_contDiffGroupoid
    (firstAnchor secondAnchor : EffectiveCover period hPeriod) :
    canonicalQuotientLocalSectionTransition period hPeriod
        firstAnchor secondAnchor ∈
      contDiffGroupoid ω coverModelWithCorners := by
  exact localSectionChart_transition_mem_groupoid
    coverModelWithCorners ω (sphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)
      firstAnchor secondAnchor

/-- Function-level analytic regularity extracted from the real atlas
transition groupoid certificate. -/
theorem canonicalQuotientLocalSectionTransition_contMDiffOn
    (firstAnchor secondAnchor : EffectiveCover period hPeriod) :
    ContMDiffOn coverModelWithCorners coverModelWithCorners ω
      (canonicalQuotientLocalSectionTransition period hPeriod
        firstAnchor secondAnchor)
      (canonicalQuotientLocalSectionTransition period hPeriod
        firstAnchor secondAnchor).source :=
  contMDiffOn_of_mem_contDiffGroupoid
    (canonicalQuotientLocalSectionTransition_mem_contDiffGroupoid
      period hPeriod firstAnchor secondAnchor)

/-- Genuine coordinate change from a first supplied holonomic patch to the
local inverse of a second patch at a common represented point. -/
def holonomicCoordinateTransitionAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (_samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    Vector4 → Vector4 :=
  (secondPatch.coordinateMap_isLocalDiffeomorph
    secondCoordinate).localInverse ∘ firstPatch.coordinateMap

@[simp] theorem holonomicCoordinateTransitionAt_apply
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint firstCoordinate =
      secondCoordinate := by
  unfold holonomicCoordinateTransitionAt
  rw [Function.comp_apply, samePoint]
  let secondLocal :=
    secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate
  exact secondLocal.localInverse_left_inv secondLocal.localInverse_mem_target

/-- The genuine transition is a smooth local diffeomorphism at the selected
overlap coordinate. -/
theorem holonomicCoordinateTransitionAt_isLocalDiffeomorphAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    IsLocalDiffeomorphAt (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4) ∞
      (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint)
      firstCoordinate := by
  have firstLocal :=
    firstPatch.coordinateMap_isLocalDiffeomorph firstCoordinate
  have secondInverseLocal :=
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.localInverse_isLocalDiffeomorphAt
  have secondInverseLocal' :
      IsLocalDiffeomorphAt coverModelWithCorners
        (modelWithCornersSelf Real Vector4) ∞
        (secondPatch.coordinateMap_isLocalDiffeomorph
          secondCoordinate).localInverse
        (firstPatch.coordinateMap firstCoordinate) := by
    simpa only [samePoint] using secondInverseLocal
  simpa only [holonomicCoordinateTransitionAt] using
    (IsLocalDiffeomorphAt.comp
      (K := modelWithCornersSelf Real Vector4)
      (P := Vector4)
      firstLocal secondInverseLocal')

/-- Near the selected overlap, composing the transition with the second
coordinate map reconstructs the first coordinate map. -/
theorem holonomicCoordinateTransitionAt_eventually_reconstructs
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    (fun coordinate =>
      secondPatch.coordinateMap
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint coordinate)) =ᶠ[
        𝓝 firstCoordinate]
      firstPatch.coordinateMap := by
  have transitionIdentity :=
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.localInverse_eventuallyEq_right
  have firstTendsto :
      Filter.Tendsto firstPatch.coordinateMap (𝓝 firstCoordinate)
        (𝓝 (secondPatch.coordinateMap secondCoordinate)) := by
    rw [← samePoint]
    exact firstPatch.coordinateMap_contMDiff.continuous.continuousAt
  simpa only [holonomicCoordinateTransitionAt, Function.comp_def, id_eq] using
    transitionIdentity.comp_tendsto firstTendsto

/-- The derivative of the genuine coordinate transition, bundled as a
continuous linear equivalence. -/
def holonomicCoordinateTransitionLinearEquivAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    Vector4 ≃L[Real] Vector4 :=
  (holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.mfderivToContinuousLinearEquiv (by simp)

/-- The bundled transition equivalence is exactly the Fréchet derivative of
the genuine coordinate change. -/
theorem holonomicCoordinateTransitionLinearEquivAt_coe
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint :
      Vector4 →L[Real] Vector4) =
      fderiv Real
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint)
        firstCoordinate := by
  rw [← mfderiv_eq_fderiv]
  exact
    (holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
        |>.mfderivToContinuousLinearEquiv_coe (by simp)

/-- Matrix of the genuine transition Jacobian in the standard coordinate
basis. -/
def holonomicCoordinateTransitionMatrixAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) : Matrix4 :=
  LinearMap.toMatrix (Pi.basisFun Real Index4) (Pi.basisFun Real Index4)
    ((holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint)
        |>.toLinearEquiv.toLinearMap)

theorem holonomicCoordinateTransitionMatrixAt_isUnit
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    IsUnit (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint) := by
  apply (LinearMap.isUnit_toMatrix_iff (Pi.basisFun Real Index4)).2
  apply (LinearMap.isUnit_iff_ker_eq_bot _).2
  apply LinearMap.ker_eq_bot.mpr
  exact
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).injective

@[simp] theorem holonomicCoordinateTransitionMatrixAt_apply
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (row column : Index4) :
    holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint row column =
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
        (Pi.single column 1) row := by
  unfold holonomicCoordinateTransitionMatrixAt
  rw [LinearMap.toMatrix_apply]
  simp

/-- Differentiating the local reconstruction gives equality of the two
manifold derivatives before expanding the chain rule. -/
theorem holonomicCoordinateMap_comp_transition_mfderiv
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        (fun coordinate =>
          secondPatch.coordinateMap
            (holonomicCoordinateTransitionAt period hPeriod firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint
              coordinate))
        firstCoordinate =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        firstPatch.coordinateMap firstCoordinate :=
  Filter.EventuallyEq.mfderiv_eq
    (I := modelWithCornersSelf Real Vector4)
    (I' := coverModelWithCorners)
    (holonomicCoordinateTransitionAt_eventually_reconstructs period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)

/-- The first coordinate derivative is the second coordinate derivative
applied to the genuine transition Jacobian.  `HEq` records the equality across
the definitionally different tangent fibers over the equal quotient points. -/
theorem holonomicCoordinateMap_mfderiv_transition_heq
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate vector : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    HEq
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        firstPatch.coordinateMap firstCoordinate vector)
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        secondPatch.coordinateMap secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint vector)) := by
  have hTransition :
      MDifferentiableAt (modelWithCornersSelf Real Vector4)
        (modelWithCornersSelf Real Vector4)
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint)
        firstCoordinate :=
    (holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
        |>.mdifferentiableAt (by simp)
  have hSecond :
      MDifferentiableAt (modelWithCornersSelf Real Vector4)
        coverModelWithCorners secondPatch.coordinateMap secondCoordinate :=
    secondPatch.coordinateMap_contMDiff.mdifferentiable (by simp)
      secondCoordinate
  have hSecondAtTransition :
      MDifferentiableAt (modelWithCornersSelf Real Vector4)
        coverModelWithCorners secondPatch.coordinateMap
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint firstCoordinate) := by
    simpa only [holonomicCoordinateTransitionAt_apply] using hSecond
  have hDerivative := congrArg (fun derivative => derivative vector)
    (holonomicCoordinateMap_comp_transition_mfderiv period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint)
  change
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          (secondPatch.coordinateMap ∘
            holonomicCoordinateTransitionAt period hPeriod firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint)
          firstCoordinate vector =
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          firstPatch.coordinateMap firstCoordinate vector at hDerivative
  rw [mfderiv_comp_apply firstCoordinate hSecondAtTransition hTransition vector]
    at hDerivative
  rw [mfderiv_eq_fderiv] at hDerivative
  rw [holonomicCoordinateTransitionAt_apply,
    ← holonomicCoordinateTransitionLinearEquivAt_coe] at hDerivative
  exact (heq_of_eq hDerivative).symm

/-- Transition law for each actual holonomic frame vector. -/
theorem holonomicFrame_transition_heq
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (index : Index4) :
    HEq (firstPatch.frame firstCoordinate index)
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        secondPatch.coordinateMap secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single index 1))) := by
  rw [firstPatch.frame_eq_coordinateDerivative]
  exact holonomicCoordinateMap_mfderiv_transition_heq period hPeriod
    firstPatch secondPatch firstCoordinate secondCoordinate
      (Pi.single index 1) samePoint

/-- The coordinate derivative is the linear equivalence from the standard
basis to the supplied holonomic frame. -/
theorem coordinateMap_mfderiv_eq_frameEquiv
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate vector =
      ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
        (Equiv.refl Index4)) vector := by
  let coordinateDerivative :
      Vector4 →ₗ[Real]
        TangentSpace coverModelWithCorners
          (patch.coordinateMap coordinate) :=
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate).toLinearMap.comp
        (NormedSpace.fromTangentSpace coordinate).symm.toLinearEquiv.toLinearMap
  have hLinear :
      coordinateDerivative =
        ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)).toLinearMap := by
    apply (Pi.basisFun Real Index4).ext
    intro index
    have hFrameEquiv :
        ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)).toLinearMap
            ((Pi.basisFun Real Index4) index) =
          patch.frame coordinate index := by
      exact Module.Basis.equiv_apply _ _ _ _
    rw [hFrameEquiv]
    simpa [coordinateDerivative, NormedSpace.fromTangentSpace] using
      (patch.frame_eq_coordinateDerivative coordinate index).symm
  have hApply := LinearMap.congr_fun hLinear vector
  change mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate vector =
    ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
      (Equiv.refl Index4)) vector at hApply
  exact hApply

private theorem bilinForm_apply_transition_eq_congruence_entry
    (form : LinearMap.BilinForm Real Vector4)
    (transition : Vector4 →ₗ[Real] Vector4)
    (first second : Index4) :
    form (transition (Pi.single first 1))
        (transition (Pi.single second 1)) =
      ((LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transition).transpose *
        LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4) form *
        LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transition) first second := by
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_comp
      (b := Pi.basisFun Real Index4)
      (c := Pi.basisFun Real Index4) form transition transition
  have hEntry := congrFun (congrFun hCongruence first) second
  simpa [LinearMap.BilinForm.toMatrix_apply] using hEntry

private theorem continuousLinearMap_apply_eq_sum_basis
    (linear : Vector4 →L[Real] Real) (vector : Vector4) :
    linear vector =
      ∑ index : Index4, vector index * linear (Pi.single index 1) := by
  have hVector :
      vector = ∑ index : Index4, vector index • Pi.single index 1 := by
    ext index
    simp [Pi.single_apply]
  conv_lhs => rw [hVector]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

private theorem matrix_toBilin_transition_eq_congruence_entry
    (hessian : Matrix4) (transition : Vector4 →ₗ[Real] Vector4)
    (first second : Index4) :
    Matrix.toBilin' hessian (transition (Pi.single first 1))
        (transition (Pi.single second 1)) =
      ((LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transition).transpose *
        hessian *
        LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transition) first second := by
  simpa [LinearMap.BilinForm.toMatrix_basisFun] using
    (bilinForm_apply_transition_eq_congruence_entry
      (Matrix.toBilin' hessian) transition first second)

/-- Intrinsic metric coefficients transform by evaluating the second chart
derivative on the genuine transition Jacobian columns. -/
theorem localMetricCoefficient_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    localMetricCoefficient period hPeriod metric firstPatch first second
        firstCoordinate =
      metric.tensor.tensor (secondPatch.coordinateMap secondCoordinate)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          secondPatch.coordinateMap secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1)))
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          secondPatch.coordinateMap secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1))) := by
  have hFirst := holonomicFrame_transition_heq period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint first
  have hSecond := holonomicFrame_transition_heq period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint second
  unfold localMetricCoefficient
  exact symmetricTensor_evaluation_eq_of_heq period hPeriod metric.tensor
    samePoint _ _ _ _ hFirst hSecond

/-- The metric congruence is forced by the genuine transition Jacobian; it is
not an additional atlas hypothesis. -/
theorem localMetricMatrix_transition_congruence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localMetricMatrix period hPeriod metric firstPatch firstCoordinate =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint).transpose *
        localMetricMatrix period hPeriod metric secondPatch secondCoordinate *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint := by
  let secondFrameEquiv :=
    (Pi.basisFun Real Index4).equiv (secondPatch.frame secondCoordinate)
      (Equiv.refl Index4)
  let secondCoordinateMetric : LinearMap.BilinForm Real Vector4 :=
    (metric.tensor.tensor
        (secondPatch.coordinateMap secondCoordinate)).toBilinForm.comp
      secondFrameEquiv.toLinearMap secondFrameEquiv.toLinearMap
  have hSecondMatrix :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4)
          secondCoordinateMetric =
        localMetricMatrix period hPeriod metric secondPatch secondCoordinate := by
    ext first second
    have hFirst :
        secondFrameEquiv ((Pi.basisFun Real Index4) first) =
          secondPatch.frame secondCoordinate first := by
      exact Module.Basis.equiv_apply _ _ _ _
    have hSecond :
        secondFrameEquiv ((Pi.basisFun Real Index4) second) =
          secondPatch.frame secondCoordinate second := by
      exact Module.Basis.equiv_apply _ _ _ _
    rw [LinearMap.BilinForm.toMatrix_apply]
    change metric.tensor.tensor (secondPatch.coordinateMap secondCoordinate)
        (secondFrameEquiv ((Pi.basisFun Real Index4) first))
        (secondFrameEquiv ((Pi.basisFun Real Index4) second)) =
      metric.tensor.tensor (secondPatch.coordinateMap secondCoordinate)
        (secondPatch.frame secondCoordinate first)
        (secondPatch.frame secondCoordinate second)
    rw [hFirst, hSecond]
  ext first second
  rw [show localMetricMatrix period hPeriod metric firstPatch firstCoordinate
      first second =
        localMetricCoefficient period hPeriod metric firstPatch first second
          firstCoordinate by rfl]
  rw [localMetricCoefficient_transition period hPeriod metric firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint first second]
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod secondPatch,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod secondPatch]
  let transitionLinear : Vector4 →ₗ[Real] Vector4 :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).toLinearEquiv.toLinearMap
  have hCongruence :=
    bilinForm_apply_transition_eq_congruence_entry secondCoordinateMetric
      transitionLinear first second
  rw [hSecondMatrix] at hCongruence
  simpa [transitionLinear, holonomicCoordinateTransitionMatrixAt,
    secondCoordinateMetric, secondFrameEquiv] using hCongruence

/-- Metric bilinear form in coordinate components. -/
def localMetricCoordinateForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : LinearMap.BilinForm Real Vector4 :=
  Matrix.toBilin' (localMetricMatrix period hPeriod metric patch coordinate)

/-- The coordinate metric form evaluates the intrinsic tensor on coordinate
derivatives. -/
theorem localMetricCoordinateForm_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : Vector4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        firstVector secondVector =
      metric.tensor.tensor (patch.coordinateMap coordinate)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate firstVector)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate secondVector) := by
  let frameEquiv :=
    (Pi.basisFun Real Index4).equiv (patch.frame coordinate)
      (Equiv.refl Index4)
  let coordinateMetric : LinearMap.BilinForm Real Vector4 :=
    (metric.tensor.tensor (patch.coordinateMap coordinate)).toBilinForm.comp
      frameEquiv.toLinearMap frameEquiv.toLinearMap
  have hMatrix :
      localMetricMatrix period hPeriod metric patch coordinate =
        LinearMap.BilinForm.toMatrix' coordinateMetric := by
    ext first second
    have hFirst :
        frameEquiv ((Pi.basisFun Real Index4) first) =
          patch.frame coordinate first := by
      exact Module.Basis.equiv_apply _ _ _ _
    have hSecond :
        frameEquiv ((Pi.basisFun Real Index4) second) =
          patch.frame coordinate second := by
      exact Module.Basis.equiv_apply _ _ _ _
    change metric.tensor.tensor (patch.coordinateMap coordinate)
        (patch.frame coordinate first) (patch.frame coordinate second) =
      coordinateMetric (Pi.single first 1) (Pi.single second 1)
    dsimp only [coordinateMetric]
    rw [LinearMap.BilinForm.comp_apply]
    change metric.tensor.tensor (patch.coordinateMap coordinate)
        (patch.frame coordinate first) (patch.frame coordinate second) =
      metric.tensor.tensor (patch.coordinateMap coordinate)
        (frameEquiv (Pi.single first 1))
        (frameEquiv (Pi.single second 1))
    have hFirstSingle :
        frameEquiv (Pi.single first 1) =
          patch.frame coordinate first := by
      simpa only [Pi.basisFun_apply] using hFirst
    have hSecondSingle :
        frameEquiv (Pi.single second 1) =
          patch.frame coordinate second := by
      simpa only [Pi.basisFun_apply] using hSecond
    rw [hFirstSingle, hSecondSingle]
  rw [localMetricCoordinateForm, hMatrix,
    Matrix.toBilin'_toMatrix']
  change metric.tensor.tensor (patch.coordinateMap coordinate)
      (frameEquiv firstVector) (frameEquiv secondVector) = _
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch]

/-- The coordinate metric form pulls back along the genuine transition
Jacobian on arbitrary vectors. -/
theorem localMetricCoordinateForm_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate firstVector secondVector : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localMetricCoordinateForm period hPeriod metric firstPatch firstCoordinate
        firstVector secondVector =
      localMetricCoordinateForm period hPeriod metric secondPatch
        secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint firstVector)
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          secondVector) := by
  rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
  have hFirst :=
    holonomicCoordinateMap_mfderiv_transition_heq period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate firstVector samePoint
  have hSecond :=
    holonomicCoordinateMap_mfderiv_transition_heq period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate secondVector samePoint
  exact symmetricTensor_evaluation_eq_of_heq period hPeriod metric.tensor
    samePoint _ _ _ _ hFirst hSecond

/-- Open coordinate domain on which the selected local inverse reconstructs
the first chart. -/
def holonomicCoordinateTransitionDomainAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (_samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) : Set Vector4 :=
  firstPatch.coordinateMap ⁻¹'
    ((secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.localInverse.source)

theorem holonomicCoordinateTransitionDomainAt_isOpen
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    IsOpen (holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint) :=
  ((secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
    |>.localInverse_open_source).preimage
      firstPatch.coordinateMap_contMDiff.continuous

theorem firstCoordinate_mem_holonomicCoordinateTransitionDomainAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    firstCoordinate ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint := by
  unfold holonomicCoordinateTransitionDomainAt
  rw [Set.mem_preimage, samePoint]
  exact (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
    |>.localInverse_mem_source

theorem holonomicCoordinateTransitionAt_reconstructs_of_mem
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint) :
    secondPatch.coordinateMap
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint current) =
      firstPatch.coordinateMap current := by
  unfold holonomicCoordinateTransitionDomainAt at hCurrent
  exact (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
    |>.localInverse_right_inv hCurrent

/-- Chain rule on the whole selected inverse domain, not only at its anchor. -/
theorem holonomicCoordinateMap_mfderiv_transition_heq_of_mem
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current vector : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint) :
    HEq
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        firstPatch.coordinateMap current vector)
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        secondPatch.coordinateMap
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint current)
        (fderiv Real
          (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint) current vector)) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have hPoint :=
    holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current samePoint
      hCurrent
  have hLocal :
      (fun coordinate => secondPatch.coordinateMap (transition coordinate)) =ᶠ[
          𝓝 current] firstPatch.coordinateMap := by
    apply Filter.eventuallyEq_of_mem
      ((holonomicCoordinateTransitionDomainAt_isOpen period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint).mem_nhds
          hCurrent)
    intro coordinate hCoordinate
    exact holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate coordinate
      samePoint hCoordinate
  have hFirstLocal :=
    firstPatch.coordinateMap_isLocalDiffeomorph current
  have hInverseLocal :
      IsLocalDiffeomorphAt coverModelWithCorners
        (modelWithCornersSelf Real Vector4) ∞
        (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate
          |>.localInverse)
        (firstPatch.coordinateMap current) :=
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.localInverse.isLocalDiffeomorphAt _ _ _ hCurrent
  have hTransition :
      MDifferentiableAt (modelWithCornersSelf Real Vector4)
        (modelWithCornersSelf Real Vector4) transition current := by
    exact (IsLocalDiffeomorphAt.comp
      (K := modelWithCornersSelf Real Vector4) (P := Vector4)
      hFirstLocal hInverseLocal).mdifferentiableAt (by simp)
  have hSecond :
      MDifferentiableAt (modelWithCornersSelf Real Vector4)
        coverModelWithCorners secondPatch.coordinateMap (transition current) :=
    secondPatch.coordinateMap_contMDiff.mdifferentiable (by simp) _
  have hMFDeriv :
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          (fun coordinate => secondPatch.coordinateMap (transition coordinate))
          current =
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          firstPatch.coordinateMap current :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real Vector4)
      (I' := coverModelWithCorners) hLocal
  have hDerivative := congrArg (fun derivative => derivative vector) hMFDeriv
  change
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          (secondPatch.coordinateMap ∘ transition) current vector =
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          firstPatch.coordinateMap current vector at hDerivative
  rw [mfderiv_comp_apply current hSecond hTransition vector,
    mfderiv_eq_fderiv] at hDerivative
  exact (heq_of_eq hDerivative).symm

/-- On the local inverse domain, the first metric coefficient is the pullback
of the second coordinate metric by the varying transition derivative. -/
theorem localMetricCoefficient_eq_transitionPullback_of_mem
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate current : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hCurrent : current ∈
      holonomicCoordinateTransitionDomainAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint)
    (first second : Index4) :
    localMetricCoefficient period hPeriod metric firstPatch first second current =
      localMetricCoordinateForm period hPeriod metric secondPatch
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
  rw [localMetricCoordinateForm_apply]
  unfold localMetricCoefficient
  rw [firstPatch.frame_eq_coordinateDerivative,
    firstPatch.frame_eq_coordinateDerivative]
  exact symmetricTensor_evaluation_eq_of_heq period hPeriod metric.tensor
    hPoint.symm _ _ _ _ hFirst hSecond

/-- Germ-level pullback identity for metric coefficients. -/
theorem localMetricCoefficient_transitionPullback_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    localMetricCoefficient period hPeriod metric firstPatch first second =ᶠ[
        𝓝 firstCoordinate]
      fun current =>
        localMetricCoordinateForm period hPeriod metric secondPatch
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
  exact localMetricCoefficient_eq_transitionPullback_of_mem period hPeriod
    metric firstPatch secondPatch firstCoordinate secondCoordinate current
    samePoint hCurrent first second

/-- First differential of a quotient scalar in one coordinate chart. -/
def localScalarDifferentialAt
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 →L[Real] Real :=
  fderiv Real (localScalarRepresentative period hPeriod field patch) coordinate

/-- Second differential of a quotient scalar as a bilinear form. -/
def localScalarSecondDifferentialFormAt
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : LinearMap.BilinForm Real Vector4 :=
  (fderiv Real
    (fderiv Real (localScalarRepresentative period hPeriod field patch))
    coordinate).toBilinForm

@[simp] theorem localScalarDifferentialAt_basis
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Index4) :
    localScalarDifferentialAt period hPeriod field patch coordinate
        (Pi.single index 1) =
      localScalarGradient period hPeriod field patch coordinate index := by
  rfl

@[simp] theorem localScalarSecondDifferentialFormAt_basis
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    localScalarSecondDifferentialFormAt period hPeriod field patch coordinate
        (Pi.single first 1) (Pi.single second 1) =
      localScalarPartialGradient period hPeriod field patch coordinate
        first second := by
  rfl

/-- Matrix of Christoffel coefficients with the upper index fixed. -/
def localLeviCivitaChristoffelMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper : Index4) : Matrix4 :=
  fun first second =>
    localLeviCivitaChristoffel period hPeriod metric patch coordinate
      upper first second

/-- Bilinear Christoffel map, valued in coordinate vectors. -/
def localLeviCivitaChristoffelApply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : Vector4) : Vector4 :=
  fun upper =>
    Matrix.toBilin'
      (localLeviCivitaChristoffelMatrix period hPeriod metric patch coordinate
        upper) firstVector secondVector

/-- The coordinate derivative of the metric, bundled as a trilinear form. -/
def localMetricDerivativeTrilinearForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real where
  toFun direction :=
    Matrix.toBilin'
      (fderiv Real
        (localMetricMatrix period hPeriod metric patch) coordinate direction)
  map_add' first second := by
    simp
  map_smul' scalar direction := by
    simp

@[simp]
theorem localMetricDerivativeTrilinearForm_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate direction firstVector secondVector : Vector4) :
    localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate
        direction firstVector secondVector =
      Matrix.toBilin'
        (fderiv Real
          (localMetricMatrix period hPeriod metric patch) coordinate direction)
        firstVector secondVector :=
  rfl

@[simp]
theorem localMetricDerivativeTrilinearForm_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate
        (Pi.single derivative 1) (Pi.single first 1) (Pi.single second 1) =
      localMetricDerivative period hPeriod metric patch coordinate
        derivative first second := by
  rw [localMetricDerivativeTrilinearForm_apply, Matrix.toBilin'_single]
  unfold localMetricDerivative
  have hMatrix :
      DifferentiableAt Real
        (localMetricMatrix period hPeriod metric patch) coordinate :=
    (localMetricMatrix_contDiff period hPeriod metric patch).differentiable
      (by simp) coordinate
  simpa only [localMetricMatrix] using
    (fderiv_matrix_entry_apply
      (localMetricMatrix period hPeriod metric patch) coordinate
      (Pi.single derivative 1) hMatrix first second).symm

/-- The local Christoffel coefficients as a vector-valued bilinear map. -/
def localLeviCivitaChristoffelBilinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 where
  toFun firstVector :=
    { toFun := fun secondVector =>
        localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          firstVector secondVector
      map_add' := by
        intro first second
        ext upper
        simp [localLeviCivitaChristoffelApply]
      map_smul' := by
        intro scalar vector
        ext upper
        simp [localLeviCivitaChristoffelApply] }
  map_add' := by
    intro first second
    ext vector upper
    simp [localLeviCivitaChristoffelApply]
  map_smul' := by
    intro scalar vector
    ext secondVector upper
    simp [localLeviCivitaChristoffelApply]

@[simp]
theorem localLeviCivitaChristoffelBilinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : Vector4) :
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
        coordinate firstVector secondVector =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        firstVector secondVector :=
  rfl

@[simp]
theorem localLeviCivitaChristoffelBilinearMap_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
        (Pi.single first 1) (Pi.single second 1) =
      fun upper =>
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper first second := by
  ext upper
  simp [localLeviCivitaChristoffelBilinearMap,
    localLeviCivitaChristoffelApply, localLeviCivitaChristoffelMatrix,
    Matrix.toBilin'_single]

theorem localMetricCoordinateForm_apply_basis_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) (second : Index4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        vector (Pi.single second 1) =
      ∑ first : Index4,
        vector first *
          localMetricMatrix period hPeriod metric patch coordinate first second := by
  simp [localMetricCoordinateForm, Matrix.toBilin'_apply, Pi.single_apply]

theorem localMetricCoordinateForm_apply_basis_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) (first : Index4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (Pi.single first 1) vector =
      ∑ second : Index4,
        localMetricMatrix period hPeriod metric patch coordinate first second *
          vector second := by
  simp [localMetricCoordinateForm, Matrix.toBilin'_apply, Pi.single_apply]

/-- Metric compatibility written as a trilinear identity on arbitrary
coordinate vectors. -/
def localLeviCivitaMetricCompatibilityForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 →ₗ[Real] Real := by
  let metricForm :=
    localMetricCoordinateForm period hPeriod metric patch coordinate
  let christoffelForm :=
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
  exact
    { toFun := fun derivative =>
        { toFun := fun first =>
            { toFun := fun second =>
                metricForm (christoffelForm derivative first) second +
                  metricForm first (christoffelForm derivative second)
              map_add' := by
                intro second third
                simp
                ring
              map_smul' := by
                intro scalar second
                simp
                ring }
          map_add' := by
            intro first second
            ext third
            simp
            ring
          map_smul' := by
            intro scalar first
            ext second
            simp
            ring }
      map_add' := by
        intro first second
        ext third fourth
        simp
        ring
      map_smul' := by
        intro scalar first
        ext second third
        simp
        ring }

@[simp]
theorem localLeviCivitaMetricCompatibilityForm_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate derivative first second : Vector4) :
    localLeviCivitaMetricCompatibilityForm period hPeriod metric patch
        coordinate derivative first second =
      localMetricCoordinateForm period hPeriod metric patch coordinate
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate derivative first) second +
        localMetricCoordinateForm period hPeriod metric patch coordinate first
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate derivative second) :=
  rfl

/-- Levi--Civita metric compatibility holds on arbitrary coordinate vectors,
not only on basis components. -/
theorem localMetricDerivativeTrilinearForm_eq_leviCivita
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate =
      localLeviCivitaMetricCompatibilityForm period hPeriod metric patch
        coordinate := by
  apply (Pi.basisFun Real Index4).ext
  intro derivative
  apply (Pi.basisFun Real Index4).ext
  intro first
  apply (Pi.basisFun Real Index4).ext
  intro second
  simp only [Pi.basisFun_apply]
  rw [localMetricDerivativeTrilinearForm_basis,
    localLeviCivitaMetricCompatibilityForm_apply,
    localLeviCivitaChristoffelBilinearMap_basis,
    localLeviCivitaChristoffelBilinearMap_basis,
    localMetricCoordinateForm_apply_basis_right,
    localMetricCoordinateForm_apply_basis_left]
  have hCompatibility :=
    (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
      |>.metricCompatible derivative first second
  change
      localMetricDerivative period hPeriod metric patch coordinate
          derivative first second =
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
  rw [hCompatibility]
  congr 1
  apply Finset.sum_congr rfl
  intro upper _
  simp only [localMetricMatrix]
  ring

/-- Bilinear Christoffel correction paired with a scalar differential. -/
def localScalarChristoffelCorrectionForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : LinearMap.BilinForm Real Vector4 :=
  ∑ upper : Index4,
    localScalarGradient period hPeriod field patch coordinate upper •
      Matrix.toBilin'
        (localLeviCivitaChristoffelMatrix period hPeriod metric patch
          coordinate upper)

/-- The component Christoffel correction is exactly evaluation of the scalar
differential on the vector-valued Christoffel map. -/
theorem localScalarChristoffelCorrectionForm_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : Vector4) :
    localScalarChristoffelCorrectionForm period hPeriod metric field patch
        coordinate firstVector secondVector =
      localScalarDifferentialAt period hPeriod field patch coordinate
        (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
          firstVector secondVector) := by
  rw [continuousLinearMap_apply_eq_sum_basis]
  simp only [localScalarChristoffelCorrectionForm,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    localScalarDifferentialAt_basis, localLeviCivitaChristoffelApply]
  apply Finset.sum_congr rfl
  intro upper _
  ring

/-- Covariant Hessian as a bilinear form. -/
def localCovariantScalarHessianForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : LinearMap.BilinForm Real Vector4 :=
  Matrix.toBilin'
    (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian

/-- The local covariant Hessian is the second differential minus the
Christoffel correction, now as an equality of bilinear forms. -/
theorem localCovariantScalarHessianForm_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localCovariantScalarHessianForm period hPeriod metric field patch coordinate =
      localScalarSecondDifferentialFormAt period hPeriod field patch coordinate -
        localScalarChristoffelCorrectionForm period hPeriod metric field patch
          coordinate := by
  apply LinearMap.BilinForm.toMatrix'.injective
  ext first second
  simp [localCovariantScalarHessianForm,
    localScalarSecondDifferentialFormAt,
    localScalarChristoffelCorrectionForm,
    localLeviCivitaChristoffelMatrix, localCovariantScalarJet,
    coordinateScalarJetNormalForm, coordinateCovariantHessian,
    localCoordinateScalarJet, LinearMap.BilinForm.toMatrix'_apply, mul_comm]
  simpa [localScalarSecondDifferentialFormAt] using
    (localScalarSecondDifferentialFormAt_basis period hPeriod field patch
      coordinate first second).symm

/-- A scalar representative in the first coordinates is locally the second
representative composed with the genuine transition. -/
theorem localScalarRepresentative_transition_eventuallyEq
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localScalarRepresentative period hPeriod field firstPatch =ᶠ[
        𝓝 firstCoordinate]
      localScalarRepresentative period hPeriod field secondPatch ∘
        holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint := by
  filter_upwards [
    holonomicCoordinateTransitionAt_eventually_reconstructs period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint]
    with coordinate hCoordinate
  unfold localScalarRepresentative
  change field (firstPatch.coordinateMap coordinate) =
    field (secondPatch.coordinateMap
      (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint coordinate))
  rw [hCoordinate]

/-- First-derivative chain rule for the pulled-back scalar representatives. -/
theorem localScalarRepresentative_fderiv_comp_transition
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    fderiv Real (localScalarRepresentative period hPeriod field firstPatch)
        firstCoordinate =
      (fderiv Real
        (localScalarRepresentative period hPeriod field secondPatch)
        secondCoordinate).comp
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint :
          Vector4 →L[Real] Vector4) := by
  have hTransition :
      DifferentiableAt Real
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint)
        firstCoordinate :=
    (holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
        |>.mdifferentiableAt (by simp) |>.differentiableAt
  have hSecond :
      DifferentiableAt Real
        (localScalarRepresentative period hPeriod field secondPatch)
        secondCoordinate :=
    (localScalarRepresentative_contDiff period hPeriod field secondPatch)
      |>.differentiable (by simp) secondCoordinate
  have hSecondAtTransition :
      DifferentiableAt Real
        (localScalarRepresentative period hPeriod field secondPatch)
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint firstCoordinate) := by
    simpa only [holonomicCoordinateTransitionAt_apply] using hSecond
  have hLocal :
      fderiv Real
          (localScalarRepresentative period hPeriod field firstPatch)
          firstCoordinate =
        fderiv Real
          (localScalarRepresentative period hPeriod field secondPatch ∘
            holonomicCoordinateTransitionAt period hPeriod firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint)
          firstCoordinate :=
    (localScalarRepresentative_transition_eventuallyEq period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.fderiv_eq
  calc
    _ = fderiv Real
        (localScalarRepresentative period hPeriod field secondPatch ∘
          holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint)
        firstCoordinate := hLocal
    _ = _ := by
      rw [fderiv_comp firstCoordinate hSecondAtTransition hTransition,
        holonomicCoordinateTransitionAt_apply,
        holonomicCoordinateTransitionLinearEquivAt_coe]

/-- Component form of the scalar-gradient transition law. -/
theorem localScalarGradient_transition
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (index : Index4) :
    localScalarGradient period hPeriod field firstPatch firstCoordinate index =
      fderiv Real (localScalarRepresentative period hPeriod field secondPatch)
        secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single index 1)) := by
  unfold localScalarGradient
  rw [localScalarRepresentative_fderiv_comp_transition period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint]
  rfl

/-- Exact second-order scalar chain rule on an overlap.  The final summand is
the non-tensorial second derivative of the coordinate transition; it is the
term cancelled by the Levi--Civita transformation law. -/
theorem localScalarPartialGradient_transition
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    localScalarPartialGradient period hPeriod field firstPatch firstCoordinate
        first second =
      fderiv Real
          (fderiv Real
            (localScalarRepresentative period hPeriod field secondPatch))
          secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        fderiv Real
          (localScalarRepresentative period hPeriod field secondPatch)
          secondCoordinate
          (fderiv Real
            (fderiv Real
              (holonomicCoordinateTransitionAt period hPeriod firstPatch
                secondPatch firstCoordinate secondCoordinate samePoint))
            firstCoordinate (Pi.single first 1) (Pi.single second 1)) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let firstRepresentative :=
    localScalarRepresentative period hPeriod field firstPatch
  let secondRepresentative :=
    localScalarRepresentative period hPeriod field secondPatch
  have hSecondDerivative :
      fderiv Real (fderiv Real firstRepresentative) firstCoordinate =
        fderiv Real (fderiv Real (secondRepresentative ∘ transition))
          firstCoordinate := by
    exact Filter.EventuallyEq.fderiv_eq
      ((localScalarRepresentative_transition_eventuallyEq period hPeriod field
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
        |>.fderiv)
  have hTransition :
      ContDiffAt Real 2 transition firstCoordinate :=
    ((holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
        |>.contMDiffAt.contDiffAt).of_le (by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hSecondRepresentative :
      ContDiffAt Real 2 secondRepresentative secondCoordinate :=
    ((localScalarRepresentative_contDiff period hPeriod field secondPatch)
      |>.contDiffAt).of_le (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hSecondRepresentativeAtTransition :
      ContDiffAt Real 2 secondRepresentative
        (transition firstCoordinate) := by
    simpa only [transition, holonomicCoordinateTransitionAt_apply] using
      hSecondRepresentative
  unfold localScalarPartialGradient
  change fderiv Real (fderiv Real firstRepresentative) firstCoordinate
      (Pi.single first 1) (Pi.single second 1) = _
  rw [hSecondDerivative]
  rw [secondFDeriv_comp_apply transition secondRepresentative firstCoordinate
    hTransition hSecondRepresentativeAtTransition]
  simp only [transition, secondRepresentative,
    holonomicCoordinateTransitionAt_apply]
  rw [← holonomicCoordinateTransitionLinearEquivAt_coe]
  rfl

/-- Second derivative of the genuine coordinate transition. -/
def holonomicCoordinateTransitionSecondDerivativeAt
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (firstVector secondVector : Vector4) : Vector4 :=
  fderiv Real
      (fderiv Real
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint))
      firstCoordinate firstVector secondVector

private theorem holonomicCoordinateTransitionAt_contDiffAt_two
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    ContDiffAt Real 2
      (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint)
      firstCoordinate :=
  ((holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.contMDiffAt.contDiffAt).of_le (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)

/-- Differentiating the germ-level metric pullback gives the exact
first-derivative transformation law, including both second-derivative terms
of the coordinate transition. -/
theorem localMetricDerivative_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (derivative first second : Index4) :
    localMetricDerivative period hPeriod metric firstPatch firstCoordinate
        derivative first second =
      localMetricCoordinateForm period hPeriod metric secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
            firstPatch secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single derivative 1) (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        localMetricDerivativeTrilinearForm period hPeriod metric secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single derivative 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        localMetricCoordinateForm period hPeriod metric secondPatch
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
  let secondMetricMatrix :=
    localMetricMatrix period hPeriod metric secondPatch
  let left : Vector4 → Vector4 := fun current =>
    fderiv Real transition current (Pi.single first 1)
  let right : Vector4 → Vector4 := fun current =>
    fderiv Real transition current (Pi.single second 1)
  have hTransitionC2 :
      ContDiffAt Real 2 transition firstCoordinate := by
    simpa only [transition] using
      holonomicCoordinateTransitionAt_contDiffAt_two period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
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
  have hSecondMetric :
      DifferentiableAt Real secondMetricMatrix secondCoordinate := by
    exact
      (localMetricMatrix_contDiff period hPeriod metric secondPatch)
        |>.differentiable (by simp) secondCoordinate
  have hSecondMetricAtTransition :
      DifferentiableAt Real secondMetricMatrix
        (transition firstCoordinate) := by
    simpa only [hTransitionAt] using hSecondMetric
  have hMatrixComposition :
      DifferentiableAt Real (secondMetricMatrix ∘ transition)
        firstCoordinate :=
    hSecondMetricAtTransition.comp firstCoordinate hTransition
  have hPullbackFunction :
      (fun current =>
        localMetricCoordinateForm period hPeriod metric secondPatch
          (transition current)
          (fderiv Real transition current (Pi.single first 1))
          (fderiv Real transition current (Pi.single second 1))) =
        fun current =>
          Matrix.toBilin' ((secondMetricMatrix ∘ transition) current)
            (left current) (right current) := by
    funext current
    rfl
  have hDerivativeEquality :
      fderiv Real
          (localMetricCoefficient period hPeriod metric firstPatch first second)
          firstCoordinate =
        fderiv Real
          (fun current =>
            localMetricCoordinateForm period hPeriod metric secondPatch
              (transition current)
              (fderiv Real transition current (Pi.single first 1))
              (fderiv Real transition current (Pi.single second 1)))
          firstCoordinate :=
    Filter.EventuallyEq.fderiv_eq
      (localMetricCoefficient_transitionPullback_eventuallyEq period hPeriod
        metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
        first second)
  have hDerivativeApply := congrArg
    (fun derivativeMap : Vector4 →L[Real] Real =>
      derivativeMap (Pi.single derivative 1))
    hDerivativeEquality
  change
      fderiv Real
          (localMetricCoefficient period hPeriod metric firstPatch first second)
          firstCoordinate (Pi.single derivative 1) =
        fderiv Real
          (fun current =>
            localMetricCoordinateForm period hPeriod metric secondPatch
              (transition current)
              (fderiv Real transition current (Pi.single first 1))
              (fderiv Real transition current (Pi.single second 1)))
          firstCoordinate (Pi.single derivative 1)
    at hDerivativeApply
  rw [hPullbackFunction] at hDerivativeApply
  rw [fderiv_matrix_toBilin_dynamic_apply
    (secondMetricMatrix ∘ transition) left right firstCoordinate
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
      (secondMetricMatrix ∘ transition) firstCoordinate =
        secondMetricMatrix secondCoordinate := by
    rw [Function.comp_apply, hTransitionAt]
  have hMatrixDerivative :
      fderiv Real (secondMetricMatrix ∘ transition) firstCoordinate
          (Pi.single derivative 1) =
        fderiv Real secondMetricMatrix secondCoordinate
          (transitionLinear (Pi.single derivative 1)) := by
    have hChain :
        fderiv Real (secondMetricMatrix ∘ transition) firstCoordinate =
          (fderiv Real secondMetricMatrix (transition firstCoordinate)).comp
            (fderiv Real transition firstCoordinate) :=
      (hSecondMetricAtTransition.hasFDerivAt.comp firstCoordinate
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
  simpa only [localMetricDerivative, localMetricCoordinateForm,
    localMetricDerivativeTrilinearForm_apply, secondMetricMatrix,
    transitionLinear] using hDerivativeApply

/-- The vector-valued Levi--Civita Christoffel map is symmetric in its two
lower vector arguments. -/
theorem localLeviCivitaChristoffelApply_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : Vector4) :
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        firstVector secondVector =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        secondVector firstVector := by
  ext upper
  simp only [localLeviCivitaChristoffelApply, Matrix.toBilin'_apply,
    localLeviCivitaChristoffelMatrix]
  calc
    (∑ first : Index4, ∑ second : Index4,
        firstVector first *
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper first second *
          secondVector second) =
      ∑ first : Index4, ∑ second : Index4,
        secondVector second *
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper second first *
          firstVector first := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        have hTorsion :=
          (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
            |>.torsionFree upper first second
        change
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              upper first second =
            localLeviCivitaChristoffel period hPeriod metric patch coordinate
              upper second first
          at hTorsion
        rw [hTorsion]
        ring
    _ = ∑ second : Index4, ∑ first : Index4,
        secondVector second *
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper second first *
          firstVector first := Finset.sum_comm

/-- Symmetry of the genuine transition's second derivative. -/
theorem holonomicCoordinateTransitionSecondDerivativeAt_symmetric
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate firstVector secondVector : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    holonomicCoordinateTransitionSecondDerivativeAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint firstVector
        secondVector =
      holonomicCoordinateTransitionSecondDerivativeAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint secondVector
        firstVector := by
  have hSymmetric :=
    (holonomicCoordinateTransitionAt_contDiffAt_two period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint)
      |>.isSymmSndFDerivAt (by norm_num)
  exact hSymmetric firstVector secondVector

/-- Pull the second-chart Levi--Civita connection back to first-chart
components by the genuine transition. -/
def pulledBackLeviCivitaChristoffel
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (upper first second : Index4) : Real :=
  (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint).symm
      (localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
          firstPatch secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single first 1) (Pi.single second 1))
    upper

theorem pulledBackLeviCivitaChristoffel_torsionFree
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    ∀ upper first second,
      pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          upper first second =
        pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          upper second first := by
  intro upper first second
  unfold pulledBackLeviCivitaChristoffel
  rw [localLeviCivitaChristoffelApply_symmetric,
    holonomicCoordinateTransitionSecondDerivativeAt_symmetric]

/-- The pulled-back connection is compatible with the first-chart metric. -/
theorem pulledBackLeviCivitaChristoffel_metricCompatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    ∀ derivative first second,
      localMetricDerivative period hPeriod metric firstPatch firstCoordinate
          derivative first second =
        (∑ upper : Index4,
          pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint
              upper derivative first *
            localMetricMatrix period hPeriod metric firstPatch firstCoordinate
              upper second) +
          ∑ upper : Index4,
            pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
                secondPatch firstCoordinate secondCoordinate samePoint
                upper derivative second *
              localMetricMatrix period hPeriod metric firstPatch firstCoordinate
                first upper := by
  intro derivative first second
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let derivativeVector : Vector4 := Pi.single derivative 1
  let firstVector : Vector4 := Pi.single first 1
  let secondVector : Vector4 := Pi.single second 1
  let firstChristoffel : Vector4 :=
    localLeviCivitaChristoffelApply period hPeriod metric secondPatch
      secondCoordinate (transitionLinear derivativeVector)
      (transitionLinear firstVector)
  let secondChristoffel : Vector4 :=
    localLeviCivitaChristoffelApply period hPeriod metric secondPatch
      secondCoordinate (transitionLinear derivativeVector)
      (transitionLinear secondVector)
  let firstTransitionSecond : Vector4 :=
    holonomicCoordinateTransitionSecondDerivativeAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint derivativeVector
      firstVector
  let secondTransitionSecond : Vector4 :=
    holonomicCoordinateTransitionSecondDerivativeAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint derivativeVector
      secondVector
  have hForms :
      localMetricDerivative period hPeriod metric firstPatch firstCoordinate
          derivative first second =
        localMetricCoordinateForm period hPeriod metric firstPatch
            firstCoordinate
            (transitionLinear.symm
              (firstChristoffel + firstTransitionSecond))
            secondVector +
          localMetricCoordinateForm period hPeriod metric firstPatch
            firstCoordinate firstVector
            (transitionLinear.symm
              (secondChristoffel + secondTransitionSecond)) := by
    rw [localMetricDerivative_transition period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint derivative first
      second]
    rw [localMetricDerivativeTrilinearForm_eq_leviCivita,
      localLeviCivitaMetricCompatibilityForm_apply,
      localLeviCivitaChristoffelBilinearMap_apply,
      localLeviCivitaChristoffelBilinearMap_apply]
    rw [localMetricCoordinateForm_transition period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate
      (transitionLinear.symm
        (firstChristoffel + firstTransitionSecond))
      secondVector samePoint]
    rw [localMetricCoordinateForm_transition period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate firstVector
      (transitionLinear.symm
        (secondChristoffel + secondTransitionSecond))
      samePoint]
    rw [transitionLinear.apply_symm_apply,
      transitionLinear.apply_symm_apply]
    simp only [map_add, LinearMap.add_apply]
    dsimp only [transitionLinear, derivativeVector, firstVector, secondVector,
      firstChristoffel, secondChristoffel, firstTransitionSecond,
      secondTransitionSecond]
    ring
  dsimp only [firstVector, secondVector] at hForms
  rw [localMetricCoordinateForm_apply_basis_right,
    localMetricCoordinateForm_apply_basis_left] at hForms
  have hSums :
      localMetricDerivative period hPeriod metric firstPatch firstCoordinate
          derivative first second =
        (∑ upper : Index4,
          pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint
              upper derivative first *
            localMetricMatrix period hPeriod metric firstPatch firstCoordinate
              upper second) +
          ∑ upper : Index4,
            localMetricMatrix period hPeriod metric firstPatch firstCoordinate
                first upper *
              pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
                secondPatch firstCoordinate secondCoordinate samePoint
                upper derivative second := by
    simpa only [pulledBackLeviCivitaChristoffel, transitionLinear,
      derivativeVector, firstChristoffel, secondChristoffel,
      firstTransitionSecond, secondTransitionSecond] using hForms
  rw [hSums]
  congr 1
  apply Finset.sum_congr rfl
  intro upper _
  ring

/-- Uniqueness identifies the pulled-back connection with the first-chart
Levi--Civita connection. -/
theorem pulledBackLeviCivitaChristoffel_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint =
      localLeviCivitaChristoffel period hPeriod metric firstPatch
        firstCoordinate := by
  have hUnique :=
    christoffel_eq_leviCivita_of_metricCompatible
      (localFixedSignMetric period hPeriod metric firstPatch firstCoordinate)
      (localMetricDerivative period hPeriod metric firstPatch firstCoordinate)
      (pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint)
      (pulledBackLeviCivitaChristoffel_torsionFree period hPeriod metric
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      (pulledBackLeviCivitaChristoffel_metricCompatible period hPeriod metric
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
  change
    pulledBackLeviCivitaChristoffel period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint =
      leviCivitaChristoffel
        (localFixedSignMetric period hPeriod metric firstPatch firstCoordinate)
        (localMetricDerivative period hPeriod metric firstPatch firstCoordinate)
  exact hUnique

/-- A scalar differential transforms by precomposition with the genuine
transition Jacobian. -/
theorem localScalarDifferentialAt_transition
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate vector : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localScalarDifferentialAt period hPeriod field firstPatch firstCoordinate
        vector =
      localScalarDifferentialAt period hPeriod field secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint vector) := by
  unfold localScalarDifferentialAt
  rw [localScalarRepresentative_fderiv_comp_transition period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint]
  rfl

/-- The exact coordinate law for the Levi--Civita connection.  It is
field-independent: the Jacobian transports the first Christoffel vector to the
second Christoffel bilinear term plus the second derivative of the coordinate
change. -/
structure HolonomicLeviCivitaTransitionAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4) : Prop where
  samePoint : firstPatch.coordinateMap firstCoordinate =
    secondPatch.coordinateMap secondCoordinate
  christoffel_transform :
    ∀ first second : Index4,
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate (Pi.single first 1) (Pi.single second 1)) =
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate
            (holonomicCoordinateTransitionLinearEquivAt period hPeriod
              firstPatch secondPatch firstCoordinate secondCoordinate samePoint
              (Pi.single first 1))
            (holonomicCoordinateTransitionLinearEquivAt period hPeriod
              firstPatch secondPatch firstCoordinate secondCoordinate samePoint
              (Pi.single second 1)) +
          holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
            firstPatch secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1) (Pi.single second 1)

/-- The genuine chart transition always satisfies the Levi--Civita
connection law; no additional overlap datum is required. -/
theorem canonicalHolonomicLeviCivitaTransitionAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    HolonomicLeviCivitaTransitionAgreement period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate where
  samePoint := samePoint
  christoffel_transform := by
    intro first second
    let transitionLinear :=
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    let transformed : Vector4 :=
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate
          (transitionLinear (Pi.single first 1))
          (transitionLinear (Pi.single second 1)) +
        holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
          firstPatch secondPatch firstCoordinate secondCoordinate samePoint
          (Pi.single first 1) (Pi.single second 1)
    have hConnection :=
      pulledBackLeviCivitaChristoffel_eq period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    have hVector :
        transitionLinear.symm transformed =
          localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate (Pi.single first 1) (Pi.single second 1) := by
      ext upper
      have hComponent :=
        congrFun (congrFun (congrFun hConnection upper) first) second
      simpa only [pulledBackLeviCivitaChristoffel, transitionLinear,
        transformed, localLeviCivitaChristoffelApply,
        localLeviCivitaChristoffelMatrix, Matrix.toBilin'_single] using
        hComponent
    have hApply :=
      congrArg (fun vector : Vector4 => transitionLinear vector) hVector
    rw [transitionLinear.apply_symm_apply] at hApply
    exact hApply.symm

/-- The connection transition law transports the Christoffel correction,
including exactly the non-tensorial second-coordinate-derivative term. -/
theorem localScalarChristoffelCorrectionForm_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : HolonomicLeviCivitaTransitionAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (first second : Index4) :
    localScalarChristoffelCorrectionForm period hPeriod metric field firstPatch
        firstCoordinate (Pi.single first 1) (Pi.single second 1) =
      localScalarChristoffelCorrectionForm period hPeriod metric field
          secondPatch secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate agreement.samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate agreement.samePoint
            (Pi.single second 1)) +
        localScalarDifferentialAt period hPeriod field secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
            firstPatch secondPatch firstCoordinate secondCoordinate
            agreement.samePoint (Pi.single first 1) (Pi.single second 1)) := by
  rw [localScalarChristoffelCorrectionForm_apply,
    localScalarDifferentialAt_transition period hPeriod field firstPatch
      secondPatch firstCoordinate secondCoordinate _ agreement.samePoint,
    agreement.christoffel_transform first second, map_add,
    ← localScalarChristoffelCorrectionForm_apply]

/-- The second-order scalar chain rule in bilinear-form notation. -/
theorem localScalarSecondDifferentialFormAt_transition
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    localScalarSecondDifferentialFormAt period hPeriod field firstPatch
        firstCoordinate (Pi.single first 1) (Pi.single second 1) =
      localScalarSecondDifferentialFormAt period hPeriod field secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1))
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single second 1)) +
        localScalarDifferentialAt period hPeriod field secondPatch
          secondCoordinate
          (holonomicCoordinateTransitionSecondDerivativeAt period hPeriod
            firstPatch secondPatch firstCoordinate secondCoordinate samePoint
            (Pi.single first 1) (Pi.single second 1)) := by
  rw [localScalarSecondDifferentialFormAt_basis]
  simpa [localScalarSecondDifferentialFormAt, localScalarDifferentialAt,
    holonomicCoordinateTransitionSecondDerivativeAt] using
    (localScalarPartialGradient_transition period hPeriod field firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint first second)

/-- Once the Levi--Civita connection has its genuine coordinate law, the
covariant scalar Hessian is tensorial. -/
theorem localCovariantScalarHessianForm_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : HolonomicLeviCivitaTransitionAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (first second : Index4) :
    localCovariantScalarHessianForm period hPeriod metric field firstPatch
        firstCoordinate (Pi.single first 1) (Pi.single second 1) =
      localCovariantScalarHessianForm period hPeriod metric field secondPatch
        secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate agreement.samePoint
          (Pi.single first 1))
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate agreement.samePoint
          (Pi.single second 1)) := by
  rw [localCovariantScalarHessianForm_eq,
    localCovariantScalarHessianForm_eq]
  simp only [LinearMap.sub_apply]
  rw [localScalarSecondDifferentialFormAt_transition period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.samePoint first second,
    localScalarChristoffelCorrectionForm_transition period hPeriod metric field
      firstPatch secondPatch firstCoordinate secondCoordinate agreement
      first second]
  ring

/-- The field-independent Levi--Civita transition law supplies the exact
matrix congruence for every scalar covariant Hessian. -/
theorem localCovariantScalarHessian_transition_congruence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : HolonomicLeviCivitaTransitionAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    (localCovariantScalarJet period hPeriod metric firstPatch field
        firstCoordinate).hessian =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate
          agreement.samePoint).transpose *
        (localCovariantScalarJet period hPeriod metric secondPatch field
          secondCoordinate).hessian *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate agreement.samePoint := by
  let transitionLinear : Vector4 →ₗ[Real] Vector4 :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate
      agreement.samePoint).toLinearEquiv.toLinearMap
  ext first second
  have hTensorial :=
    localCovariantScalarHessianForm_transition period hPeriod metric field
      firstPatch secondPatch firstCoordinate secondCoordinate agreement
      first second
  have hCongruence :=
    matrix_toBilin_transition_eq_congruence_entry
      (localCovariantScalarJet period hPeriod metric secondPatch field
        secondCoordinate).hessian transitionLinear first second
  simpa [localCovariantScalarHessianForm, transitionLinear,
    holonomicCoordinateTransitionMatrixAt] using hTensorial.trans hCongruence

/-- Correct tensorial overlap datum for the scalar wave.  Unlike raw component
equality, both covariant matrices are pulled back by the actual transition
Jacobian. -/
structure HolonomicCovariantWaveTransitionAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4) : Prop where
  samePoint : firstPatch.coordinateMap firstCoordinate =
    secondPatch.coordinateMap secondCoordinate
  metric_congruence :
    localMetricMatrix period hPeriod metric firstPatch firstCoordinate =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint).transpose *
        localMetricMatrix period hPeriod metric secondPatch secondCoordinate *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
  hessian_congruence :
    (localCovariantScalarJet period hPeriod metric firstPatch field
        firstCoordinate).hessian =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint).transpose *
        (localCovariantScalarJet period hPeriod metric secondPatch field
          secondCoordinate).hessian *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint

namespace HolonomicCovariantWaveTransitionAgreement

/-- Only the covariant-Hessian law remains to be supplied: metric congruence
follows from the intrinsic tensor and the genuine chart transition. -/
def ofHessianCongruence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hessian_congruence :
      (localCovariantScalarJet period hPeriod metric firstPatch field
          firstCoordinate).hessian =
        (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint).transpose *
          (localCovariantScalarJet period hPeriod metric secondPatch field
            secondCoordinate).hessian *
          holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint) :
    HolonomicCovariantWaveTransitionAgreement period hPeriod metric field
      firstPatch secondPatch firstCoordinate secondCoordinate where
  samePoint := samePoint
  metric_congruence :=
    localMetricMatrix_transition_congruence period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  hessian_congruence := hessian_congruence

end HolonomicCovariantWaveTransitionAgreement

/-- The genuine Jacobian congruence laws imply equality of the local scalar
wave contractions. -/
theorem localCovariantScalarWave_eq_of_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : HolonomicCovariantWaveTransitionAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric firstPatch firstCoordinate)
        (localCovariantScalarJet period hPeriod metric firstPatch field
          firstCoordinate) =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric secondPatch secondCoordinate)
        (localCovariantScalarJet period hPeriod metric secondPatch field
          secondCoordinate) := by
  apply covariantScalarJetWave_eq_of_congruence
    (localFixedSignMetric period hPeriod metric firstPatch firstCoordinate)
    (localFixedSignMetric period hPeriod metric secondPatch secondCoordinate)
    (localCovariantScalarJet period hPeriod metric firstPatch field
      firstCoordinate)
    (localCovariantScalarJet period hPeriod metric secondPatch field
      secondCoordinate)
    (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate agreement.samePoint)
    (holonomicCoordinateTransitionMatrixAt_isUnit period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate agreement.samePoint)
  · exact agreement.metric_congruence
  · exact agreement.hessian_congruence

/-- With intrinsic metric congruence proved above, covariant-Hessian
congruence alone implies scalar-wave naturality. -/
theorem localCovariantScalarWave_eq_of_hessian_congruence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (hessian_congruence :
      (localCovariantScalarJet period hPeriod metric firstPatch field
          firstCoordinate).hessian =
        (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint).transpose *
          (localCovariantScalarJet period hPeriod metric secondPatch field
            secondCoordinate).hessian *
          holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate samePoint) :
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric firstPatch firstCoordinate)
        (localCovariantScalarJet period hPeriod metric firstPatch field
          firstCoordinate) =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric secondPatch secondCoordinate)
        (localCovariantScalarJet period hPeriod metric secondPatch field
          secondCoordinate) :=
  localCovariantScalarWave_eq_of_transition period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate
      (HolonomicCovariantWaveTransitionAgreement.ofHessianCongruence
        period hPeriod metric field firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint hessian_congruence)

/-- Reflexive first-jet agreement in one already selected frame. -/
theorem localMetricFirstJetAgreement_refl
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LocalMetricFirstJetAgreement period hPeriod metric
      patch patch coordinate coordinate where
  metricMatrix_eq := rfl
  metricDerivative_eq := rfl

/-- Symmetry of rebased metric first-jet agreement. -/
theorem localMetricFirstJetAgreement_symm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    LocalMetricFirstJetAgreement period hPeriod metric
      secondPatch firstPatch secondCoordinate firstCoordinate where
  metricMatrix_eq := agreement.metricMatrix_eq.symm
  metricDerivative_eq := agreement.metricDerivative_eq.symm

/-- Transitivity of rebased metric first-jet agreement. -/
theorem localMetricFirstJetAgreement_trans
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch thirdPatch :
      SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate thirdCoordinate : Vector4)
    (firstAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (secondAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      secondPatch thirdPatch secondCoordinate thirdCoordinate) :
    LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch thirdPatch firstCoordinate thirdCoordinate where
  metricMatrix_eq :=
    firstAgreement.metricMatrix_eq.trans secondAgreement.metricMatrix_eq
  metricDerivative_eq :=
    firstAgreement.metricDerivative_eq.trans
      secondAgreement.metricDerivative_eq

/-- Reflexive scalar second-jet agreement in one selected frame. -/
theorem localScalarSecondJetAgreement_refl
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LocalScalarSecondJetAgreement period hPeriod field
      patch patch coordinate coordinate where
  field_eq := rfl
  gradient_eq := rfl
  partialGradient_eq := rfl

/-- Symmetry of rebased scalar second-jet agreement. -/
theorem localScalarSecondJetAgreement_symm
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    LocalScalarSecondJetAgreement period hPeriod field
      secondPatch firstPatch secondCoordinate firstCoordinate where
  field_eq := agreement.field_eq.symm
  gradient_eq := agreement.gradient_eq.symm
  partialGradient_eq := agreement.partialGradient_eq.symm

/-- Transitivity of rebased scalar second-jet agreement. -/
theorem localScalarSecondJetAgreement_trans
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch thirdPatch :
      SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate thirdCoordinate : Vector4)
    (firstAgreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (secondAgreement : LocalScalarSecondJetAgreement period hPeriod field
      secondPatch thirdPatch secondCoordinate thirdCoordinate) :
    LocalScalarSecondJetAgreement period hPeriod field
      firstPatch thirdPatch firstCoordinate thirdCoordinate where
  field_eq := firstAgreement.field_eq.trans secondAgreement.field_eq
  gradient_eq :=
    firstAgreement.gradient_eq.trans secondAgreement.gradient_eq
  partialGradient_eq :=
    firstAgreement.partialGradient_eq.trans
      secondAgreement.partialGradient_eq

/-- Combined overlap datum after both coordinate jets have been rebased into
one common finite frame. -/
structure RebasedHolonomicTransitionJetAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4) : Prop where
  samePoint : firstPatch.coordinateMap firstCoordinate =
    secondPatch.coordinateMap secondCoordinate
  metricFirstJet : LocalMetricFirstJetAgreement period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate
  scalarSecondJet : LocalScalarSecondJetAgreement period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate

/-- Reflexivity of the combined rebased transition datum. -/
theorem rebasedHolonomicTransitionJetAgreement_refl
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    RebasedHolonomicTransitionJetAgreement period hPeriod metric field
      patch patch coordinate coordinate where
  samePoint := rfl
  metricFirstJet :=
    localMetricFirstJetAgreement_refl period hPeriod metric patch coordinate
  scalarSecondJet :=
    localScalarSecondJetAgreement_refl period hPeriod field patch coordinate

/-- The combined rebased transition datum is symmetric. -/
theorem RebasedHolonomicTransitionJetAgreement.symm
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field : SmoothScalarField period hPeriod}
    {firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod}
    {firstCoordinate secondCoordinate : Vector4}
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    RebasedHolonomicTransitionJetAgreement period hPeriod metric field
      secondPatch firstPatch secondCoordinate firstCoordinate where
  samePoint := agreement.samePoint.symm
  metricFirstJet := localMetricFirstJetAgreement_symm period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet
  scalarSecondJet := localScalarSecondJetAgreement_symm period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.scalarSecondJet

/-- The combined rebased transition datum is transitive. -/
theorem RebasedHolonomicTransitionJetAgreement.trans
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field : SmoothScalarField period hPeriod}
    {firstPatch secondPatch thirdPatch :
      SmoothHolonomicFrameChart4 period hPeriod}
    {firstCoordinate secondCoordinate thirdCoordinate : Vector4}
    (firstAgreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate)
    (secondAgreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field secondPatch thirdPatch secondCoordinate thirdCoordinate) :
    RebasedHolonomicTransitionJetAgreement period hPeriod metric field
      firstPatch thirdPatch firstCoordinate thirdCoordinate where
  samePoint := firstAgreement.samePoint.trans secondAgreement.samePoint
  metricFirstJet := localMetricFirstJetAgreement_trans period hPeriod metric
    firstPatch secondPatch thirdPatch firstCoordinate secondCoordinate
      thirdCoordinate firstAgreement.metricFirstJet
      secondAgreement.metricFirstJet
  scalarSecondJet := localScalarSecondJetAgreement_trans period hPeriod field
    firstPatch secondPatch thirdPatch firstCoordinate secondCoordinate
      thirdCoordinate firstAgreement.scalarSecondJet
      secondAgreement.scalarSecondJet

/-- Rebased metric first jets give identical local Levi--Civita coefficients
in the selected common frame. -/
theorem localLeviCivitaChristoffel_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localLeviCivitaChristoffel period hPeriod metric firstPatch
        firstCoordinate =
      localLeviCivitaChristoffel period hPeriod metric secondPatch
        secondCoordinate :=
  localLeviCivitaChristoffel_eq_of_firstJetAgreement period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet

/-- Rebased scalar second jets give the same coordinate jet record. -/
theorem localCoordinateScalarJet_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localCoordinateScalarJet period hPeriod field firstPatch firstCoordinate =
      localCoordinateScalarJet period hPeriod field secondPatch
        secondCoordinate :=
  localCoordinateScalarJet_eq_of_secondJetAgreement period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.scalarSecondJet

/-- Metric and scalar rebased jets give the same covariant scalar jet. -/
theorem localCovariantScalarJet_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localCovariantScalarJet period hPeriod metric firstPatch field
        firstCoordinate =
      localCovariantScalarJet period hPeriod metric secondPatch field
        secondCoordinate :=
  localCovariantScalarJet_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet agreement.scalarSecondJet

/-- The scalar Euler residual glues across a rebased transition. -/
theorem localSmoothScalarEulerResidual_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (massSquared source : Real)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarEulerResidual period hPeriod metric firstPatch field
        massSquared source firstCoordinate =
      localSmoothScalarEulerResidual period hPeriod metric secondPatch field
        massSquared source secondCoordinate :=
  localSmoothScalarEulerResidual_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate massSquared source
      agreement.metricFirstJet agreement.scalarSecondJet

/-- The raised scalar gradient glues across a rebased transition. -/
theorem localSmoothScalarRaisedGradient_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarRaisedGradient period hPeriod metric firstPatch field
        firstCoordinate =
      localSmoothScalarRaisedGradient period hPeriod metric secondPatch field
        secondCoordinate :=
  localSmoothScalarRaisedGradient_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet agreement.scalarSecondJet

/-- Rebased quotient-atlas jets give identical realized stress divergence. -/
theorem localSmoothScalarStressDivergence_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (massSquared source : Real)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarStressDivergence period hPeriod metric firstPatch field
        massSquared source firstCoordinate =
      localSmoothScalarStressDivergence period hPeriod metric secondPatch field
        massSquared source secondCoordinate :=
  localSmoothScalarStressDivergence_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate massSquared source
      agreement.metricFirstJet agreement.scalarSecondJet

/-- Exact residual contract: selected holonomic patches must realize the
analytic quotient transition jets in a common rebased frame. -/
structure CanonicalRebasedHolonomicAtlasTransitionJetContract
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)) : Prop where
  agreement : ∀
      (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod),
    firstPatch ∈ atlasPatches → secondPatch ∈ atlasPatches →
    ∀ (firstCoordinate secondCoordinate : Vector4),
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        RebasedHolonomicTransitionJetAgreement period hPeriod metric field
          firstPatch secondPatch firstCoordinate secondCoordinate

/-- Patchwise compatibility required by a future global stress-conservation
gluing theorem. -/
def CanonicalAtlasStressDivergenceCompatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod))
    (massSquared source : Real) : Prop :=
  ∀ (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod),
    firstPatch ∈ atlasPatches → secondPatch ∈ atlasPatches →
    ∀ (firstCoordinate secondCoordinate : Vector4),
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        localSmoothScalarStressDivergence period hPeriod metric firstPatch field
            massSquared source firstCoordinate =
          localSmoothScalarStressDivergence period hPeriod metric secondPatch
            field massSquared source secondCoordinate

/-- The rebased transition-jet contract supplies the exact overlap condition
needed by global stress-divergence gluing. -/
theorem CanonicalRebasedHolonomicAtlasTransitionJetContract.toStressCompatibility
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod))
    (contract : CanonicalRebasedHolonomicAtlasTransitionJetContract
      period hPeriod metric field atlasPatches)
    (massSquared source : Real) :
    CanonicalAtlasStressDivergenceCompatible period hPeriod metric field
      atlasPatches massSquared source := by
  intro firstPatch secondPatch hFirst hSecond
    firstCoordinate secondCoordinate hSamePoint
  exact localSmoothScalarStressDivergence_eq_of_rebasedTransition
    period hPeriod metric field firstPatch secondPatch
      firstCoordinate secondCoordinate massSquared source
      (contract.agreement firstPatch secondPatch hFirst hSecond
        firstCoordinate secondCoordinate hSamePoint)

/-- Minimal downstream bridge for `GlobalScalarStressConservation`: a covering
family of selected holonomic patches together with coherent rebased jets. -/
structure CanonicalHolonomicAtlasStressConservationBridge
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod) where
  atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)
  covers : ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ atlasPatches, ∃ coordinate : Vector4,
      patch.coordinateMap coordinate = point
  transitionJets : CanonicalRebasedHolonomicAtlasTransitionJetContract
    period hPeriod metric field atlasPatches

/-- The downstream bridge immediately provides overlap compatibility of every
realized local stress divergence. -/
theorem CanonicalHolonomicAtlasStressConservationBridge.stressCompatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real) :
    CanonicalAtlasStressDivergenceCompatible period hPeriod metric field
      bridge.atlasPatches massSquared source :=
  CanonicalRebasedHolonomicAtlasTransitionJetContract.toStressCompatibility
    period hPeriod metric field bridge.atlasPatches bridge.transitionJets
      massSquared source

end

end P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
end JanusFormal
