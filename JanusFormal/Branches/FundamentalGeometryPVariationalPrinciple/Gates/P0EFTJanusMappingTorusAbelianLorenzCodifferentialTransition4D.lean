import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D

/-!
# Transition naturality of the abelian Lorenz codifferential

The matrix-raised local gauge potential is the coordinate representative of
the intrinsic inverse musical.  Its Levi--Civita derivative therefore changes
by conjugation on overlaps, so its trace is chart-independent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Topology
open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem localMetricCoordinateForm_raised_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Index4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (Pi.single index 1)
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate) =
      localGaugeCoefficient period hPeriod potential component patch index
        coordinate := by
  rw [localMetricCoordinateForm_apply_basis_left]
  change
    ((localMetricMatrix period hPeriod metric patch coordinate) *ᵥ
      ((localMetricMatrix period hPeriod metric patch coordinate)⁻¹ *ᵥ
        fun lower =>
          localGaugeCoefficient period hPeriod potential component patch lower
            coordinate)) index = _
  rw [Matrix.mulVec_mulVec]
  have hDet :
      IsUnit
        (localMetricMatrix period hPeriod metric patch coordinate).det :=
    isUnit_iff_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate)
  rw [Matrix.mul_nonsing_inv _ hDet, Matrix.one_mulVec]

/-- The locally raised coefficients lift to the genuine intrinsic inverse
musical of the gauge one-form. -/
theorem coordinateMap_mfderiv_localRaisedAbelianGaugePotential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate) =
      inverseMetricSharp period hPeriod metric
        (patch.coordinateMap coordinate)
        (potential.toFun component (patch.coordinateMap coordinate)) := by
  apply (metric.musical (patch.coordinateMap coordinate)).injective
  rw [metric_flat_inverseMetricSharp]
  apply ContinuousLinearMap.ext
  intro tangent
  let frameEquiv :=
    (Pi.basisFun Real Index4).equiv (patch.frame coordinate)
      (Equiv.refl Index4)
  obtain ⟨vector, rfl⟩ := frameEquiv.surjective tangent
  have hMusical := metric.musical_eq_tensor
    (patch.coordinateMap coordinate)
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod]
  have hFlat :
      metric.musical (patch.coordinateMap coordinate)
          (frameEquiv
            (localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate)) =
        metric.tensor.tensor (patch.coordinateMap coordinate)
          (frameEquiv
            (localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate)) :=
    DFunLike.congr_fun hMusical _
  rw [hFlat]
  rw [metric.tensor.symmetric]
  have hForm :=
    localMetricCoordinateForm_apply period hPeriod metric patch coordinate
      vector
      (localRaisedAbelianGaugePotential period hPeriod metric potential
        component patch coordinate)
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod] at hForm
  rw [← hForm]
  have hExpansion :
      vector = ∑ index : Index4, vector index • Pi.single index 1 := by
    ext index
    simp [Pi.single_apply]
  rw [hExpansion, map_sum, map_sum, map_sum]
  simp_rw [map_smul]
  rw [LinearMap.sum_apply Finset.univ
    (fun index : Index4 =>
      vector index •
        localMetricCoordinateForm period hPeriod metric patch coordinate
          (Pi.single index 1))
    (localRaisedAbelianGaugePotential period hPeriod metric potential
      component patch coordinate)]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  rw [localMetricCoordinateForm_raised_basis period hPeriod metric potential
    component patch coordinate index]
  unfold localGaugeCoefficient
  have hBasis :
      frameEquiv (Pi.single index 1) = patch.frame coordinate index := by
    have hBasis' :
        ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)) ((Pi.basisFun Real Index4) index) =
            patch.frame coordinate index := by
      exact Module.Basis.equiv_apply _ _ _ _
    simpa only [frameEquiv, Pi.basisFun_apply] using hBasis'
  rw [hBasis]

/-- On a genuine chart overlap, the raised local potential obeys the vector
transition law as a germ. -/
theorem localRaisedAbelianGaugePotential_transition_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    (fun current =>
      fderiv Real transition current
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component firstPatch current)) =ᶠ[𝓝 firstCoordinate]
      fun current =>
        localRaisedAbelianGaugePotential period hPeriod metric potential
          component secondPatch (transition current) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  filter_upwards [
    (holonomicCoordinateTransitionDomainAt_isOpen period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).mem_nhds
      (firstCoordinate_mem_holonomicCoordinateTransitionDomainAt period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)]
      with current hCurrent
  have hPoint :=
    holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current samePoint
      hCurrent
  let secondFrameEquiv :=
    (Pi.basisFun Real Index4).equiv
      (secondPatch.frame (transition current)) (Equiv.refl Index4)
  apply secondFrameEquiv.injective
  let firstFrameEquiv :=
    (Pi.basisFun Real Index4).equiv (firstPatch.frame current)
      (Equiv.refl Index4)
  have hChain :=
    holonomicCoordinateMap_mfderiv_transition_heq_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current
      (localRaisedAbelianGaugePotential period hPeriod metric potential
        component firstPatch current) samePoint hCurrent
  change
    HEq
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        firstPatch.coordinateMap current
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component firstPatch current))
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        secondPatch.coordinateMap (transition current)
          (fderiv Real transition current
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component firstPatch current))) at hChain
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod] at hChain
  change
    HEq
      (firstFrameEquiv
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component firstPatch current))
      (secondFrameEquiv
        (fderiv Real transition current
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component firstPatch current))) at hChain
  rw [hPoint] at hChain
  have hFirstLift :
      firstFrameEquiv
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component firstPatch current) =
        inverseMetricSharp period hPeriod metric
          (firstPatch.coordinateMap current)
          (potential.toFun component (firstPatch.coordinateMap current)) := by
    rw [show firstFrameEquiv
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component firstPatch current) =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        firstPatch.coordinateMap current
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component firstPatch current) by
      exact
        (coordinateMap_mfderiv_eq_frameEquiv period hPeriod firstPatch current
          _).symm]
    exact coordinateMap_mfderiv_localRaisedAbelianGaugePotential
      period hPeriod metric potential component firstPatch current
  have hSecondLift :
      secondFrameEquiv
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component secondPatch (transition current)) =
        inverseMetricSharp period hPeriod metric
          (secondPatch.coordinateMap (transition current))
          (potential.toFun component
            (secondPatch.coordinateMap (transition current))) := by
    rw [show secondFrameEquiv
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component secondPatch (transition current)) =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        secondPatch.coordinateMap (transition current)
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component secondPatch (transition current)) by
      exact
        (coordinateMap_mfderiv_eq_frameEquiv period hPeriod secondPatch
          (transition current) _).symm]
    exact coordinateMap_mfderiv_localRaisedAbelianGaugePotential
      period hPeriod metric potential component secondPatch
        (transition current)
  rw [hPoint] at hSecondLift
  calc
    secondFrameEquiv
        (fderiv Real transition current
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component firstPatch current)) =
        firstFrameEquiv
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component firstPatch current) :=
      (eq_of_heq hChain).symm
    _ = _ := hFirstLift
    _ = _ := hSecondLift.symm

/-- Coordinate covariant derivative of the raised gauge potential, bundled as
an endomorphism so its divergence is its invariant trace. -/
def localAbelianLorenzCovariantDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 →ₗ[Real] Vector4 where
  toFun := fun direction =>
    fderiv Real
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch)
        coordinate direction +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
        coordinate direction
        (localRaisedAbelianGaugePotential period hPeriod metric potential
          component patch coordinate)
  map_add' := by
    intro first second
    simp only [map_add, LinearMap.add_apply]
    abel
  map_smul' := by
    intro scalar direction
    simp only [map_smul, RingHom.id_apply, smul_add,
      LinearMap.smul_apply]

/-- The explicit diagonal coordinate sum is the algebraic trace of the
coordinate covariant derivative. -/
theorem localAbelianLorenzDivergence_eq_trace
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localAbelianLorenzDivergence period hPeriod metric potential component
        patch coordinate =
      LinearMap.trace Real Vector4
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component patch coordinate) := by
  rw [LinearMap.trace_eq_matrix_trace Real (Pi.basisFun Real Index4)]
  unfold localAbelianLorenzDivergence Matrix.trace
  apply Finset.sum_congr rfl
  intro derivative _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply]
  change
    fderiv Real
          (fun current =>
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch current derivative)
          coordinate (Pi.single derivative 1) +
        ∑ lower : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              derivative derivative lower *
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate lower =
      (localAbelianLorenzCovariantDerivative period hPeriod metric potential
        component patch coordinate (Pi.single derivative 1)) derivative
  unfold localAbelianLorenzCovariantDerivative
  change
    fderiv Real
          (fun current =>
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch current derivative)
          coordinate (Pi.single derivative 1) +
        ∑ lower : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              derivative derivative lower *
            localRaisedAbelianGaugePotential period hPeriod metric potential
              component patch coordinate lower =
      (fderiv Real
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch)
          coordinate (Pi.single derivative 1)) derivative +
        localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate (Pi.single derivative 1)
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch coordinate) derivative
  congr 1
  · have hDifferentiable :
        DifferentiableAt Real
          (localRaisedAbelianGaugePotential period hPeriod metric potential
            component patch) coordinate :=
      (localRaisedAbelianGaugePotential_contDiff period hPeriod metric
        potential component patch).differentiable (by simp) coordinate
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

/-- The coordinate covariant derivatives are conjugate by the genuine
transition Jacobian. -/
theorem localAbelianLorenzCovariantDerivative_transition_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate direction : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    let transitionLinear :=
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    transitionLinear
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component firstPatch firstCoordinate direction) =
      localAbelianLorenzCovariantDerivative period hPeriod metric potential
        component secondPatch secondCoordinate (transitionLinear direction) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let firstVector :=
    localRaisedAbelianGaugePotential period hPeriod metric potential component
      firstPatch
  let secondVector :=
    localRaisedAbelianGaugePotential period hPeriod metric potential component
      secondPatch
  have hTransitionC2 : ContDiffAt Real 2 transition firstCoordinate := by
    exact
      ((holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
        |>.contMDiffAt.contDiffAt).of_le (by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hTransition : DifferentiableAt Real transition firstCoordinate :=
    hTransitionC2.differentiableAt (by norm_num)
  have hTransitionDerivative :
      DifferentiableAt Real (fderiv Real transition) firstCoordinate :=
    (hTransitionC2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hFirstVector : DifferentiableAt Real firstVector firstCoordinate :=
    (localRaisedAbelianGaugePotential_contDiff period hPeriod metric potential
      component firstPatch).differentiable (by simp) firstCoordinate
  have hSecondVector : DifferentiableAt Real secondVector secondCoordinate :=
    (localRaisedAbelianGaugePotential_contDiff period hPeriod metric potential
      component secondPatch).differentiable (by simp) secondCoordinate
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition] using
      holonomicCoordinateTransitionAt_apply period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hSecondVectorAtTransition :
      DifferentiableAt Real secondVector (transition firstCoordinate) := by
    simpa only [hTransitionAt] using hSecondVector
  have hVectorGerm :
      (fun current =>
        fderiv Real transition current (firstVector current)) =ᶠ[
          𝓝 firstCoordinate]
        fun current => secondVector (transition current) := by
    simpa only [transition, firstVector, secondVector] using
      localRaisedAbelianGaugePotential_transition_eventuallyEq period hPeriod
        metric potential component firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint
  have hVectorAt :
      fderiv Real transition firstCoordinate (firstVector firstCoordinate) =
        secondVector secondCoordinate := by
    have hAt := hVectorGerm.eq_of_nhds
    rw [hTransitionAt] at hAt
    exact hAt
  have hLeftDerivative :
      fderiv Real
          (fun current =>
            fderiv Real transition current (firstVector current))
          firstCoordinate direction =
        fderiv Real (fderiv Real transition) firstCoordinate direction
            (firstVector firstCoordinate) +
          fderiv Real transition firstCoordinate
            (fderiv Real firstVector firstCoordinate direction) := by
    have hProduct := fderiv_clm_apply hTransitionDerivative hFirstVector
    have hApplied := congrArg
      (fun derivativeMap : Vector4 →L[Real] Vector4 =>
        derivativeMap direction) hProduct
    simpa only [add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply, add_comm] using hApplied
  have hRightDerivative :
      fderiv Real (fun current => secondVector (transition current))
          firstCoordinate direction =
        fderiv Real secondVector secondCoordinate
          (fderiv Real transition firstCoordinate direction) := by
    change
      fderiv Real (secondVector ∘ transition) firstCoordinate direction =
        fderiv Real secondVector secondCoordinate
          (fderiv Real transition firstCoordinate direction)
    rw [fderiv_comp firstCoordinate hSecondVectorAtTransition hTransition,
      hTransitionAt]
    rfl
  have hDerivativeEquality :
      fderiv Real
          (fun current =>
            fderiv Real transition current (firstVector current))
          firstCoordinate =
        fderiv Real (fun current => secondVector (transition current))
          firstCoordinate :=
    Filter.EventuallyEq.fderiv_eq hVectorGerm
  have hDerivativeApply := congrArg
    (fun derivativeMap : Vector4 →L[Real] Vector4 =>
      derivativeMap direction) hDerivativeEquality
  rw [hLeftDerivative, hRightDerivative] at hDerivativeApply
  have hConnection :=
    (fixedHolonomicTransition_leviCivita_eventuallyEq_vectors period hPeriod
      metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
      direction (firstVector firstCoordinate)).eq_of_nhds
  change
    fderiv Real transition firstCoordinate
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          firstCoordinate direction (firstVector firstCoordinate)) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          (transition firstCoordinate)
          (fderiv Real transition firstCoordinate direction)
          (fderiv Real transition firstCoordinate
            (firstVector firstCoordinate)) +
        fderiv Real (fderiv Real transition) firstCoordinate direction
          (firstVector firstCoordinate) at hConnection
  rw [hTransitionAt, hVectorAt] at hConnection
  have hLinear :
      (transitionLinear : Vector4 →L[Real] Vector4) =
        fderiv Real transition firstCoordinate := by
    simpa only [transitionLinear, transition] using
      holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hLinearApply (vector : Vector4) :
      transitionLinear vector =
        fderiv Real transition firstCoordinate vector := by
    exact congrArg (fun linearMap : Vector4 →L[Real] Vector4 =>
      linearMap vector) hLinear
  change
    transitionLinear
        (fderiv Real firstVector firstCoordinate direction +
          localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate direction (firstVector firstCoordinate)) =
      fderiv Real secondVector secondCoordinate
          (transitionLinear direction) +
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate (transitionLinear direction)
          (secondVector secondCoordinate)
  simp_rw [hLinearApply]
  rw [map_add]
  rw [hConnection]
  rw [← hDerivativeApply]
  abel

/-- The coordinate covariant-derivative endomorphisms are conjugate on an
overlap. -/
theorem localAbelianLorenzCovariantDerivative_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    let transitionLinear :=
      (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint).toLinearEquiv
    transitionLinear.conj
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component firstPatch firstCoordinate) =
      localAbelianLorenzCovariantDerivative period hPeriod metric potential
        component secondPatch secondCoordinate := by
  let transitionContinuous :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let transitionLinear := transitionContinuous.toLinearEquiv
  apply LinearMap.ext
  intro vector
  simp only [LinearEquiv.conj_apply_apply]
  change
    transitionContinuous
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component firstPatch firstCoordinate
            (transitionContinuous.symm vector)) =
      localAbelianLorenzCovariantDerivative period hPeriod metric potential
        component secondPatch secondCoordinate vector
  have hTransition :=
    localAbelianLorenzCovariantDerivative_transition_apply period hPeriod
      metric potential component firstPatch secondPatch firstCoordinate
        secondCoordinate (transitionContinuous.symm vector) samePoint
  change
    transitionContinuous
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component firstPatch firstCoordinate
            (transitionContinuous.symm vector)) =
      localAbelianLorenzCovariantDerivative period hPeriod metric potential
        component secondPatch secondCoordinate
          (transitionContinuous (transitionContinuous.symm vector))
    at hTransition
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hTransition

/-- The Lorenz divergence is independent of the holonomic chart used to
compute it. -/
theorem localAbelianLorenzDivergence_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localAbelianLorenzDivergence period hPeriod metric potential component
        firstPatch firstCoordinate =
      localAbelianLorenzDivergence period hPeriod metric potential component
        secondPatch secondCoordinate := by
  rw [localAbelianLorenzDivergence_eq_trace,
    localAbelianLorenzDivergence_eq_trace]
  let transitionLinear :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).toLinearEquiv
  have hConjugate :=
    localAbelianLorenzCovariantDerivative_transition period hPeriod metric
      potential component firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint
  change
    transitionLinear.conj
        (localAbelianLorenzCovariantDerivative period hPeriod metric potential
          component firstPatch firstCoordinate) =
      localAbelianLorenzCovariantDerivative period hPeriod metric potential
        component secondPatch secondCoordinate at hConjugate
  rw [← hConjugate]
  exact (LinearMap.trace_conj'
    (localAbelianLorenzCovariantDerivative period hPeriod metric potential
      component firstPatch firstCoordinate) transitionLinear).symm

end
end P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
end JanusFormal
