import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaDerivative4D

/-!
# Local Riemann naturality for the canonical holonomic transition

The fixed transition-germ Levi--Civita law is differentiated and
antisymmetrized.  The symmetric second and third transition jets cancel,
leaving the tensorial transformation law for the local Riemann endomorphism.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaGerm4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionThirdJet4D
open P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaDerivative4D
open P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Vector4
abbrev Index4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Index4
abbrev Endomorphism4 :=
  P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D.Endomorphism4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

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
  have derivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have functionEquality :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [functionEquality] at derivative
  have applied := congrArg
    (fun derivativeMap : E →L[Real] G => derivativeMap direction)
    derivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using applied

theorem localLeviCivitaChristoffelApply_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : E → Vector4) (point : E)
    (hCoordinate : DifferentiableAt Real coordinate point)
    (hFirstVector : DifferentiableAt Real firstVector point)
    (hSecondVector : DifferentiableAt Real secondVector point) :
    DifferentiableAt Real
      (fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric patch
          (coordinate current) (firstVector current) (secondVector current))
      point := by
  apply differentiableAt_pi.mpr
  intro upper
  simp only [localLeviCivitaChristoffelApply, Matrix.toBilin'_apply]
  apply DifferentiableAt.fun_sum
  intro first _
  apply DifferentiableAt.fun_sum
  intro second _
  have hChristoffel :
      DifferentiableAt Real
        (fun current =>
          localLeviCivitaChristoffel period hPeriod metric patch
            (coordinate current) upper first second)
        point :=
    ((localLeviCivitaChristoffel_contDiff period hPeriod metric patch
      upper first second).differentiable (by simp) (coordinate point)).comp
        point hCoordinate
  exact
    (((differentiableAt_pi.mp hFirstVector) first).mul hChristoffel).mul
      ((differentiableAt_pi.mp hSecondVector) second)

theorem fderiv_localLeviCivitaChristoffelApply_dynamic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate firstVector secondVector : E → Vector4)
    (point direction : E)
    (hCoordinate : DifferentiableAt Real coordinate point)
    (hFirstVector : DifferentiableAt Real firstVector point)
    (hSecondVector : DifferentiableAt Real secondVector point) :
    fderiv Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric patch
            (coordinate current) (firstVector current) (secondVector current))
        point direction =
      localLeviCivitaChristoffelApply period hPeriod metric patch
          (coordinate point) (fderiv Real firstVector point direction)
          (secondVector point) +
        fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric patch
                current (firstVector point) (secondVector point))
            (coordinate point) (fderiv Real coordinate point direction) +
        localLeviCivitaChristoffelApply period hPeriod metric patch
          (coordinate point) (firstVector point)
          (fderiv Real secondVector point direction) := by
  have hWhole :=
    localLeviCivitaChristoffelApply_differentiableAt period hPeriod metric
      patch coordinate firstVector secondVector point hCoordinate hFirstVector
      hSecondVector
  have hCoordinateOnly :
      DifferentiableAt Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric patch current
            (firstVector point) (secondVector point))
        (coordinate point) :=
    localLeviCivitaChristoffelApply_differentiableAt period hPeriod metric
      patch id (fun _ => firstVector point) (fun _ => secondVector point)
      (coordinate point) differentiableAt_id (differentiableAt_const _)
      (differentiableAt_const _)
  ext upper
  have hWholeComponent :
      fderiv Real
          (fun current =>
            localLeviCivitaChristoffelApply period hPeriod metric patch
              (coordinate current) (firstVector current)
              (secondVector current) upper)
          point direction =
        fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric patch
                (coordinate current) (firstVector current)
                (secondVector current))
            point direction upper := by
    have applied := congrArg
      (fun derivative : E →L[Real] Real => derivative direction)
      (fderiv_apply hWhole upper)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using applied
  have hCoordinateComponent :
      fderiv Real
          (fun current =>
            localLeviCivitaChristoffelApply period hPeriod metric patch current
              (firstVector point) (secondVector point) upper)
          (coordinate point) (fderiv Real coordinate point direction) =
        fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric patch
                current (firstVector point) (secondVector point))
            (coordinate point) (fderiv Real coordinate point direction)
              upper := by
    have applied := congrArg
      (fun derivative : Vector4 →L[Real] Real =>
        derivative (fderiv Real coordinate point direction))
      (fderiv_apply hCoordinateOnly upper)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using applied
  simp only [Pi.add_apply]
  rw [← hWholeComponent, ← hCoordinateComponent]
  let baseMatrix : Vector4 →
      P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Matrix4 :=
    fun current =>
    localLeviCivitaChristoffelMatrix period hPeriod metric patch current upper
  let matrix : E →
      P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Matrix4 :=
    baseMatrix ∘ coordinate
  have hBaseMatrix : DifferentiableAt Real baseMatrix (coordinate point) := by
    apply differentiableAt_pi.mpr
    intro first
    apply differentiableAt_pi.mpr
    intro second
    exact
      (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
        upper first second).differentiable (by simp) (coordinate point)
  have hMatrix : DifferentiableAt Real matrix point :=
    hBaseMatrix.comp point hCoordinate
  have hMatrixChain :
      fderiv Real matrix point direction =
        fderiv Real baseMatrix (coordinate point)
          (fderiv Real coordinate point direction) := by
    have applied := congrArg
      (fun derivative : E →L[Real]
          P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Matrix4 =>
        derivative direction)
      (fderiv_comp point hBaseMatrix hCoordinate)
    change
      fderiv Real (baseMatrix ∘ coordinate) point direction =
        fderiv Real baseMatrix (coordinate point)
          (fderiv Real coordinate point direction)
      at applied
    exact applied
  have hDynamic :=
    fderiv_matrix_toBilin_dynamic_apply matrix firstVector secondVector
      point direction hMatrix hFirstVector hSecondVector
  have hCoordinateDerivative :=
    fderiv_matrix_toBilin_dynamic_apply baseMatrix
      (fun _ : Vector4 => firstVector point)
      (fun _ : Vector4 => secondVector point)
      (coordinate point) (fderiv Real coordinate point direction)
      hBaseMatrix (differentiableAt_const _) (differentiableAt_const _)
  change
    fderiv Real
        (fun current =>
          Matrix.toBilin' (matrix current) (firstVector current)
            (secondVector current))
        point direction =
      Matrix.toBilin' (matrix point)
          (fderiv Real firstVector point direction) (secondVector point) +
        fderiv Real
            (fun current =>
              Matrix.toBilin' (baseMatrix current) (firstVector point)
                (secondVector point))
            (coordinate point) (fderiv Real coordinate point direction) +
        Matrix.toBilin' (matrix point) (firstVector point)
          (fderiv Real secondVector point direction)
  rw [hDynamic]
  rw [hMatrixChain]
  simpa using hCoordinateDerivative.symm

/-- Riemann curvature applied to arbitrary coordinate vectors. -/
def localLeviCivitaRiemannVector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : Vector4) : Vector4 :=
  fderiv Real
      (fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric patch current
          second vector)
      coordinate first -
    fderiv Real
      (fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric patch current
          first vector)
      coordinate second +
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
      first
      (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        second vector) -
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
      second
      (localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        first vector)

private theorem localLeviCivitaConnectionEndomorphism_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) (direction : Index4) :
    localLeviCivitaConnectionEndomorphism period hPeriod metric patch
        coordinate direction vector =
      localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
        (Pi.single direction 1) vector := by
  classical
  ext upper
  unfold localLeviCivitaConnectionEndomorphism
    localLeviCivitaConnectionMatrix
    localLeviCivitaChristoffelApply
    localLeviCivitaChristoffelMatrix
  simp only [Matrix.toBilin'_apply]
  change
    (∑ lower : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper direction lower * vector lower) =
      ∑ first : Index4, ∑ second : Index4,
        (Pi.single direction (1 : Real) : Vector4) first *
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper first second *
          vector second
  have collapse :
      (∑ first : Index4, ∑ second : Index4,
        (Pi.single direction (1 : Real) : Vector4) first *
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper first second *
          vector second) =
        ∑ second : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              upper direction second *
            vector second := by
    rw [Finset.sum_eq_single direction]
    · simp
    · intro other _ hOther
      rw [Pi.single_eq_of_ne hOther]
      simp
    · simp
  rw [collapse]

private theorem localConnectionDirectionalDerivative_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) (derivative direction : Index4) :
    algebraDirectionalDerivative
        (fun current =>
          localLeviCivitaConnectionEndomorphism period hPeriod metric patch
            current direction)
        coordinate derivative vector =
      fderiv Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric patch current
            (Pi.single direction 1) vector)
        coordinate (Pi.single derivative 1) := by
  let connection := fun current =>
    localLeviCivitaConnectionEndomorphism period hPeriod metric patch current
      direction
  have hConnection : DifferentiableAt Real connection coordinate :=
    (localLeviCivitaConnectionEndomorphism_contDiff period hPeriod metric
      patch direction).differentiable (by simp) coordinate
  have derivativeApply :=
    fderiv_continuousLinearMap_apply_const connection coordinate
      (Pi.single derivative 1) vector hConnection
  have functionEquality :
      (fun current => connection current vector) =
        fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric patch current
            (Pi.single direction 1) vector := by
    funext current
    exact localLeviCivitaConnectionEndomorphism_apply period hPeriod metric
      patch current vector direction
  unfold algebraDirectionalDerivative
  change fderiv Real connection coordinate (Pi.single derivative 1) vector = _
  rw [← derivativeApply, functionEquality]

/-- On coordinate-basis curvature directions, the arbitrary-vector
presentation is exactly the existing endomorphism-valued Riemann curvature. -/
theorem localLeviCivitaRiemannVector_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) (first second : Index4) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate
        (Pi.single first 1) (Pi.single second 1) vector =
      localLeviCivitaRiemannEndomorphism period hPeriod metric patch coordinate
        first second vector := by
  unfold localLeviCivitaRiemannVector
  unfold localLeviCivitaRiemannEndomorphism algebraConnectionCurvature
  change
    _ =
      (algebraDirectionalDerivative
          (fun current =>
            localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              current second)
          coordinate first -
        algebraDirectionalDerivative
          (fun current =>
            localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              current first)
          coordinate second +
        localLeviCivitaConnectionEndomorphism period hPeriod metric patch
            coordinate first *
          localLeviCivitaConnectionEndomorphism period hPeriod metric patch
            coordinate second -
        localLeviCivitaConnectionEndomorphism period hPeriod metric patch
            coordinate second *
          localLeviCivitaConnectionEndomorphism period hPeriod metric patch
            coordinate first) vector
  simp only [sub_apply, add_apply, mul_apply_eq_comp]
  rw [localConnectionDirectionalDerivative_apply period hPeriod metric patch
    coordinate vector first second]
  rw [localConnectionDirectionalDerivative_apply period hPeriod metric patch
    coordinate vector second first]
  rw [localLeviCivitaConnectionEndomorphism_apply period hPeriod metric patch
    coordinate
    (localLeviCivitaConnectionEndomorphism period hPeriod metric patch
      coordinate second vector) first]
  rw [localLeviCivitaConnectionEndomorphism_apply period hPeriod metric patch
    coordinate
    (localLeviCivitaConnectionEndomorphism period hPeriod metric patch
      coordinate first vector) second]
  rw [localLeviCivitaConnectionEndomorphism_apply period hPeriod metric patch
    coordinate vector second]
  rw [localLeviCivitaConnectionEndomorphism_apply period hPeriod metric patch
    coordinate vector first]

/-- The fixed transition-germ Christoffel law on arbitrary coordinate
vectors. -/
theorem fixedHolonomicTransition_leviCivita_eventuallyEq_vectors
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (firstVector secondVector : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    (fun current =>
      fderiv Real transition current
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          current firstVector secondVector)) =ᶠ[𝓝 firstCoordinate]
      fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            (transition current)
            (fderiv Real transition current firstVector)
            (fderiv Real transition current secondVector) +
          fderiv Real (fderiv Real transition) current firstVector
            secondVector := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have allBasis :
      ∀ᶠ current in 𝓝 firstCoordinate,
        ∀ first second : Index4,
          fderiv Real transition current
              (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
                current (Pi.single first 1) (Pi.single second 1)) =
            localLeviCivitaChristoffelApply period hPeriod metric secondPatch
                (transition current)
                (fderiv Real transition current (Pi.single first 1))
                (fderiv Real transition current (Pi.single second 1)) +
              fderiv Real (fderiv Real transition) current
                (Pi.single first 1) (Pi.single second 1) := by
    apply Filter.eventually_all.mpr
    intro first
    apply Filter.eventually_all.mpr
    intro second
    filter_upwards [
      fixedHolonomicTransition_leviCivita_eventuallyEq period hPeriod metric
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint
        first second] with current hCurrent
    exact hCurrent
  filter_upwards [allBasis] with current hBasis
  let jacobian : Vector4 →ₗ[Real] Vector4 :=
    (fderiv Real transition current).toLinearMap
  let firstChristoffel :=
    localLeviCivitaChristoffelBilinearMap period hPeriod metric firstPatch
      current
  let secondChristoffel :=
    localLeviCivitaChristoffelBilinearMap period hPeriod metric secondPatch
      (transition current)
  let hessian := fderiv Real (fderiv Real transition) current
  let left : Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 :=
    { toFun := fun first =>
        LinearMap.comp jacobian (firstChristoffel first)
      map_add' := by
        intro first second
        ext vector
        simp [jacobian, firstChristoffel]
      map_smul' := by
        intro scalar first
        ext vector
        simp [jacobian, firstChristoffel] }
  let right : Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 :=
    { toFun := fun first =>
        { toFun := fun second =>
            secondChristoffel (jacobian first) (jacobian second) +
              hessian first second
          map_add' := by
            intro leftVector rightVector
            simp only [map_add]
            abel
          map_smul' := by
            intro scalar vector
            simp only [map_smul, RingHom.id_apply, smul_add] }
      map_add' := by
        intro first second
        apply LinearMap.ext
        intro vector
        change
          secondChristoffel (jacobian (first + second)) (jacobian vector) +
              hessian (first + second) vector =
            (secondChristoffel (jacobian first) (jacobian vector) +
                hessian first vector) +
              (secondChristoffel (jacobian second) (jacobian vector) +
                hessian second vector)
        simp only [map_add, LinearMap.add_apply, add_apply]
        abel
      map_smul' := by
        intro scalar first
        apply LinearMap.ext
        intro vector
        change
          secondChristoffel (jacobian (scalar • first)) (jacobian vector) +
              hessian (scalar • first) vector =
            scalar •
              (secondChristoffel (jacobian first) (jacobian vector) +
                hessian first vector)
        simp only [map_smul, LinearMap.smul_apply, smul_apply, smul_add] }
  have mapsEqual : left = right := by
    apply (Pi.basisFun Real Index4).ext
    intro first
    apply (Pi.basisFun Real Index4).ext
    intro second
    simp only [Pi.basisFun_apply, left, right, jacobian,
      firstChristoffel, secondChristoffel, hessian,
      localLeviCivitaChristoffelBilinearMap_apply]
    change
      fderiv Real transition current
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            current (Pi.single first 1) (Pi.single second 1)) =
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            (transition current)
            (fderiv Real transition current (Pi.single first 1))
            (fderiv Real transition current (Pi.single second 1)) +
          fderiv Real (fderiv Real transition) current
            (Pi.single first 1) (Pi.single second 1)
    exact hBasis first second
  have applied := congrArg
    (fun map : Vector4 →ₗ[Real] Vector4 →ₗ[Real] Vector4 =>
      map firstVector secondVector)
    mapsEqual
  change
    fderiv Real transition current
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          current firstVector secondVector) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          (transition current)
          (fderiv Real transition current firstVector)
          (fderiv Real transition current secondVector) +
        fderiv Real (fderiv Real transition) current firstVector secondVector
  exact applied

/-- Exact derivative of the arbitrary-vector fixed-transition Christoffel
germ, before expanding the product rules. -/
theorem fixedHolonomicTransition_leviCivitaDerivative_vectors
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (firstVector secondVector : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real
        (fun current =>
          fderiv Real transition current
            (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
              current firstVector secondVector))
        firstCoordinate =
      fderiv Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
              (transition current)
              (fderiv Real transition current firstVector)
              (fderiv Real transition current secondVector) +
            fderiv Real (fderiv Real transition) current firstVector
              secondVector)
        firstCoordinate :=
  (fixedHolonomicTransition_leviCivita_eventuallyEq_vectors period hPeriod
    metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
    firstVector secondVector).fderiv_eq

/-- Fully expanded directional derivative of the arbitrary-vector
Christoffel transition law. -/
theorem fixedHolonomicTransition_leviCivitaDerivative_vectors_expanded
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (direction firstVector secondVector : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real (fderiv Real transition) firstCoordinate direction
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate firstVector secondVector) +
        fderiv Real transition firstCoordinate
          (fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric firstPatch
                current firstVector secondVector)
            firstCoordinate direction) =
      fderiv Real
            (fun current =>
              localLeviCivitaChristoffelApply period hPeriod metric secondPatch
                current
                (fderiv Real transition firstCoordinate firstVector)
                (fderiv Real transition firstCoordinate secondVector))
            secondCoordinate
            (fderiv Real transition firstCoordinate direction) +
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate
          (fderiv Real (fderiv Real transition) firstCoordinate direction
            firstVector)
          (fderiv Real transition firstCoordinate secondVector) +
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate
            (fderiv Real transition firstCoordinate firstVector)
            (fderiv Real (fderiv Real transition) firstCoordinate direction
              secondVector) +
        fderiv Real (fderiv Real (fderiv Real transition)) firstCoordinate
          direction firstVector secondVector := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have hTransitionC3 : ContDiffAt Real 3 transition firstCoordinate := by
    simpa only [transition] using
      holonomicCoordinateTransitionAt_contDiffAt_three period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint
  have hTransition : DifferentiableAt Real transition firstCoordinate :=
    hTransitionC3.differentiableAt (by norm_num)
  have hJacobian :
      DifferentiableAt Real (fderiv Real transition) firstCoordinate :=
    (hTransitionC3.fderiv_right (m := 2) (by norm_num)).differentiableAt
      (by norm_num)
  have hHessian :
      DifferentiableAt Real (fderiv Real (fderiv Real transition))
        firstCoordinate :=
    ((hTransitionC3.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition] using
      holonomicCoordinateTransitionAt_apply period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hFirstJacobian :
      DifferentiableAt Real
        (fun current => fderiv Real transition current firstVector)
        firstCoordinate :=
    (ContinuousLinearMap.apply Real Vector4 firstVector).differentiableAt.comp
      firstCoordinate hJacobian
  have hSecondJacobian :
      DifferentiableAt Real
        (fun current => fderiv Real transition current secondVector)
        firstCoordinate :=
    (ContinuousLinearMap.apply Real Vector4 secondVector).differentiableAt.comp
      firstCoordinate hJacobian
  have hFirstJacobianDerivative :
      fderiv Real
          (fun current => fderiv Real transition current firstVector)
          firstCoordinate direction =
        fderiv Real (fderiv Real transition) firstCoordinate direction
          firstVector :=
    fderiv_continuousLinearMap_apply_const
      (fderiv Real transition) firstCoordinate direction firstVector hJacobian
  have hSecondJacobianDerivative :
      fderiv Real
          (fun current => fderiv Real transition current secondVector)
          firstCoordinate direction =
        fderiv Real (fderiv Real transition) firstCoordinate direction
          secondVector :=
    fderiv_continuousLinearMap_apply_const
      (fderiv Real transition) firstCoordinate direction secondVector hJacobian
  have hFirstChristoffel :
      DifferentiableAt Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            current firstVector secondVector)
        firstCoordinate :=
    localLeviCivitaChristoffelApply_differentiableAt period hPeriod metric
      firstPatch id (fun _ => firstVector) (fun _ => secondVector)
      firstCoordinate differentiableAt_id (differentiableAt_const _)
      (differentiableAt_const _)
  have hLeftDerivative :
      fderiv Real
          (fun current =>
            fderiv Real transition current
              (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
                current firstVector secondVector))
          firstCoordinate direction =
        fderiv Real (fderiv Real transition) firstCoordinate direction
            (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
              firstCoordinate firstVector secondVector) +
          fderiv Real transition firstCoordinate
            (fderiv Real
              (fun current =>
                localLeviCivitaChristoffelApply period hPeriod metric
                  firstPatch current firstVector secondVector)
              firstCoordinate direction) := by
    have productRule :=
      fderiv_clm_apply hJacobian hFirstChristoffel
    have applied := congrArg
      (fun derivative : Vector4 →L[Real] Vector4 => derivative direction)
      productRule
    simpa only [add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply, add_comm] using applied
  have hSecondDynamic :
      DifferentiableAt Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            (transition current)
            (fderiv Real transition current firstVector)
            (fderiv Real transition current secondVector))
        firstCoordinate :=
    localLeviCivitaChristoffelApply_differentiableAt period hPeriod metric
      secondPatch transition
      (fun current => fderiv Real transition current firstVector)
      (fun current => fderiv Real transition current secondVector)
      firstCoordinate hTransition hFirstJacobian hSecondJacobian
  have hSecondDynamicDerivative :=
    fderiv_localLeviCivitaChristoffelApply_dynamic period hPeriod metric
      secondPatch transition
      (fun current => fderiv Real transition current firstVector)
      (fun current => fderiv Real transition current secondVector)
      firstCoordinate direction hTransition hFirstJacobian hSecondJacobian
  rw [hTransitionAt, hFirstJacobianDerivative,
    hSecondJacobianDerivative] at hSecondDynamicDerivative
  let hessianFirst : Vector4 → Vector4 →L[Real] Vector4 := fun current =>
    fderiv Real (fderiv Real transition) current firstVector
  have hHessianFirst : DifferentiableAt Real hessianFirst firstCoordinate := by
    have hApplied := hHessian.clm_apply
      (differentiableAt_const (c := firstVector))
    simpa only [hessianFirst] using hApplied
  have hHessianFirstDerivative :
      fderiv Real hessianFirst firstCoordinate direction =
        fderiv Real (fderiv Real (fderiv Real transition)) firstCoordinate
          direction firstVector := by
    exact fderiv_continuousLinearMap_apply_const
      (fderiv Real (fderiv Real transition)) firstCoordinate direction
      firstVector hHessian
  have hHessianTerm :
      DifferentiableAt Real
        (fun current =>
          fderiv Real (fderiv Real transition) current firstVector
            secondVector)
        firstCoordinate :=
    (ContinuousLinearMap.apply Real Vector4 secondVector).differentiableAt.comp
      firstCoordinate hHessianFirst
  have hThirdDerivative :
      fderiv Real
          (fun current =>
            fderiv Real (fderiv Real transition) current firstVector
              secondVector)
          firstCoordinate direction =
        fderiv Real (fderiv Real (fderiv Real transition)) firstCoordinate
          direction firstVector secondVector := by
    calc
      _ = fderiv Real hessianFirst firstCoordinate direction secondVector :=
        fderiv_continuousLinearMap_apply_const hessianFirst firstCoordinate
          direction secondVector hHessianFirst
      _ = _ := by rw [hHessianFirstDerivative]
  have hRightDerivative :
      fderiv Real
          (fun current =>
            localLeviCivitaChristoffelApply period hPeriod metric secondPatch
                (transition current)
                (fderiv Real transition current firstVector)
                (fderiv Real transition current secondVector) +
              fderiv Real (fderiv Real transition) current firstVector
                secondVector)
          firstCoordinate direction =
        fderiv Real
              (fun current =>
                localLeviCivitaChristoffelApply period hPeriod metric
                  secondPatch current
                  (fderiv Real transition firstCoordinate firstVector)
                  (fderiv Real transition firstCoordinate secondVector))
              secondCoordinate
              (fderiv Real transition firstCoordinate direction) +
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate
            (fderiv Real (fderiv Real transition) firstCoordinate direction
              firstVector)
            (fderiv Real transition firstCoordinate secondVector) +
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
              secondCoordinate
              (fderiv Real transition firstCoordinate firstVector)
              (fderiv Real (fderiv Real transition) firstCoordinate direction
                secondVector) +
          fderiv Real (fderiv Real (fderiv Real transition)) firstCoordinate
            direction firstVector secondVector := by
    have sumRule := fderiv_add hSecondDynamic hHessianTerm
    have applied := congrArg
      (fun derivative : Vector4 →L[Real] Vector4 => derivative direction)
      sumRule
    simp only [add_apply] at applied
    rw [hSecondDynamicDerivative, hThirdDerivative] at applied
    change
      fderiv Real
          (fun current =>
            localLeviCivitaChristoffelApply period hPeriod metric secondPatch
                (transition current)
                (fderiv Real transition current firstVector)
                (fderiv Real transition current secondVector) +
              fderiv Real (fderiv Real transition) current firstVector
                secondVector)
          firstCoordinate direction = _
      at applied
    rw [applied]
    abel
  have raw := congrArg
    (fun derivative : Vector4 →L[Real] Vector4 => derivative direction)
    (fixedHolonomicTransition_leviCivitaDerivative_vectors period hPeriod
      metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
      firstVector secondVector)
  exact hLeftDerivative.symm.trans (raw.trans hRightDerivative)

/-- The two Christoffel-product terms in curvature after applying the fixed
transition Jacobian. -/
theorem fixedHolonomicTransition_leviCivitaProduct_vectors
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second vector : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real transition firstCoordinate
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          firstCoordinate first
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate second vector)) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate
          (fderiv Real transition firstCoordinate first)
          (localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate
            (fderiv Real transition firstCoordinate second)
            (fderiv Real transition firstCoordinate vector)) +
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate
          (fderiv Real transition firstCoordinate first)
          (fderiv Real (fderiv Real transition) firstCoordinate second
            vector) +
        fderiv Real (fderiv Real transition) firstCoordinate first
          (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate second vector) := by
  dsimp only
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let inner :=
    localLeviCivitaChristoffelApply period hPeriod metric firstPatch
      firstCoordinate second vector
  have hTarget : transition firstCoordinate = secondCoordinate := by
    simpa only [transition] using
      holonomicCoordinateTransitionAt_apply period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hOuter :=
    (fixedHolonomicTransition_leviCivita_eventuallyEq_vectors period hPeriod
      metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
      first inner).self_of_nhds
  have hInner :=
    (fixedHolonomicTransition_leviCivita_eventuallyEq_vectors period hPeriod
      metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
      second vector).self_of_nhds
  change
    fderiv Real transition firstCoordinate
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          firstCoordinate first inner) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          (transition firstCoordinate)
          (fderiv Real transition firstCoordinate first)
          (fderiv Real transition firstCoordinate inner) +
        fderiv Real (fderiv Real transition) firstCoordinate first inner
    at hOuter
  change
    fderiv Real transition firstCoordinate inner =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          (transition firstCoordinate)
          (fderiv Real transition firstCoordinate second)
          (fderiv Real transition firstCoordinate vector) +
        fderiv Real (fderiv Real transition) firstCoordinate second vector
    at hInner
  rw [hTarget] at hOuter hInner
  rw [hInner] at hOuter
  change
    _ =
      localLeviCivitaChristoffelBilinearMap period hPeriod metric secondPatch
          secondCoordinate
          (fderiv Real transition firstCoordinate first) (_ + _) +
        _ at hOuter
  simp only [map_add,
    localLeviCivitaChristoffelBilinearMap_apply] at hOuter
  simpa only [transition, inner, add_assoc] using hOuter

/-- Unconditional local naturality of Riemann curvature under the fixed
canonical holonomic transition. -/
theorem localLeviCivitaRiemannVector_natural
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second vector : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real transition firstCoordinate
        (localLeviCivitaRiemannVector period hPeriod metric firstPatch
          firstCoordinate first second vector) =
      localLeviCivitaRiemannVector period hPeriod metric secondPatch
        secondCoordinate
        (fderiv Real transition firstCoordinate first)
        (fderiv Real transition firstCoordinate second)
        (fderiv Real transition firstCoordinate vector) := by
  dsimp only
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let J := fderiv Real transition firstCoordinate
  let H := fderiv Real (fderiv Real transition) firstCoordinate
  let K := fderiv Real (fderiv Real (fderiv Real transition)) firstCoordinate
  let G1 := fun coordinate first second =>
    localLeviCivitaChristoffelApply period hPeriod metric firstPatch
      coordinate first second
  let G2 := fun coordinate first second =>
    localLeviCivitaChristoffelApply period hPeriod metric secondPatch
      coordinate first second
  let D1 := fun derivative first second =>
    fderiv Real (fun coordinate => G1 coordinate first second)
      firstCoordinate derivative
  let D2 := fun derivative first second =>
    fderiv Real (fun coordinate => G2 coordinate first second)
      secondCoordinate derivative
  have hDu :
      H first (G1 firstCoordinate second vector) +
          J (D1 first second vector) =
        D2 (J first) (J second) (J vector) +
            G2 secondCoordinate (H first second) (J vector) +
          G2 secondCoordinate (J second) (H first vector) +
        K first second vector := by
    simpa only [transition, J, H, K, G1, G2, D1, D2] using
      fixedHolonomicTransition_leviCivitaDerivative_vectors_expanded
        period hPeriod metric firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint first second vector
  have hDv :
      H second (G1 firstCoordinate first vector) +
          J (D1 second first vector) =
        D2 (J second) (J first) (J vector) +
            G2 secondCoordinate (H second first) (J vector) +
          G2 secondCoordinate (J first) (H second vector) +
        K second first vector := by
    simpa only [transition, J, H, K, G1, G2, D1, D2] using
      fixedHolonomicTransition_leviCivitaDerivative_vectors_expanded
        period hPeriod metric firstPatch secondPatch firstCoordinate
        secondCoordinate samePoint second first vector
  have hPu :
      J (G1 firstCoordinate first (G1 firstCoordinate second vector)) =
        G2 secondCoordinate (J first)
            (G2 secondCoordinate (J second) (J vector)) +
          G2 secondCoordinate (J first) (H second vector) +
        H first (G1 firstCoordinate second vector) := by
    simpa only [transition, J, H, G1, G2] using
      fixedHolonomicTransition_leviCivitaProduct_vectors period hPeriod metric
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint first
        second vector
  have hPv :
      J (G1 firstCoordinate second (G1 firstCoordinate first vector)) =
        G2 secondCoordinate (J second)
            (G2 secondCoordinate (J first) (J vector)) +
          G2 secondCoordinate (J second) (H first vector) +
        H second (G1 firstCoordinate first vector) := by
    simpa only [transition, J, H, G1, G2] using
      fixedHolonomicTransition_leviCivitaProduct_vectors period hPeriod metric
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint second
        first vector
  have hH : H first second = H second first := by
    simpa only [H, transition,
      holonomicCoordinateTransitionSecondDerivativeAt] using
      holonomicCoordinateTransitionSecondDerivativeAt_symmetric period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate first second
        samePoint
  have hK : K first second vector = K second first vector := by
    simpa only [K, transition,
      holonomicCoordinateTransitionThirdDerivativeAt] using
      holonomicCoordinateTransitionThirdDerivativeAt_swap_outer period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint first
        second vector
  have hDu' :
      J (D1 first second vector) =
        D2 (J first) (J second) (J vector) +
            G2 secondCoordinate (H first second) (J vector) +
          G2 secondCoordinate (J second) (H first vector) +
        K first second vector -
          H first (G1 firstCoordinate second vector) := by
    rw [← hDu]
    abel
  have hDv' :
      J (D1 second first vector) =
        D2 (J second) (J first) (J vector) +
            G2 secondCoordinate (H second first) (J vector) +
          G2 secondCoordinate (J first) (H second vector) +
        K second first vector -
          H second (G1 firstCoordinate first vector) := by
    rw [← hDv]
    abel
  unfold localLeviCivitaRiemannVector
  change
    J (D1 first second vector - D1 second first vector +
        G1 firstCoordinate first (G1 firstCoordinate second vector) -
      G1 firstCoordinate second (G1 firstCoordinate first vector)) =
      D2 (J first) (J second) (J vector) -
          D2 (J second) (J first) (J vector) +
        G2 secondCoordinate (J first)
          (G2 secondCoordinate (J second) (J vector)) -
      G2 secondCoordinate (J second)
        (G2 secondCoordinate (J first) (J vector))
  simp only [map_sub, map_add]
  rw [hDu', hDv', hPu, hPv, hH, hK]
  abel

/-- Existing endomorphism-valued Riemann curvature as the coordinate-basis
source of the arbitrary-vector naturality law. -/
theorem localLeviCivitaRiemannEndomorphism_natural
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) (vector : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real transition firstCoordinate
        (localLeviCivitaRiemannEndomorphism period hPeriod metric firstPatch
          firstCoordinate first second vector) =
      localLeviCivitaRiemannVector period hPeriod metric secondPatch
        secondCoordinate
        (fderiv Real transition firstCoordinate (Pi.single first 1))
        (fderiv Real transition firstCoordinate (Pi.single second 1))
        (fderiv Real transition firstCoordinate vector) := by
  simpa only [localLeviCivitaRiemannVector_basis] using
    localLeviCivitaRiemannVector_natural period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
      (Pi.single first 1) (Pi.single second 1) vector

end

end P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
end JanusFormal
