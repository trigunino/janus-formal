import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D

/-!
# Frame-free Maxwell action and its conformal Hessian

The intrinsic abelian curvature and the inverse Lorentz metric are contracted
without a supplied frame field.  The resulting scalar globalizes across the
canonical holonomic atlas and defines a frame-free Maxwell action.

In four dimensions, a positive conformal rescaling multiplies the inverse
metric contraction by `scale⁻²` and the relative Lorentz volume by `scale²`.
For a fixed gauge potential the action is therefore exactly constant on every
positive exponential conformal curve, so its conformal metric Hessian is zero.

This does not construct a Hessian in arbitrary metric directions, vary the
gauge potential, or identify a mixed metric--gauge block.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Conformal scaling of the local contraction -/

theorem localMetricInverse_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localMetricMatrix period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate)⁻¹ =
      (scale (patch.coordinateMap coordinate))⁻¹ •
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ := by
  letI : Invertible (scale (patch.coordinateMap coordinate)) :=
    invertibleOfNonzero (ne_of_gt (hScale _))
  rw [localMetricMatrix_conformal, Matrix.inv_smul]
  · rw [invOf_eq_inv]
  · exact isUnit_iff_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)

theorem localMaxwellPairing_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellPairing period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        first second patch coordinate =
      (scale (patch.coordinateMap coordinate))⁻¹ ^ 2 *
        localMaxwellPairing period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          first second patch coordinate := by
  simp only [localMaxwellPairing, localMetricInverse_conformal,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem localMaxwellLagrangian_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMaxwellLagrangian period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        potential patch coordinate =
      (scale (patch.coordinateMap coordinate))⁻¹ ^ 2 *
        localMaxwellLagrangian period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          potential patch coordinate := by
  unfold localMaxwellLagrangian
  rw [localMaxwellPairing_conformal]
  ring

/-! ## Smoothness of the local scalar -/

theorem localGaugeCurvatureMatrix_entry_contDiff
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localGaugeCurvatureMatrix period hPeriod potential component patch
        coordinate first second) := by
  let vectors : Fin 2 → Vector4 :=
    ![Pi.single first 1, Pi.single second 1]
  have hEvaluation :
      ContDiff Real ∞ (fun coordinate =>
        localGaugeCurvature period hPeriod potential component patch coordinate
          vectors) :=
    (ContinuousAlternatingMap.apply Real Vector4 Real vectors).contDiff.comp
      (localGaugeCurvature_contDiff period hPeriod potential component patch)
  change ContDiff Real ∞ (fun coordinate =>
    localGaugeCurvature period hPeriod potential component patch coordinate
      vectors)
  exact hEvaluation

theorem localMaxwellPairing_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localMaxwellPairing period hPeriod metric first second patch) := by
  apply ContDiff.sum
  intro component _
  apply ContDiff.sum
  intro μ _
  apply ContDiff.sum
  intro ν _
  apply ContDiff.sum
  intro ρ _
  apply ContDiff.sum
  intro σ _
  exact
    ((((localMetricInverseEntry_contDiff
          period hPeriod metric patch μ ρ).mul
        (localMetricInverseEntry_contDiff
          period hPeriod metric patch ν σ)).mul
      (localGaugeCurvatureMatrix_entry_contDiff
        period hPeriod first component patch μ ν)).mul
      (localGaugeCurvatureMatrix_entry_contDiff
        period hPeriod second component patch ρ σ))

theorem localMaxwellLagrangian_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localMaxwellLagrangian period hPeriod metric potential patch) := by
  unfold localMaxwellLagrangian
  exact contDiff_const.mul
    (localMaxwellPairing_contDiff
      period hPeriod metric potential potential patch)

/-! ## Tensorial transition and globalization -/

private theorem updateVectorPair_zero
    (first second replacement : Vector4) :
    Function.update ![first, second] (0 : Fin 2) replacement =
      ![replacement, second] := by
  funext index
  fin_cases index <;> simp [Function.update]

private theorem updateVectorPair_one
    (first second replacement : Vector4) :
    Function.update ![first, second] (1 : Fin 2) replacement =
      ![first, replacement] := by
  funext index
  fin_cases index <;> simp [Function.update]

/-- A two-form viewed as its underlying bilinear form. -/
def alternatingTwoFormToBilin
    (form : Vector4 [⋀^Fin 2]→L[Real] Real) :
    LinearMap.BilinForm Real Vector4 :=
  LinearMap.mk₂ Real
    (fun first second => form ![first, second])
    (by
      intro first second third
      have h :=
        form.map_update_add (![0, third]) (0 : Fin 2) first second
      simpa only [updateVectorPair_zero] using h)
    (by
      intro scalar first second
      have h :=
        form.map_update_smul (![0, second]) (0 : Fin 2) scalar first
      simpa only [updateVectorPair_zero, smul_eq_mul] using h)
    (by
      intro first second third
      have h :=
        form.map_update_add (![first, 0]) (1 : Fin 2) second third
      simpa only [updateVectorPair_one] using h)
    (by
      intro scalar first second
      have h :=
        form.map_update_smul (![first, 0]) (1 : Fin 2) scalar second
      simpa only [updateVectorPair_one, smul_eq_mul] using h)

@[simp]
theorem alternatingTwoFormToBilin_apply
    (form : Vector4 [⋀^Fin 2]→L[Real] Real)
    (first second : Vector4) :
    alternatingTwoFormToBilin form first second = form ![first, second] :=
  rfl

theorem localGaugeCurvatureMatrix_eq_toMatrix
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localGaugeCurvatureMatrix period hPeriod potential component patch
        coordinate =
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4)
        (alternatingTwoFormToBilin
          (localGaugeCurvature period hPeriod potential component patch
            coordinate)) := by
  ext first second
  rw [LinearMap.BilinForm.toMatrix_apply]
  change
    (localGaugeCurvature period hPeriod potential component patch coordinate)
        ![Pi.single first 1, Pi.single second 1] =
      alternatingTwoFormToBilin
        (localGaugeCurvature period hPeriod potential component patch coordinate)
        ((Pi.basisFun Real Index4) first)
        ((Pi.basisFun Real Index4) second)
  rw [alternatingTwoFormToBilin_apply]
  simp only [Pi.basisFun_apply]

theorem localGaugeCurvatureMatrix_transition
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localGaugeCurvatureMatrix period hPeriod potential component firstPatch
        firstCoordinate =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint).transpose *
        localGaugeCurvatureMatrix period hPeriod potential component secondPatch
          secondCoordinate *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint := by
  let transition :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).toLinearEquiv.toLinearMap
  let secondForm : LinearMap.BilinForm Real Vector4 :=
    alternatingTwoFormToBilin
      (localGaugeCurvature period hPeriod potential component secondPatch
        secondCoordinate)
  have hForms :
      alternatingTwoFormToBilin
          (localGaugeCurvature period hPeriod potential component firstPatch
            firstCoordinate) =
        secondForm.comp transition transition := by
    apply LinearMap.ext₂
    intro first second
    change
      (localGaugeCurvature period hPeriod potential component firstPatch
          firstCoordinate) ![first, second] =
        (localGaugeCurvature period hPeriod potential component secondPatch
          secondCoordinate) ![transition first, transition second]
    calc
      (localGaugeCurvature period hPeriod potential component firstPatch
          firstCoordinate) ![first, second] =
          ((localGaugeCurvature period hPeriod potential component secondPatch
              secondCoordinate).compContinuousLinearMap
            (holonomicCoordinateTransitionLinearEquivAt period hPeriod
              firstPatch secondPatch firstCoordinate secondCoordinate
              samePoint : Vector4 →L[Real] Vector4)) ![first, second] := by
        exact congrArg
          (fun form : Vector4 [⋀^Fin 2]→L[Real] Real =>
            form ![first, second])
          (localGaugeCurvature_transition period hPeriod potential component
            firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      _ = _ := by
        rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
        congr 1
        funext index
        fin_cases index <;> rfl
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_comp
      (b := Pi.basisFun Real Index4)
      (c := Pi.basisFun Real Index4)
      secondForm transition transition
  rw [← hForms] at hCongruence
  rw [← localGaugeCurvatureMatrix_eq_toMatrix
      period hPeriod potential component firstPatch firstCoordinate,
    ← localGaugeCurvatureMatrix_eq_toMatrix
      period hPeriod potential component secondPatch secondCoordinate]
    at hCongruence
  exact hCongruence

/-- Algebraic inverse-metric contraction of two covariant two-tensors. -/
def matrixMaxwellContraction
    (inverseMetric first second : Matrix4) : Real :=
  ∑ μ : Index4, ∑ ν : Index4, ∑ ρ : Index4, ∑ σ : Index4,
    inverseMetric μ ρ * inverseMetric ν σ *
      first μ ν * second ρ σ

private theorem sumFour_permute
    (f : Index4 → Index4 → Index4 → Index4 → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ b, ∑ a, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ b, ∑ a, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]

private theorem matrixMaxwellContraction_eq_trace
    (inverseMetric first second : Matrix4) :
    matrixMaxwellContraction inverseMetric first second =
      Matrix.trace
        (inverseMetric.transpose * first *
          inverseMetric * second.transpose) := by
  unfold matrixMaxwellContraction Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [sumFour_permute]
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- The matrix Maxwell contraction is invariant under an invertible change
of basis. -/
theorem matrixMaxwellContraction_congruence
    (transition metric first second : Matrix4)
    (hTransition : IsUnit transition) :
    matrixMaxwellContraction
        (transition.transpose * metric * transition)⁻¹
        (transition.transpose * first * transition)
        (transition.transpose * second * transition) =
      matrixMaxwellContraction metric⁻¹ first second := by
  rw [matrixMaxwellContraction_eq_trace,
    matrixMaxwellContraction_eq_trace]
  have hDet : IsUnit transition.det :=
    (Matrix.isUnit_iff_isUnit_det transition).mp hTransition
  have hTransposeDet : IsUnit transition.transpose.det :=
    Matrix.isUnit_det_transpose transition hDet
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv]
  calc
    _ = Matrix.trace
        (transition⁻¹ *
          (metric.transpose⁻¹ * first * metric⁻¹ * second.transpose) *
          transition) := by
      congr 1
      simp only [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left transition.transpose _
        hTransposeDet]
      rw [Matrix.mul_nonsing_inv_cancel_left transition _ hDet]
      rw [Matrix.nonsing_inv_mul_cancel_left transition.transpose _
        hTransposeDet]
    _ = _ :=
      Matrix.trace_conj' hTransition
        (metric.transpose⁻¹ * first * metric⁻¹ * second.transpose)

theorem localMaxwellPairing_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localMaxwellPairing period hPeriod metric first second firstPatch
        firstCoordinate =
      localMaxwellPairing period hPeriod metric first second secondPatch
        secondCoordinate := by
  let transition :=
    holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  have hTransition : IsUnit transition := by
    simpa only [transition] using
      holonomicCoordinateTransitionMatrixAt_isUnit period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  have hMetric :
      localMetricMatrix period hPeriod metric firstPatch firstCoordinate =
        transition.transpose *
          localMetricMatrix period hPeriod metric secondPatch
            secondCoordinate *
          transition := by
    simpa only [transition] using
      localMetricMatrix_transition_congruence period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
  change
    (∑ component : Fin 2,
      matrixMaxwellContraction
        (localMetricMatrix period hPeriod metric firstPatch firstCoordinate)⁻¹
        (localGaugeCurvatureMatrix period hPeriod first component firstPatch
          firstCoordinate)
        (localGaugeCurvatureMatrix period hPeriod second component firstPatch
          firstCoordinate)) =
      ∑ component : Fin 2,
        matrixMaxwellContraction
          (localMetricMatrix period hPeriod metric secondPatch
            secondCoordinate)⁻¹
          (localGaugeCurvatureMatrix period hPeriod first component secondPatch
            secondCoordinate)
          (localGaugeCurvatureMatrix period hPeriod second component secondPatch
            secondCoordinate)
  apply Finset.sum_congr rfl
  intro component _
  have hFirst :=
    localGaugeCurvatureMatrix_transition period hPeriod first component
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint
  have hSecond :=
    localGaugeCurvatureMatrix_transition period hPeriod second component
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint
  rw [hMetric, hFirst, hSecond]
  exact matrixMaxwellContraction_congruence transition
    (localMetricMatrix period hPeriod metric secondPatch secondCoordinate)
    (localGaugeCurvatureMatrix period hPeriod first component secondPatch
      secondCoordinate)
    (localGaugeCurvatureMatrix period hPeriod second component secondPatch
      secondCoordinate) hTransition

structure MaxwellPairingChartWitness
    (point : EffectiveQuotient period hPeriod) where
  patch : SmoothHolonomicFrameChart4 period hPeriod
  coordinate : Vector4
  coordinateMap_eq : patch.coordinateMap coordinate = point

private theorem maxwellPairingChartWitness_nonempty
    (point : EffectiveQuotient period hPeriod) :
    Nonempty (MaxwellPairingChartWitness period hPeriod point) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  exact ⟨⟨patch, coordinate, hCoordinate⟩⟩

def selectedMaxwellPairingChart
    (point : EffectiveQuotient period hPeriod) :
    MaxwellPairingChartWitness period hPeriod point :=
  Classical.choice
    (maxwellPairingChartWitness_nonempty period hPeriod point)

/-- Chart-independent inverse-metric contraction of two abelian curvatures. -/
def globalMaxwellPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness := selectedMaxwellPairingChart period hPeriod point
  localMaxwellPairing period hPeriod metric first second witness.patch
    witness.coordinate

theorem globalMaxwellPairing_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalMaxwellPairing period hPeriod metric first second
        (patch.coordinateMap coordinate) =
      localMaxwellPairing period hPeriod metric first second patch
        coordinate := by
  let witness :=
    selectedMaxwellPairingChart period hPeriod
      (patch.coordinateMap coordinate)
  change
    localMaxwellPairing period hPeriod metric first second witness.patch
        witness.coordinate =
      localMaxwellPairing period hPeriod metric first second patch coordinate
  exact localMaxwellPairing_transition period hPeriod metric first second
    witness.patch patch witness.coordinate coordinate witness.coordinateMap_eq

theorem globalMaxwellPairing_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (globalMaxwellPairing period hPeriod metric first second) := by
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let hLocal := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hRepresentative :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (localMaxwellPairing period hPeriod metric first second patch ∘
          hLocal.localInverse)
        (patch.coordinateMap coordinate) :=
    (localMaxwellPairing_contDiff period hPeriod metric first second patch)
      |>.contMDiff.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hRepresentative.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
  have hRight :
      patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
    simpa only [Function.comp_apply, id_eq] using hNearby
  change
    globalMaxwellPairing period hPeriod metric first second nearby =
      localMaxwellPairing period hPeriod metric first second patch
        (hLocal.localInverse nearby)
  calc
    globalMaxwellPairing period hPeriod metric first second nearby =
        globalMaxwellPairing period hPeriod metric first second
          (patch.coordinateMap (hLocal.localInverse nearby)) :=
      congrArg (globalMaxwellPairing period hPeriod metric first second)
        hRight.symm
    _ = _ := globalMaxwellPairing_eq_local period hPeriod metric first second
      patch (hLocal.localInverse nearby)

/-- Smooth global scalar represented by the local Maxwell contraction. -/
def globalSmoothMaxwellPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := globalMaxwellPairing period hPeriod metric first second
  contMDiff_toFun :=
    globalMaxwellPairing_contMDiff period hPeriod metric first second

/-! ## Frame-free density and action -/

theorem globalMaxwellPairing_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        first second point =
      (scale point)⁻¹ ^ 2 *
        globalMaxwellPairing period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          first second point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        first second witness.patch witness.coordinate =
      (scale point)⁻¹ ^ 2 *
        localMaxwellPairing period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          first second witness.patch witness.coordinate
  rw [localMaxwellPairing_conformal, witness.coordinateMap_eq]

/-- Global Maxwell Lagrangian `-1/4 F²` for a fixed gauge potential. -/
def frameFreeMaxwellDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    -(1 / 4 : Real) *
      globalMaxwellPairing period hPeriod metric potential potential point
  contMDiff_toFun :=
    contMDiff_const.mul
      (globalMaxwellPairing_contMDiff
        period hPeriod metric potential potential)

theorem frameFreeMaxwellDensity_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    frameFreeMaxwellDensity period hPeriod metric potential
        (patch.coordinateMap coordinate) =
      localMaxwellLagrangian period hPeriod metric potential patch
        coordinate := by
  change
    -(1 / 4 : Real) *
        globalMaxwellPairing period hPeriod metric potential potential
          (patch.coordinateMap coordinate) =
      _
  rw [globalMaxwellPairing_eq_local]
  rfl

theorem frameFreeMaxwellDensity_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeMaxwellDensity period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        potential point =
      (scale point)⁻¹ ^ 2 *
        frameFreeMaxwellDensity period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          potential point := by
  change
    -(1 / 4 : Real) *
        globalMaxwellPairing period hPeriod
          (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
          potential potential point =
      (scale point)⁻¹ ^ 2 *
        (-(1 / 4 : Real) *
          globalMaxwellPairing period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            potential potential point)
  rw [globalMaxwellPairing_conformal]
  ring

/-- Exact cancellation of the conformal Maxwell weight with the four-volume
weight in dimension four. -/
theorem relativeFrameFreeMaxwellDensity_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
          (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
          point *
        frameFreeMaxwellDensity period hPeriod
          (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
          potential point =
      frameFreeMaxwellDensity period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        potential point := by
  rw [globalMetricVolumeRatio_conformal,
    frameFreeMaxwellDensity_conformal]
  field_simp [ne_of_gt (hScale point)]

/-- Maxwell action measured by the Lorentz volume of the same metric. -/
def generalLorentzFrameFreeMaxwellAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Real :=
  ∫ point,
    frameFreeMaxwellDensity period hPeriod metric potential point
      ∂generalLorentzVolumeMeasure period hPeriod metric

theorem frameFreeMaxwellDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    Integrable
      (frameFreeMaxwellDensity period hPeriod metric potential)
      (generalLorentzVolumeMeasure period hPeriod metric) := by
  letI := generalLorentzVolumeMeasure_isFinite period hPeriod metric
  exact
    (frameFreeMaxwellDensity period hPeriod metric potential)
      |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem generalLorentzFrameFreeMaxwellAction_eq_reference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    generalLorentzFrameFreeMaxwellAction period hPeriod metric potential =
      ∫ point,
        globalMetricVolumeRatio period hPeriod metric point *
          frameFreeMaxwellDensity period hPeriod metric potential point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  exact integral_generalLorentzVolumeMeasure_eq_reference
    period hPeriod metric
      (frameFreeMaxwellDensity period hPeriod metric potential)

/-- Fixed intrinsic reference value of the Maxwell action. -/
def intrinsicCanonicalFrameFreeMaxwellAction
    (potential : SmoothAbelianGaugePotential period hPeriod) : Real :=
  ∫ point,
    frameFreeMaxwellDensity period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      potential point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem generalLorentzFrameFreeMaxwellAction_intrinsic
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    generalLorentzFrameFreeMaxwellAction period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) potential =
      intrinsicCanonicalFrameFreeMaxwellAction
        period hPeriod potential := by
  unfold generalLorentzFrameFreeMaxwellAction
    intrinsicCanonicalFrameFreeMaxwellAction
  rw [generalLorentzVolumeMeasure_intrinsic]

theorem generalLorentzFrameFreeMaxwellAction_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    generalLorentzFrameFreeMaxwellAction period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        potential =
      intrinsicCanonicalFrameFreeMaxwellAction
        period hPeriod potential := by
  rw [generalLorentzFrameFreeMaxwellAction_eq_reference]
  unfold intrinsicCanonicalFrameFreeMaxwellAction
  apply integral_congr_ae
  filter_upwards [] with point
  exact relativeFrameFreeMaxwellDensity_conformal
    period hPeriod scale hScale potential point

/-! ## Constant conformal action curve and null Hessian -/

def conformalFrameFreeMaxwellActionCurve
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod
    (conformalLorentzMetricCurve period hPeriod
      baseScale direction hBaseScale parameter)
    potential

theorem conformalFrameFreeMaxwellActionCurve_eq_reference
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : Real) :
    conformalFrameFreeMaxwellActionCurve period hPeriod
        baseScale direction hBaseScale potential parameter =
      intrinsicCanonicalFrameFreeMaxwellAction
        period hPeriod potential := by
  exact generalLorentzFrameFreeMaxwellAction_conformal period hPeriod
    (positiveConformalScaleCurve
      period hPeriod baseScale direction parameter)
    (positiveConformalScaleCurve_pos
      period hPeriod baseScale direction hBaseScale parameter)
    potential

theorem conformalFrameFreeMaxwellActionCurve_contDiff
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ContDiff Real ∞
      (conformalFrameFreeMaxwellActionCurve period hPeriod
        baseScale direction hBaseScale potential) := by
  rw [show
    conformalFrameFreeMaxwellActionCurve period hPeriod
        baseScale direction hBaseScale potential =
      fun _parameter =>
        intrinsicCanonicalFrameFreeMaxwellAction
          period hPeriod potential by
    funext parameter
    exact conformalFrameFreeMaxwellActionCurve_eq_reference
      period hPeriod baseScale direction hBaseScale potential parameter]
  exact contDiff_const

theorem conformalFrameFreeMaxwellActionCurve_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (conformalFrameFreeMaxwellActionCurve period hPeriod
        baseScale direction hBaseScale potential)
      0 parameter := by
  have hConstant :
      conformalFrameFreeMaxwellActionCurve period hPeriod
          baseScale direction hBaseScale potential =
        fun _varied =>
          intrinsicCanonicalFrameFreeMaxwellAction
            period hPeriod potential := by
    funext varied
    exact conformalFrameFreeMaxwellActionCurve_eq_reference
      period hPeriod baseScale direction hBaseScale potential varied
  rw [hConstant]
  exact hasDerivAt_const parameter _

theorem conformalFrameFreeMaxwellActionCurve_deriv
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : Real) :
    deriv
        (conformalFrameFreeMaxwellActionCurve period hPeriod
          baseScale direction hBaseScale potential)
        parameter =
      0 :=
  (conformalFrameFreeMaxwellActionCurve_hasDerivAt
    period hPeriod baseScale direction hBaseScale potential parameter).deriv

/-- Two-parameter positive conformal surface, implemented by two commuting
exponential rescalings. -/
def conformalFrameFreeMaxwellMixedActionCurve
    (baseScale first second : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod
    (conformalLorentzMetricCurve period hPeriod
      (positiveConformalScaleCurve
        period hPeriod baseScale second secondParameter)
      first
      (positiveConformalScaleCurve_pos
        period hPeriod baseScale second hBaseScale secondParameter)
      firstParameter)
    potential

theorem conformalFrameFreeMaxwellMixedActionCurve_eq_reference
    (baseScale first second : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) :
    conformalFrameFreeMaxwellMixedActionCurve period hPeriod
        baseScale first second hBaseScale potential
        firstParameter secondParameter =
      intrinsicCanonicalFrameFreeMaxwellAction
        period hPeriod potential := by
  exact generalLorentzFrameFreeMaxwellAction_conformal period hPeriod
    (positiveConformalScaleCurve period hPeriod
      (positiveConformalScaleCurve
        period hPeriod baseScale second secondParameter)
      first firstParameter)
    (positiveConformalScaleCurve_pos period hPeriod
      (positiveConformalScaleCurve
        period hPeriod baseScale second secondParameter)
      first
      (positiveConformalScaleCurve_pos
        period hPeriod baseScale second hBaseScale secondParameter)
      firstParameter)
    potential

theorem conformalFrameFreeMaxwellMixedActionCurve_hasDerivAt_first
    (baseScale first second : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) :
    HasDerivAt
      (fun varied =>
        conformalFrameFreeMaxwellMixedActionCurve period hPeriod
          baseScale first second hBaseScale potential varied secondParameter)
      0 firstParameter := by
  rw [show
    (fun varied =>
      conformalFrameFreeMaxwellMixedActionCurve period hPeriod
        baseScale first second hBaseScale potential varied secondParameter) =
      fun _varied =>
        intrinsicCanonicalFrameFreeMaxwellAction
          period hPeriod potential by
    funext varied
    exact conformalFrameFreeMaxwellMixedActionCurve_eq_reference
      period hPeriod baseScale first second hBaseScale potential
        varied secondParameter]
  exact hasDerivAt_const firstParameter _

/-- The metric Hessian restricted to conformal tangent directions. -/
def conformalFrameFreeMaxwellHessian
    (_potential : SmoothAbelianGaugePotential period hPeriod) :
    LinearMap.BilinForm Real (SmoothScalarField period hPeriod) :=
  0

@[simp]
theorem conformalFrameFreeMaxwellHessian_eq_zero
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : SmoothScalarField period hPeriod) :
    conformalFrameFreeMaxwellHessian
        period hPeriod potential first second =
      0 :=
  rfl

theorem conformalFrameFreeMaxwellHessian_symmetric
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : SmoothScalarField period hPeriod) :
    conformalFrameFreeMaxwellHessian
        period hPeriod potential first second =
      conformalFrameFreeMaxwellHessian
        period hPeriod potential second first :=
  rfl

theorem conformalFrameFreeMaxwellActionCurve_deriv_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (conformalFrameFreeMaxwellActionCurve period hPeriod
            baseScale direction hBaseScale potential)
          varied)
      (conformalFrameFreeMaxwellHessian
        period hPeriod potential direction direction)
      parameter := by
  rw [show
    (fun varied =>
      deriv
        (conformalFrameFreeMaxwellActionCurve period hPeriod
          baseScale direction hBaseScale potential)
        varied) =
      fun _varied => 0 by
    funext varied
    exact conformalFrameFreeMaxwellActionCurve_deriv
      period hPeriod baseScale direction hBaseScale potential varied]
  exact hasDerivAt_const parameter 0

/-- The mixed derivative on the two-parameter logarithmic conformal surface
is the zero bilinear Hessian. -/
theorem conformalFrameFreeMaxwellMixedActionCurve_deriv_hasDerivAt_second
    (baseScale first second : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (fun firstVaried =>
            conformalFrameFreeMaxwellMixedActionCurve period hPeriod
              baseScale first second hBaseScale potential
              firstVaried varied)
          firstParameter)
      (conformalFrameFreeMaxwellHessian
        period hPeriod potential first second)
      secondParameter := by
  rw [show
    (fun varied =>
      deriv
        (fun firstVaried =>
          conformalFrameFreeMaxwellMixedActionCurve period hPeriod
            baseScale first second hBaseScale potential
            firstVaried varied)
        firstParameter) =
      fun _varied => 0 by
    funext varied
    exact
      (conformalFrameFreeMaxwellMixedActionCurve_hasDerivAt_first
        period hPeriod baseScale first second hBaseScale potential
          firstParameter varied).deriv]
  exact hasDerivAt_const secondParameter 0

end

end P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
end JanusFormal
