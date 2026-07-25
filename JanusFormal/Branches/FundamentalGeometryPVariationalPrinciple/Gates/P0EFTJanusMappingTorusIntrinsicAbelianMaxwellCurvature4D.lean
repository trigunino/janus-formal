import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D

/-!
# Intrinsic abelian Maxwell curvature on the D8 quotient

The genuine gauge one-form is pulled back to every smooth holonomic chart and
its exterior derivative is taken there.  Naturality of the exterior
derivative proves the tensorial overlap law, so the resulting two-form is
independent of coordinates.  Exact gauge shifts have zero curvature by
`d² = 0`; no supplied field-strength or gauge-invariance hypothesis is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem smoothness_two_le_infty :
    minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

private def coordinateCovector (index : Index4) : Vector4 →L[Real] Real :=
  ContinuousLinearMap.proj index

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

/-- Coordinate coefficient of the genuine intrinsic gauge one-form. -/
def localGaugeCoefficient
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Index4) (coordinate : Vector4) : Real :=
  potential.toFun component (patch.coordinateMap coordinate)
    (patch.frame coordinate index)

theorem localGaugeCoefficient_contDiff
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Index4) :
    ContDiff Real ∞
      (localGaugeCoefficient period hPeriod potential component patch index) := by
  exact
    ((potential.contMDiff_eval component).comp
      (patch.frame_contMDiff index)).contDiff

/-- Pullback of the intrinsic gauge one-form to one genuine holonomic chart. -/
def localGaugeOneForm
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Vector4 → Vector4 [⋀^Fin 1]→L[Real] Real :=
  fun coordinate =>
    ∑ index : Index4,
      localGaugeCoefficient period hPeriod potential component patch index
          coordinate •
        ContinuousAlternatingMap.ofSubsingleton Real Vector4 Real (0 : Fin 1)
          (coordinateCovector index)

theorem localGaugeOneForm_contDiff
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localGaugeOneForm period hPeriod potential component patch) := by
  apply ContDiff.sum
  intro index _
  exact
    (localGaugeCoefficient_contDiff period hPeriod potential component patch
      index).smul_const _

/-- Evaluation of the coordinate one-form is evaluation of the intrinsic
one-form on the derivative of the coordinate map. -/
theorem localGaugeOneForm_apply
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4) :
    localGaugeOneForm period hPeriod potential component patch coordinate
        (fun _ => vector) =
      potential.toFun component (patch.coordinateMap coordinate)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate vector) := by
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch]
  have hFrame :
      ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
        (Equiv.refl Index4)) vector =
        ∑ index : Index4, vector index • patch.frame coordinate index := by
    have hVector :
        vector = ∑ index : Index4, vector index • Pi.single index 1 := by
      ext index
      simp [Pi.single_apply]
    conv_lhs => rw [hVector]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [map_smul]
    congr 1
    have hBasis :
        ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)) ((Pi.basisFun Real Index4) index) =
          patch.frame coordinate index := by
      exact Module.Basis.equiv_apply _ _ _ _
    simpa only [Pi.basisFun_apply] using hBasis
  rw [hFrame, map_sum]
  simp [localGaugeOneForm, localGaugeCoefficient, coordinateCovector,
    ContinuousAlternatingMap.smul_apply, mul_comm]

/-- The local Maxwell curvature is the actual exterior derivative `dA`. -/
def localGaugeCurvature
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Vector4 → Vector4 [⋀^Fin 2]→L[Real] Real :=
  extDeriv (localGaugeOneForm period hPeriod potential component patch)

theorem localGaugeCurvature_contDiff
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localGaugeCurvature period hPeriod potential component patch) := by
  have hDerivative :
      ContDiff Real ∞
        (fderiv Real
          (localGaugeOneForm period hPeriod potential component patch)) :=
    (localGaugeOneForm_contDiff period hPeriod potential component patch)
      |>.fderiv_right (m := ∞) (by simp)
  unfold localGaugeCurvature extDeriv
  simpa [Function.comp_def,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM Real Vector4 Real)
      |>.contDiff.comp hDerivative

private theorem gaugeEvaluation_eq_of_heq
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    {firstPoint secondPoint : EffectiveQuotient period hPeriod}
    (hPoint : firstPoint = secondPoint)
    (firstVector : TangentSpace coverModelWithCorners firstPoint)
    (secondVector : TangentSpace coverModelWithCorners secondPoint)
    (hVector : HEq firstVector secondVector) :
    potential.toFun component firstPoint firstVector =
      potential.toFun component secondPoint secondVector := by
  subst secondPoint
  rw [eq_of_heq hVector]

/-- The coordinate one-forms agree as pullbacks on every chart overlap. -/
theorem localGaugeOneForm_transition_eventuallyEq
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localGaugeOneForm period hPeriod potential component firstPatch =ᶠ[
        𝓝 firstCoordinate]
      fun current =>
        (localGaugeOneForm period hPeriod potential component secondPatch
          (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint current))
          |>.compContinuousLinearMap
            (fderiv Real
              (holonomicCoordinateTransitionAt period hPeriod firstPatch
                secondPatch firstCoordinate secondCoordinate samePoint)
              current) := by
  filter_upwards [
    (holonomicCoordinateTransitionDomainAt_isOpen period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).mem_nhds
      (firstCoordinate_mem_holonomicCoordinateTransitionDomainAt period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)]
    with current hCurrent
  apply ContinuousAlternatingMap.ext
  intro vectors
  have hVectors : vectors = fun _ => vectors 0 := by
    funext index
    rw [Subsingleton.elim index 0]
  rw [hVectors]
  rw [localGaugeOneForm_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change
    potential.toFun component (firstPatch.coordinateMap current)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          firstPatch.coordinateMap current (vectors 0)) =
      localGaugeOneForm period hPeriod potential component secondPatch
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint current)
        (fun _ =>
          fderiv Real
            (holonomicCoordinateTransitionAt period hPeriod firstPatch
              secondPatch firstCoordinate secondCoordinate samePoint)
            current (vectors 0))
  rw [localGaugeOneForm_apply]
  exact gaugeEvaluation_eq_of_heq period hPeriod potential component
    (holonomicCoordinateTransitionAt_reconstructs_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current samePoint
      hCurrent).symm _ _
    (holonomicCoordinateMap_mfderiv_transition_heq_of_mem period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate current
      (vectors 0) samePoint hCurrent)

/-- Maxwell curvature has the genuine tensorial two-form transition law. -/
theorem localGaugeCurvature_transition
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localGaugeCurvature period hPeriod potential component firstPatch
        firstCoordinate =
      (localGaugeCurvature period hPeriod potential component secondPatch
        secondCoordinate).compContinuousLinearMap
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint :
          Vector4 →L[Real] Vector4) := by
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  have hLocal :
      extDeriv
          (localGaugeOneForm period hPeriod potential component firstPatch)
          firstCoordinate =
        extDeriv
          (fun current =>
            (localGaugeOneForm period hPeriod potential component secondPatch
              (transition current)).compContinuousLinearMap
                (fderiv Real transition current))
          firstCoordinate :=
    (localGaugeOneForm_transition_eventuallyEq period hPeriod potential component
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.extDeriv_eq
  have hSecond :
      DifferentiableAt Real
        (localGaugeOneForm period hPeriod potential component secondPatch)
        (transition firstCoordinate) :=
    (localGaugeOneForm_contDiff period hPeriod potential component secondPatch)
      |>.differentiable (by simp) _
  have hTransition :
      ContDiffAt Real ∞ transition firstCoordinate :=
    (holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
      |>.contMDiffAt.contDiffAt
  rw [localGaugeCurvature, hLocal]
  rw [extDeriv_pullback (r := ∞) hSecond hTransition smoothness_two_le_infty]
  simp only [transition, holonomicCoordinateTransitionAt_apply,
    localGaugeCurvature]
  rw [← holonomicCoordinateTransitionLinearEquivAt_coe]

private def localGhostZeroForm
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Vector4 → Vector4 [⋀^Fin 0]→L[Real] Real :=
  fun coordinate =>
    ContinuousAlternatingMap.constOfIsEmpty Real Vector4 (Fin 0)
      (localScalarRepresentative period hPeriod
        (ghostComponent period hPeriod parameter component) patch coordinate)

private theorem localGhostZeroForm_contDiff
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localGhostZeroForm period hPeriod parameter component patch) := by
  exact
    (ContinuousAlternatingMap.constOfIsEmptyLIE Real Vector4 Real (Fin 0))
      |>.contDiff.comp
      (localScalarRepresentative_contDiff period hPeriod
        (ghostComponent period hPeriod parameter component) patch)

/-- Pulling back an exact intrinsic potential gives the exterior derivative
of the pulled-back gauge parameter. -/
theorem localGaugeOneForm_exact
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localGaugeOneForm period hPeriod
        (exactGaugePotential period hPeriod parameter) component patch =
      extDeriv (localGhostZeroForm period hPeriod parameter component patch) := by
  funext coordinate
  unfold localGhostZeroForm
  rw [extDeriv_constOfIsEmpty]
  apply ContinuousAlternatingMap.ext
  intro vectors
  change
    (∑ index : Index4,
        (exactGaugePotential period hPeriod parameter).toFun component
            (patch.coordinateMap coordinate) (patch.frame coordinate index) *
          vectors 0 index) =
      fderiv Real
        (localScalarRepresentative period hPeriod
          (ghostComponent period hPeriod parameter component) patch)
        coordinate (vectors 0)
  rw [continuousLinearMap_apply_eq_sum_basis
    (fderiv Real
      (localScalarRepresentative period hPeriod
        (ghostComponent period hPeriod parameter component) patch) coordinate)
    (vectors 0)]
  apply Finset.sum_congr rfl
  intro index _
  change
    scalarDifferential period hPeriod
          (ghostComponent period hPeriod parameter component)
          (patch.coordinateMap coordinate) (patch.frame coordinate index) *
        vectors 0 index =
      vectors 0 index *
        localScalarGradient period hPeriod
          (ghostComponent period hPeriod parameter component) patch coordinate
          index
  rw [localScalarGradient_eq_scalarDifferential_frame period hPeriod
    (ghostComponent period hPeriod parameter component) patch coordinate index]
  ring

theorem localGaugeOneForm_add
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localGaugeOneForm period hPeriod (first + second) component patch =
      localGaugeOneForm period hPeriod first component patch +
        localGaugeOneForm period hPeriod second component patch := by
  funext coordinate
  simp only [localGaugeOneForm, localGaugeCoefficient, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  change
    (first.toFun component (patch.coordinateMap coordinate)
          (patch.frame coordinate index) +
        second.toFun component (patch.coordinateMap coordinate)
          (patch.frame coordinate index)) •
        ContinuousAlternatingMap.ofSubsingleton Real Vector4 Real (0 : Fin 1)
          (coordinateCovector index) =
      first.toFun component (patch.coordinateMap coordinate)
          (patch.frame coordinate index) •
          ContinuousAlternatingMap.ofSubsingleton Real Vector4 Real (0 : Fin 1)
            (coordinateCovector index) +
        second.toFun component (patch.coordinateMap coordinate)
          (patch.frame coordinate index) •
          ContinuousAlternatingMap.ofSubsingleton Real Vector4 Real (0 : Fin 1)
            (coordinateCovector index)
  rw [add_smul]

/-- The derived Maxwell curvature is invariant under every exact abelian
gauge transformation. -/
theorem localGaugeCurvature_gaugeTransform
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localGaugeCurvature period hPeriod
        (gaugeTransform period hPeriod parameter potential) component patch =
      localGaugeCurvature period hPeriod potential component patch := by
  funext coordinate
  rw [gaugeTransform, localGaugeCurvature, localGaugeOneForm_add]
  rw [extDeriv_add
    ((localGaugeOneForm_contDiff period hPeriod potential component patch)
      |>.differentiable (by simp) coordinate)
    ((localGaugeOneForm_contDiff period hPeriod
      (exactGaugePotential period hPeriod parameter) component patch)
      |>.differentiable (by simp) coordinate)]
  rw [localGaugeOneForm_exact]
  rw [extDeriv_extDeriv_apply (r := ∞)
    ((localGhostZeroForm_contDiff period hPeriod parameter component patch)
      |>.contDiffAt) smoothness_two_le_infty]
  exact add_zero _

end

end P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
end JanusFormal
