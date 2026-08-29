import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D

/-!
# Local Ricci and scalar-curvature naturality

The arbitrary-vector Riemann transformation law is contracted by trace to
obtain Ricci covariance.  Metric congruence then cancels the two remaining
Jacobian factors in the inverse-metric contraction, proving unconditional
local scalar-curvature naturality.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D

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
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicRiemannEndomorphismBridge4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Vector4
abbrev Index4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Index4
abbrev Matrix4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Matrix4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem localChristoffelApply_fixed_differentiableAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) :
    DifferentiableAt Real
      (fun current =>
        localLeviCivitaChristoffelApply period hPeriod metric patch current
          first second)
      coordinate := by
  apply differentiableAt_pi.mpr
  intro upper
  simp only [localLeviCivitaChristoffelApply, Matrix.toBilin'_apply]
  apply DifferentiableAt.fun_sum
  intro firstIndex _
  apply DifferentiableAt.fun_sum
  intro secondIndex _
  exact
    ((differentiableAt_const _).mul
      ((localLeviCivitaChristoffel_contDiff period hPeriod metric patch
        upper firstIndex secondIndex).differentiable (by simp)
          coordinate)).mul (differentiableAt_const _)

private theorem localLeviCivitaRiemannVector_add_first
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first₁ first₂ second vector : Vector4) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate
        (first₁ + first₂) second vector =
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first₁ second vector +
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first₂ second vector := by
  let gamma := fun current first second =>
    localLeviCivitaChristoffelApply period hPeriod metric patch current
      first second
  have hGamma₁ :
      DifferentiableAt Real (fun current => gamma current first₁ vector)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate first₁ vector
  have hGamma₂ :
      DifferentiableAt Real (fun current => gamma current first₂ vector)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate first₂ vector
  have hFunction :
      (fun current => gamma current (first₁ + first₂) vector) =
        (fun current => gamma current first₁ vector) +
          fun current => gamma current first₂ vector := by
    funext current
    change
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current (first₁ + first₂) vector =
        localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            current first₁ vector +
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            current first₂ vector
    simp only [map_add, LinearMap.add_apply]
  unfold localLeviCivitaRiemannVector
  change
    fderiv Real (fun current => gamma current second vector) coordinate
          (first₁ + first₂) -
        fderiv Real (fun current => gamma current (first₁ + first₂) vector)
          coordinate second +
      gamma coordinate (first₁ + first₂) (gamma coordinate second vector) -
      gamma coordinate second (gamma coordinate (first₁ + first₂) vector) =
      _
  rw [map_add, hFunction, fderiv_add hGamma₁ hGamma₂]
  simp only [add_apply, gamma]
  change
    _ +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate (first₁ + first₂) _ -
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate second
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate (first₁ + first₂) vector) =
      _
  simp only [map_add, LinearMap.add_apply,
    localLeviCivitaChristoffelBilinearMap_apply]
  abel

private theorem localLeviCivitaRiemannVector_smul_first
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : Vector4) (scalar : Real) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate
        (scalar • first) second vector =
      scalar •
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second vector := by
  let gamma := fun current first second =>
    localLeviCivitaChristoffelApply period hPeriod metric patch current
      first second
  have hFunction :
      (fun current => gamma current (scalar • first) vector) =
        scalar • fun current => gamma current first vector := by
    funext current
    change
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current (scalar • first) vector =
        scalar •
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            current first vector
    simp only [map_smul, LinearMap.smul_apply]
  unfold localLeviCivitaRiemannVector
  change
    fderiv Real (fun current => gamma current second vector) coordinate
          (scalar • first) -
        fderiv Real (fun current => gamma current (scalar • first) vector)
          coordinate second +
      gamma coordinate (scalar • first) (gamma coordinate second vector) -
      gamma coordinate second (gamma coordinate (scalar • first) vector) =
      _
  rw [map_smul, hFunction, fderiv_const_smul_field]
  simp only [gamma]
  change
    _ +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate (scalar • first) _ -
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate second
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate (scalar • first) vector) =
      _
  simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_apply,
    localLeviCivitaChristoffelBilinearMap_apply, smul_sub, smul_add]

private theorem localLeviCivitaRiemannVector_add_second
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second₁ second₂ vector : Vector4) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate first
        (second₁ + second₂) vector =
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second₁ vector +
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second₂ vector := by
  let gamma := fun current first second =>
    localLeviCivitaChristoffelApply period hPeriod metric patch current
      first second
  have hGamma₁ :
      DifferentiableAt Real (fun current => gamma current second₁ vector)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate second₁ vector
  have hGamma₂ :
      DifferentiableAt Real (fun current => gamma current second₂ vector)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate second₂ vector
  have hFunction :
      (fun current => gamma current (second₁ + second₂) vector) =
        (fun current => gamma current second₁ vector) +
          fun current => gamma current second₂ vector := by
    funext current
    change
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current (second₁ + second₂) vector =
        localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            current second₁ vector +
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            current second₂ vector
    simp only [map_add, LinearMap.add_apply]
  unfold localLeviCivitaRiemannVector
  change
    fderiv Real
          (fun current => gamma current (second₁ + second₂) vector)
          coordinate first -
        fderiv Real (fun current => gamma current first vector) coordinate
          (second₁ + second₂) +
      gamma coordinate first (gamma coordinate (second₁ + second₂) vector) -
      gamma coordinate (second₁ + second₂) (gamma coordinate first vector) =
      _
  rw [hFunction, fderiv_add hGamma₁ hGamma₂, map_add]
  simp only [add_apply, gamma]
  change
    _ +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate first
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate (second₁ + second₂) vector) -
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate (second₁ + second₂) _ =
      _
  simp only [map_add, LinearMap.add_apply,
    localLeviCivitaChristoffelBilinearMap_apply]
  abel

private theorem localLeviCivitaRiemannVector_smul_second
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : Vector4) (scalar : Real) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate first
        (scalar • second) vector =
      scalar •
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second vector := by
  let gamma := fun current first second =>
    localLeviCivitaChristoffelApply period hPeriod metric patch current
      first second
  have hFunction :
      (fun current => gamma current (scalar • second) vector) =
        scalar • fun current => gamma current second vector := by
    funext current
    change
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current (scalar • second) vector =
        scalar •
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            current second vector
    simp only [map_smul, LinearMap.smul_apply]
  unfold localLeviCivitaRiemannVector
  change
    fderiv Real
          (fun current => gamma current (scalar • second) vector)
          coordinate first -
        fderiv Real (fun current => gamma current first vector) coordinate
          (scalar • second) +
      gamma coordinate first (gamma coordinate (scalar • second) vector) -
      gamma coordinate (scalar • second) (gamma coordinate first vector) =
      _
  rw [hFunction, fderiv_const_smul_field, map_smul]
  simp only [Pi.smul_apply, smul_apply, gamma]
  change
    _ +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate first
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate (scalar • second) vector) -
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate (scalar • second) _ =
      _
  simp only [map_smul, LinearMap.smul_apply,
    localLeviCivitaChristoffelBilinearMap_apply, smul_sub, smul_add]

private theorem localLeviCivitaRiemannVector_add_vector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector₁ vector₂ : Vector4) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate first
        second (vector₁ + vector₂) =
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second vector₁ +
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second vector₂ := by
  let gamma := fun current first second =>
    localLeviCivitaChristoffelApply period hPeriod metric patch current
      first second
  have hSecond₁ :
      DifferentiableAt Real (fun current => gamma current second vector₁)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate second vector₁
  have hSecond₂ :
      DifferentiableAt Real (fun current => gamma current second vector₂)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate second vector₂
  have hFirst₁ :
      DifferentiableAt Real (fun current => gamma current first vector₁)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate first vector₁
  have hFirst₂ :
      DifferentiableAt Real (fun current => gamma current first vector₂)
        coordinate :=
    localChristoffelApply_fixed_differentiableAt period hPeriod metric patch
      coordinate first vector₂
  have hSecondFunction :
      (fun current => gamma current second (vector₁ + vector₂)) =
        (fun current => gamma current second vector₁) +
          fun current => gamma current second vector₂ := by
    funext current
    change
      (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
        current second) (vector₁ + vector₂) =
      (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current second) vector₁ +
        (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current second) vector₂
    rw [map_add]
  have hFirstFunction :
      (fun current => gamma current first (vector₁ + vector₂)) =
        (fun current => gamma current first vector₁) +
          fun current => gamma current first vector₂ := by
    funext current
    change
      (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
        current first) (vector₁ + vector₂) =
      (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current first) vector₁ +
        (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current first) vector₂
    rw [map_add]
  unfold localLeviCivitaRiemannVector
  change
    fderiv Real
          (fun current => gamma current second (vector₁ + vector₂))
          coordinate first -
        fderiv Real
          (fun current => gamma current first (vector₁ + vector₂))
          coordinate second +
      gamma coordinate first
          (gamma coordinate second (vector₁ + vector₂)) -
      gamma coordinate second
          (gamma coordinate first (vector₁ + vector₂)) =
      _
  rw [hSecondFunction, fderiv_add hSecond₁ hSecond₂, hFirstFunction,
    fderiv_add hFirst₁ hFirst₂]
  simp only [add_apply, gamma]
  change
    _ +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate first
          ((localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate second) (vector₁ + vector₂)) -
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate second
          ((localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate first) (vector₁ + vector₂)) =
      _
  simp only [map_add, localLeviCivitaChristoffelBilinearMap_apply]
  abel

private theorem localLeviCivitaRiemannVector_smul_vector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second vector : Vector4) (scalar : Real) :
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate first
        second (scalar • vector) =
      scalar •
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          first second vector := by
  let gamma := fun current first second =>
    localLeviCivitaChristoffelApply period hPeriod metric patch current
      first second
  have hSecondFunction :
      (fun current => gamma current second (scalar • vector)) =
        scalar • fun current => gamma current second vector := by
    funext current
    change
      (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
        current second) (scalar • vector) =
      scalar •
        (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current second) vector
    rw [map_smul]
  have hFirstFunction :
      (fun current => gamma current first (scalar • vector)) =
        scalar • fun current => gamma current first vector := by
    funext current
    change
      (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
        current first) (scalar • vector) =
      scalar •
        (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          current first) vector
    rw [map_smul]
  unfold localLeviCivitaRiemannVector
  change
    fderiv Real
          (fun current => gamma current second (scalar • vector))
          coordinate first -
        fderiv Real
          (fun current => gamma current first (scalar • vector))
          coordinate second +
      gamma coordinate first (gamma coordinate second (scalar • vector)) -
      gamma coordinate second (gamma coordinate first (scalar • vector)) =
      _
  rw [hSecondFunction, fderiv_const_smul_field, hFirstFunction,
    fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply, gamma]
  change
    _ +
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate first
          ((localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate second) (scalar • vector)) -
      localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
          coordinate second
          ((localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
            coordinate first) (scalar • vector)) =
      _
  simp only [map_smul, localLeviCivitaChristoffelBilinearMap_apply, smul_sub,
    smul_add]

/-- Curvature with the traced direction left free as an endomorphism. -/
def localRicciTraceEndomorphism
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) : Vector4 →ₗ[Real] Vector4 where
  toFun := fun traced =>
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate
      traced second first
  map_add' := fun traced₁ traced₂ =>
    localLeviCivitaRiemannVector_add_first period hPeriod metric patch
      coordinate traced₁ traced₂ second first
  map_smul' := fun scalar traced =>
    localLeviCivitaRiemannVector_smul_first period hPeriod metric patch
      coordinate traced second first scalar

/-- Ricci curvature evaluated on arbitrary coordinate vectors. -/
def localRicciCurvatureVector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) : Real :=
  LinearMap.trace Real Vector4
    (localRicciTraceEndomorphism period hPeriod metric patch coordinate
      first second)

private theorem localRicciCurvatureVector_add_first
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first₁ first₂ second : Vector4) :
    localRicciCurvatureVector period hPeriod metric patch coordinate
        (first₁ + first₂) second =
      localRicciCurvatureVector period hPeriod metric patch coordinate first₁
          second +
        localRicciCurvatureVector period hPeriod metric patch coordinate first₂
          second := by
  have hEndomorphism :
      localRicciTraceEndomorphism period hPeriod metric patch coordinate
          (first₁ + first₂) second =
        localRicciTraceEndomorphism period hPeriod metric patch coordinate
            first₁ second +
          localRicciTraceEndomorphism period hPeriod metric patch coordinate
            first₂ second := by
    apply LinearMap.ext
    intro traced
    change
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          traced second (first₁ + first₂) =
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
            traced second first₁ +
          localLeviCivitaRiemannVector period hPeriod metric patch coordinate
            traced second first₂
    exact localLeviCivitaRiemannVector_add_vector period hPeriod metric patch
      coordinate traced second first₁ first₂
  unfold localRicciCurvatureVector
  rw [hEndomorphism, map_add]

private theorem localRicciCurvatureVector_smul_first
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) (scalar : Real) :
    localRicciCurvatureVector period hPeriod metric patch coordinate
        (scalar • first) second =
      scalar •
        localRicciCurvatureVector period hPeriod metric patch coordinate first
          second := by
  have hEndomorphism :
      localRicciTraceEndomorphism period hPeriod metric patch coordinate
          (scalar • first) second =
        scalar •
          localRicciTraceEndomorphism period hPeriod metric patch coordinate
            first second := by
    apply LinearMap.ext
    intro traced
    change
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          traced second (scalar • first) =
        scalar •
          localLeviCivitaRiemannVector period hPeriod metric patch coordinate
            traced second first
    exact localLeviCivitaRiemannVector_smul_vector period hPeriod metric patch
      coordinate traced second first scalar
  unfold localRicciCurvatureVector
  rw [hEndomorphism, map_smul]

private theorem localRicciCurvatureVector_add_second
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second₁ second₂ : Vector4) :
    localRicciCurvatureVector period hPeriod metric patch coordinate first
        (second₁ + second₂) =
      localRicciCurvatureVector period hPeriod metric patch coordinate first
          second₁ +
        localRicciCurvatureVector period hPeriod metric patch coordinate first
          second₂ := by
  have hEndomorphism :
      localRicciTraceEndomorphism period hPeriod metric patch coordinate first
          (second₁ + second₂) =
        localRicciTraceEndomorphism period hPeriod metric patch coordinate
            first second₁ +
          localRicciTraceEndomorphism period hPeriod metric patch coordinate
            first second₂ := by
    apply LinearMap.ext
    intro traced
    change
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          traced (second₁ + second₂) first =
        localLeviCivitaRiemannVector period hPeriod metric patch coordinate
            traced second₁ first +
          localLeviCivitaRiemannVector period hPeriod metric patch coordinate
            traced second₂ first
    exact localLeviCivitaRiemannVector_add_second period hPeriod metric patch
      coordinate traced second₁ second₂ first
  unfold localRicciCurvatureVector
  rw [hEndomorphism, map_add]

private theorem localRicciCurvatureVector_smul_second
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) (scalar : Real) :
    localRicciCurvatureVector period hPeriod metric patch coordinate first
        (scalar • second) =
      scalar •
        localRicciCurvatureVector period hPeriod metric patch coordinate first
          second := by
  have hEndomorphism :
      localRicciTraceEndomorphism period hPeriod metric patch coordinate first
          (scalar • second) =
        scalar •
          localRicciTraceEndomorphism period hPeriod metric patch coordinate
            first second := by
    apply LinearMap.ext
    intro traced
    change
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
          traced (scalar • second) first =
        scalar •
          localLeviCivitaRiemannVector period hPeriod metric patch coordinate
            traced second first
    exact localLeviCivitaRiemannVector_smul_second period hPeriod metric patch
      coordinate traced second first scalar
  unfold localRicciCurvatureVector
  rw [hEndomorphism, map_smul]

/-- Ricci curvature as a bilinear form on arbitrary coordinate vectors. -/
def localRicciCurvatureBilinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : LinearMap.BilinForm Real Vector4 where
  toFun := fun first =>
    { toFun := fun second =>
        localRicciCurvatureVector period hPeriod metric patch coordinate first
          second
      map_add' := fun second₁ second₂ =>
        localRicciCurvatureVector_add_second period hPeriod metric patch
          coordinate first second₁ second₂
      map_smul' := fun scalar second =>
        localRicciCurvatureVector_smul_second period hPeriod metric patch
          coordinate first second scalar }
  map_add' := by
    intro first₁ first₂
    apply LinearMap.ext
    intro second
    exact localRicciCurvatureVector_add_first period hPeriod metric patch
      coordinate first₁ first₂ second
  map_smul' := by
    intro scalar first
    apply LinearMap.ext
    intro second
    exact localRicciCurvatureVector_smul_first period hPeriod metric patch
      coordinate first second scalar

/-- Matrix of the existing Ricci components. -/
def localRicciCurvatureMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Matrix4 :=
  fun first second =>
    localRicciCurvature period hPeriod metric patch coordinate first second

/-- On coordinate-basis vectors, the trace presentation is the existing
Ricci curvature component. -/
theorem localRicciCurvatureVector_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    localRicciCurvatureVector period hPeriod metric patch coordinate
        (Pi.single first 1) (Pi.single second 1) =
      localRicciCurvature period hPeriod metric patch coordinate first
        second := by
  unfold localRicciCurvatureVector localRicciCurvature
  rw [LinearMap.trace_eq_matrix_trace Real (Pi.basisFun Real Index4)]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply]
  apply Finset.sum_congr rfl
  intro contracted _
  change
    localLeviCivitaRiemannVector period hPeriod metric patch coordinate
        (Pi.single contracted 1) (Pi.single second 1)
        (Pi.single first 1) contracted =
      localRiemannCurvature period hPeriod metric patch coordinate
        contracted first contracted second
  rw [localLeviCivitaRiemannVector_basis]
  exact
    localLeviCivitaRiemannEndomorphism_basis_component period hPeriod metric
      patch coordinate contracted first contracted second

theorem localRicciCurvatureBilinearMap_toMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4)
        (localRicciCurvatureBilinearMap period hPeriod metric patch
          coordinate) =
      localRicciCurvatureMatrix period hPeriod metric patch coordinate := by
  ext first second
  rw [LinearMap.BilinForm.toMatrix_apply]
  simp only [Pi.basisFun_apply, localRicciCurvatureBilinearMap,
    localRicciCurvatureMatrix]
  change
    localRicciCurvatureVector period hPeriod metric patch coordinate
        (Pi.single first 1) (Pi.single second 1) =
      localRicciCurvature period hPeriod metric patch coordinate first second
  exact localRicciCurvatureVector_basis period hPeriod metric patch coordinate
    first second

/-- Ricci curvature on arbitrary vectors is natural under the fixed
holonomic transition. -/
theorem localRicciCurvatureVector_natural
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Vector4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    localRicciCurvatureVector period hPeriod metric firstPatch firstCoordinate
        first second =
      localRicciCurvatureVector period hPeriod metric secondPatch
        secondCoordinate
        (fderiv Real transition firstCoordinate first)
        (fderiv Real transition firstCoordinate second) := by
  dsimp only
  let transition :=
    holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
      firstCoordinate secondCoordinate samePoint
  let equivalence :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint).toLinearEquiv
  let firstEndomorphism :=
    localRicciTraceEndomorphism period hPeriod metric firstPatch
      firstCoordinate first second
  let secondEndomorphism :=
    localRicciTraceEndomorphism period hPeriod metric secondPatch
      secondCoordinate (equivalence first) (equivalence second)
  have hConjugate :
      secondEndomorphism = equivalence.conj firstEndomorphism := by
    apply LinearMap.ext
    intro traced
    change
      localLeviCivitaRiemannVector period hPeriod metric secondPatch
          secondCoordinate traced (equivalence second) (equivalence first) =
        equivalence
          (localLeviCivitaRiemannVector period hPeriod metric firstPatch
            firstCoordinate (equivalence.symm traced) second first)
    have hNaturality :=
      localLeviCivitaRiemannVector_natural period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
        (equivalence.symm traced) second first
    dsimp only at hNaturality
    rw [← holonomicCoordinateTransitionLinearEquivAt_coe] at hNaturality
    change
      equivalence
          (localLeviCivitaRiemannVector period hPeriod metric firstPatch
            firstCoordinate (equivalence.symm traced) second first) =
        localLeviCivitaRiemannVector period hPeriod metric secondPatch
          secondCoordinate (equivalence (equivalence.symm traced))
          (equivalence second) (equivalence first)
      at hNaturality
    rw [equivalence.apply_symm_apply] at hNaturality
    exact hNaturality.symm
  unfold localRicciCurvatureVector
  rw [← holonomicCoordinateTransitionLinearEquivAt_coe]
  change
    LinearMap.trace Real Vector4 firstEndomorphism =
      LinearMap.trace Real Vector4 secondEndomorphism
  rw [hConjugate]
  exact (LinearMap.trace_conj' firstEndomorphism equivalence).symm

/-- Ricci components transform by the same Jacobian congruence as the
covariant metric. -/
theorem localRicciCurvatureMatrix_transition_congruence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localRicciCurvatureMatrix period hPeriod metric firstPatch
        firstCoordinate =
      (holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint).transpose *
        localRicciCurvatureMatrix period hPeriod metric secondPatch
          secondCoordinate *
        holonomicCoordinateTransitionMatrixAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint := by
  let firstForm :=
    localRicciCurvatureBilinearMap period hPeriod metric firstPatch
      firstCoordinate
  let secondForm :=
    localRicciCurvatureBilinearMap period hPeriod metric secondPatch
      secondCoordinate
  let transitionLinear : Vector4 →ₗ[Real] Vector4 :=
    (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint :
        Vector4 →L[Real] Vector4).toLinearMap
  have hForms :
      firstForm = secondForm.comp transitionLinear transitionLinear := by
    apply LinearMap.ext
    intro first
    apply LinearMap.ext
    intro second
    change
      localRicciCurvatureVector period hPeriod metric firstPatch
          firstCoordinate first second =
        localRicciCurvatureVector period hPeriod metric secondPatch
          secondCoordinate (transitionLinear first) (transitionLinear second)
    have hNaturality :=
      localRicciCurvatureVector_natural period hPeriod metric firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint first second
    dsimp only at hNaturality
    rw [← holonomicCoordinateTransitionLinearEquivAt_coe] at hNaturality
    exact hNaturality
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_comp
      (b := Pi.basisFun Real Index4)
      (c := Pi.basisFun Real Index4) secondForm transitionLinear
      transitionLinear
  calc
    localRicciCurvatureMatrix period hPeriod metric firstPatch
        firstCoordinate =
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4) firstForm := by
        simpa only [firstForm] using
          (localRicciCurvatureBilinearMap_toMatrix period hPeriod metric
            firstPatch firstCoordinate).symm
    _ =
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4)
        (secondForm.comp transitionLinear transitionLinear) := by
          rw [hForms]
    _ =
      (LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transitionLinear).transpose *
        LinearMap.BilinForm.toMatrix (Pi.basisFun Real Index4) secondForm *
        LinearMap.toMatrix (Pi.basisFun Real Index4)
          (Pi.basisFun Real Index4) transitionLinear :=
      hCongruence
    _ = _ := by
      have hSecondMatrix :=
        localRicciCurvatureBilinearMap_toMatrix period hPeriod metric
          secondPatch secondCoordinate
      rw [hSecondMatrix]
      rfl

def matrixEntryContraction (first second : Matrix4) : Real :=
  ∑ i : Index4, ∑ j : Index4, first i j * second i j

private theorem matrixEntryContraction_eq_trace
    (first second : Matrix4) :
    matrixEntryContraction first second =
      Matrix.trace (first * second.transpose) := by
  unfold matrixEntryContraction Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

/-- Inverse-metric contraction is invariant when the metric and an arbitrary
covariant matrix transform by the same invertible congruence. -/
theorem matrixEntryContraction_congruence
    (transition metric covariant : Matrix4)
    (hTransition : IsUnit transition) :
    matrixEntryContraction
        (transition.transpose * metric * transition)⁻¹
        (transition.transpose * covariant * transition) =
      matrixEntryContraction metric⁻¹ covariant := by
  rw [matrixEntryContraction_eq_trace,
    matrixEntryContraction_eq_trace]
  have hTransposeDet : IsUnit transition.transpose.det :=
    Matrix.isUnit_det_transpose transition
      ((Matrix.isUnit_iff_isUnit_det transition).mp hTransition)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    Matrix.trace
        ((transition.transpose * metric * transition)⁻¹ *
          (transition.transpose * (covariant.transpose * transition))) =
      Matrix.trace
        (transition⁻¹ * (metric⁻¹ * covariant.transpose) * transition) := by
        congr 1
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
        calc
          (transition⁻¹ * (metric⁻¹ * transition.transpose⁻¹)) *
                (transition.transpose *
                  (covariant.transpose * transition)) =
              transition⁻¹ *
                (metric⁻¹ *
                  (transition.transpose⁻¹ *
                    (transition.transpose *
                      (covariant.transpose * transition)))) := by
                        noncomm_ring
          _ =
              transition⁻¹ *
                (metric⁻¹ * (covariant.transpose * transition)) := by
            rw [Matrix.nonsing_inv_mul_cancel_left transition.transpose
              (covariant.transpose * transition) hTransposeDet]
          _ =
              transition⁻¹ * (metric⁻¹ * covariant.transpose) *
                transition := by
            noncomm_ring
    _ = Matrix.trace (metric⁻¹ * covariant.transpose) :=
      Matrix.trace_conj' hTransition (metric⁻¹ * covariant.transpose)

/-- The intrinsic local scalar curvature is independent of the selected
canonical holonomic chart. -/
theorem localScalarCurvature_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    localScalarCurvature period hPeriod metric firstPatch firstCoordinate =
      localScalarCurvature period hPeriod metric secondPatch
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
  have hRicci :
      localRicciCurvatureMatrix period hPeriod metric firstPatch
          firstCoordinate =
        transition.transpose *
          localRicciCurvatureMatrix period hPeriod metric secondPatch
            secondCoordinate *
          transition := by
    simpa only [transition] using
      localRicciCurvatureMatrix_transition_congruence period hPeriod metric
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint
  unfold localScalarCurvature
  change
    matrixEntryContraction
        (localMetricMatrix period hPeriod metric firstPatch
          firstCoordinate)⁻¹
        (localRicciCurvatureMatrix period hPeriod metric firstPatch
          firstCoordinate) =
      matrixEntryContraction
        (localMetricMatrix period hPeriod metric secondPatch
          secondCoordinate)⁻¹
        (localRicciCurvatureMatrix period hPeriod metric secondPatch
          secondCoordinate)
  rw [hMetric, hRicci]
  exact matrixEntryContraction_congruence transition
    (localMetricMatrix period hPeriod metric secondPatch secondCoordinate)
    (localRicciCurvatureMatrix period hPeriod metric secondPatch
      secondCoordinate) hTransition

end

end P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
end JanusFormal
