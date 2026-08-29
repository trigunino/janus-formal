import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D

/-!
# Homothetic Einstein--Hilbert Hessian

Positive constant conformal rescalings preserve the Levi--Civita connection
and Ricci tensor, while scalar curvature scales inversely.  Combined with the
four-dimensional volume ratio, this gives an exact one-dimensional
Einstein--Hilbert action and its first two derivatives along a positive
exponential homothety.

This is a genuine metric line and includes the curvature variation.  It is
not a Frechet Hessian on the full space of smooth Lorentz metrics and it does
not cover nonconstant conformal factors.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusHomotheticEinsteinHilbertHessian4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Frobenius Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Coord4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Vector4

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

/-! ## Constant positive conformal rescaling -/

def constantHomotheticScaleField
    (scale : Real) : SmoothScalarField period hPeriod where
  toFun := fun _ => scale
  contMDiff_toFun := contMDiff_const

@[simp]
theorem constantHomotheticScaleField_apply
    (scale : Real) (point : EffectiveQuotient period hPeriod) :
    constantHomotheticScaleField period hPeriod scale point = scale :=
  rfl

def homotheticLorentzMetric
    (scale : Real) (hScale : 0 < scale) :
    SmoothGeneralLorentzMetric period hPeriod :=
  conformalSmoothGeneralLorentzMetric period hPeriod
    (constantHomotheticScaleField period hPeriod scale)
    (fun _ => hScale)

theorem localMetricMatrix_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) :
    localMetricMatrix period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      scale •
        localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate := by
  exact localMetricMatrix_conformal period hPeriod
    (constantHomotheticScaleField period hPeriod scale)
    (fun _ => hScale) patch coordinate

theorem localMetricCoefficient_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (first second : Fin 4) :
    localMetricCoefficient period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch first second coordinate =
      scale *
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first second coordinate := by
  change
    localMetricMatrix period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate first second =
      scale *
        localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate first second
  rw [localMetricMatrix_homothetic]
  rfl

theorem localMetricDerivative_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (derivative first second : Fin 4) :
    localMetricDerivative period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate derivative first second =
      scale *
        localMetricDerivative period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate derivative first second := by
  unfold localMetricDerivative
  rw [show
    localMetricCoefficient period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch first second =
      fun current =>
        scale *
          localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch first second current by
    funext current
    exact localMetricCoefficient_homothetic period hPeriod scale hScale patch
      current first second]
  rw [fderiv_const_mul
    ((localMetricCoefficient_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch first second).differentiable (by simp)).differentiableAt scale]
  rfl

theorem localMetricInverse_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) :
    (localMetricMatrix period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate)⁻¹ =
      scale⁻¹ •
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ := by
  letI : Invertible scale := invertibleOfNonzero (ne_of_gt hScale)
  rw [localMetricMatrix_homothetic]
  rw [Matrix.inv_smul]
  · rw [invOf_eq_inv]
  · exact isUnit_iff_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

theorem localLeviCivitaChristoffel_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (upper first second : Fin 4) :
    localLeviCivitaChristoffel period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate upper first second =
      localLeviCivitaChristoffel period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate upper first second := by
  unfold localLeviCivitaChristoffel leviCivitaChristoffel
  apply Finset.sum_congr rfl
  intro contracted _
  simp only [localFixedSignMetric]
  rw [localMetricInverse_homothetic,
    localMetricDerivative_homothetic,
    localMetricDerivative_homothetic,
    localMetricDerivative_homothetic]
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hScale]

theorem localChristoffelDerivative_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4)
    (derivative upper first second : Fin 4) :
    localChristoffelDerivative period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate derivative upper first second =
      localChristoffelDerivative period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate derivative upper first second := by
  unfold localChristoffelDerivative
  rw [show
    (fun current =>
      localLeviCivitaChristoffel period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch current upper first second) =
      fun current =>
        localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch current upper first second by
    funext current
    exact localLeviCivitaChristoffel_homothetic period hPeriod scale hScale
      patch current upper first second]

theorem localRiemannCurvature_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4)
    (upper lower first second : Fin 4) :
    localRiemannCurvature period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate upper lower first second =
      localRiemannCurvature period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate upper lower first second := by
  unfold localRiemannCurvature
  simp only [localChristoffelDerivative_homothetic,
    localLeviCivitaChristoffel_homothetic]

theorem localRicciCurvature_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (first second : Fin 4) :
    localRicciCurvature period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate first second =
      localRicciCurvature period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate first second := by
  unfold localRicciCurvature
  simp only [localRiemannCurvature_homothetic]

theorem localScalarCurvature_homothetic
    (scale : Real) (hScale : 0 < scale)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) :
    localScalarCurvature period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      scale⁻¹ *
        localScalarCurvature period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate := by
  unfold localScalarCurvature
  simp only [localMetricInverse_homothetic,
    localRicciCurvature_homothetic, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem globalScalarCurvature_homothetic
    (scale : Real) (hScale : 0 < scale)
    (point : EffectiveQuotient period hPeriod) :
    globalScalarCurvature period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale) point =
      scale⁻¹ *
        globalScalarCurvature period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) point := by
  let witness := selectedScalarCurvatureChart period hPeriod point
  change
    localScalarCurvature period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        witness.patch witness.coordinate =
      scale⁻¹ *
        localScalarCurvature period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          witness.patch witness.coordinate
  exact localScalarCurvature_homothetic period hPeriod scale hScale
    witness.patch witness.coordinate

theorem globalMetricVolumeRatio_homothetic
    (scale : Real) (hScale : 0 < scale)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale) point =
      scale ^ 2 := by
  exact globalMetricVolumeRatio_conformal period hPeriod
    (constantHomotheticScaleField period hPeriod scale)
    (fun _ => hScale) point

theorem frameFreeEinsteinHilbertDensity_homothetic
    (scale : Real) (hScale : 0 < scale)
    (couplings : EinsteinHilbertCouplings)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeEinsteinHilbertDensity period hPeriod
        (homotheticLorentzMetric period hPeriod scale hScale)
        couplings point =
      (1 / (2 * couplings.gravitationalCoupling)) *
        (scale⁻¹ *
            globalScalarCurvature period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
          2 * couplings.cosmologicalConstant) := by
  change
    (1 / (2 * couplings.gravitationalCoupling)) *
        (globalScalarCurvature period hPeriod
            (homotheticLorentzMetric period hPeriod scale hScale) point -
          2 * couplings.cosmologicalConstant) =
      _
  rw [globalScalarCurvature_homothetic]

/-- Exact fixed-reference Einstein--Hilbert density under a positive
homothety. -/
theorem relativeFrameFreeEinsteinHilbertDensity_homothetic
    (scale : Real) (hScale : 0 < scale)
    (couplings : EinsteinHilbertCouplings)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
          (homotheticLorentzMetric period hPeriod scale hScale) point *
        frameFreeEinsteinHilbertDensity period hPeriod
          (homotheticLorentzMetric period hPeriod scale hScale)
          couplings point =
      (1 / (2 * couplings.gravitationalCoupling)) *
        (scale *
            globalScalarCurvature period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
          2 * couplings.cosmologicalConstant * scale ^ 2) := by
  rw [globalMetricVolumeRatio_homothetic,
    frameFreeEinsteinHilbertDensity_homothetic]
  field_simp [ne_of_gt hScale]

/-! ## Exact affine homothetic action -/

def intrinsicTotalScalarCurvature : Real :=
  ∫ point,
    globalScalarCurvature period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

def intrinsicTotalLorentzVolume : Real :=
  ∫ _point : EffectiveQuotient period hPeriod, (1 : Real)
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

/-- Polynomial continuation of the positive homothetic
Einstein--Hilbert action to the full affine scale line. -/
def homotheticEinsteinHilbertReducedAction
    (couplings : EinsteinHilbertCouplings) (scale : Real) : Real :=
  (1 / (2 * couplings.gravitationalCoupling)) *
    (scale * intrinsicTotalScalarCurvature period hPeriod -
      scale ^ 2 *
        (2 * couplings.cosmologicalConstant *
          intrinsicTotalLorentzVolume period hPeriod))

def homotheticEinsteinHilbertAction
    (scale : Real) (hScale : 0 < scale)
    (couplings : EinsteinHilbertCouplings) : Real :=
  generalLorentzFrameFreeEinsteinHilbertAction period hPeriod
    (homotheticLorentzMetric period hPeriod scale hScale) couplings

theorem homotheticEinsteinHilbertAction_eq_reduced
    (scale : Real) (hScale : 0 < scale)
    (couplings : EinsteinHilbertCouplings) :
    homotheticEinsteinHilbertAction period hPeriod scale hScale couplings =
      homotheticEinsteinHilbertReducedAction
        period hPeriod couplings scale := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  have hCurvature : Integrable
      (fun point =>
        globalScalarCurvature period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    (globalSmoothScalarCurvature period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)).contMDiff_toFun
      |>.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hScaledCurvature :=
    hCurvature.const_mul scale
  have hConstant : Integrable
      (fun _point : EffectiveQuotient period hPeriod =>
        2 * couplings.cosmologicalConstant * scale ^ 2)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    integrable_const _
  unfold homotheticEinsteinHilbertAction
  rw [generalLorentzFrameFreeEinsteinHilbertAction_eq_reference]
  calc
    (∫ point,
        globalMetricVolumeRatio period hPeriod
              (homotheticLorentzMetric period hPeriod scale hScale) point *
            frameFreeEinsteinHilbertDensity period hPeriod
              (homotheticLorentzMetric period hPeriod scale hScale)
              couplings point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        ∫ point,
          (1 / (2 * couplings.gravitationalCoupling)) *
            (scale *
                globalScalarCurvature period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
              2 * couplings.cosmologicalConstant * scale ^ 2)
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact relativeFrameFreeEinsteinHilbertDensity_homothetic
        period hPeriod scale hScale couplings point
    _ = (1 / (2 * couplings.gravitationalCoupling)) *
        ∫ point,
          (scale *
              globalScalarCurvature period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
            2 * couplings.cosmologicalConstant * scale ^ 2)
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      rw [integral_const_mul]
    _ = (1 / (2 * couplings.gravitationalCoupling)) *
        ((∫ point,
            scale *
              globalScalarCurvature period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) -
          ∫ _point : EffectiveQuotient period hPeriod,
            2 * couplings.cosmologicalConstant * scale ^ 2
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
      rw [integral_sub hScaledCurvature hConstant]
    _ = homotheticEinsteinHilbertReducedAction
        period hPeriod couplings scale := by
      rw [integral_const_mul]
      rw [show
        (fun _point : EffectiveQuotient period hPeriod =>
          2 * couplings.cosmologicalConstant * scale ^ 2) =
          fun _point =>
            (2 * couplings.cosmologicalConstant * scale ^ 2) * (1 : Real) by
        funext point
        ring]
      rw [integral_const_mul]
      unfold homotheticEinsteinHilbertReducedAction
        intrinsicTotalScalarCurvature intrinsicTotalLorentzVolume
      ring

def homotheticEinsteinHilbertAffineFirstVariation
    (couplings : EinsteinHilbertCouplings)
    (scale tangent : Real) : Real :=
  (1 / (2 * couplings.gravitationalCoupling)) *
    (tangent * intrinsicTotalScalarCurvature period hPeriod -
      (2 * tangent * scale) *
        (2 * couplings.cosmologicalConstant *
          intrinsicTotalLorentzVolume period hPeriod))

/-- The genuine symmetric Hessian in the one-dimensional affine homothety
coordinate. -/
def homotheticEinsteinHilbertAffineHessian
    (couplings : EinsteinHilbertCouplings)
    (first second : Real) : Real :=
  (1 / (2 * couplings.gravitationalCoupling)) *
    (-(2 * first * second) *
      (2 * couplings.cosmologicalConstant *
        intrinsicTotalLorentzVolume period hPeriod))

theorem homotheticEinsteinHilbertAffineHessian_symmetric
    (couplings : EinsteinHilbertCouplings)
    (first second : Real) :
    homotheticEinsteinHilbertAffineHessian
        period hPeriod couplings first second =
      homotheticEinsteinHilbertAffineHessian
        period hPeriod couplings second first := by
  unfold homotheticEinsteinHilbertAffineHessian
  ring

theorem homotheticEinsteinHilbertReducedAction_hasDerivAt
    (couplings : EinsteinHilbertCouplings) (scale : Real) :
    HasDerivAt
      (homotheticEinsteinHilbertReducedAction period hPeriod couplings)
      (homotheticEinsteinHilbertAffineFirstVariation
        period hPeriod couplings scale 1)
      scale := by
  have hLinear :=
    (hasDerivAt_id (x := scale)).mul_const
      (intrinsicTotalScalarCurvature period hPeriod)
  have hQuadratic :=
    ((hasDerivAt_id (x := scale)).pow 2).mul_const
      (2 * couplings.cosmologicalConstant *
        intrinsicTotalLorentzVolume period hPeriod)
  have hDerivative :=
    (hLinear.sub hQuadratic).const_mul
      (1 / (2 * couplings.gravitationalCoupling))
  unfold homotheticEinsteinHilbertReducedAction
    homotheticEinsteinHilbertAffineFirstVariation
  simpa only [id_eq, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSubDiff, pow_one, one_mul, mul_one] using hDerivative

theorem homotheticEinsteinHilbertAffineLine_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (scale tangent : Real) :
    HasDerivAt
      (fun parameter =>
        homotheticEinsteinHilbertReducedAction period hPeriod couplings
          (scale + parameter * tangent))
      (homotheticEinsteinHilbertAffineFirstVariation
        period hPeriod couplings scale tangent)
      0 := by
  have hScaleRaw :=
    ((hasDerivAt_id (x := 0)).mul_const tangent).const_add scale
  have hScale :
      HasDerivAt (fun parameter => scale + parameter * tangent) tangent 0 := by
    exact hScaleRaw.congr_deriv (by ring)
  have hComposite :=
    (homotheticEinsteinHilbertReducedAction_hasDerivAt
      period hPeriod couplings (scale + 0 * tangent)).comp 0 hScale
  refine (hComposite.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun _ => rfl
  · simp only [zero_mul, add_zero]
    unfold homotheticEinsteinHilbertAffineFirstVariation
    ring

theorem homotheticEinsteinHilbertAffineFirstVariation_hasDerivAt_scale
    (couplings : EinsteinHilbertCouplings)
    (scale tangent : Real) :
    HasDerivAt
      (fun varied =>
        homotheticEinsteinHilbertAffineFirstVariation
          period hPeriod couplings varied tangent)
      (homotheticEinsteinHilbertAffineHessian
        period hPeriod couplings tangent 1)
      scale := by
  unfold homotheticEinsteinHilbertAffineFirstVariation
    homotheticEinsteinHilbertAffineHessian
  have hVariable :=
    ((hasDerivAt_id (x := scale)).const_mul (2 * tangent)).mul_const
      (2 * couplings.cosmologicalConstant *
        intrinsicTotalLorentzVolume period hPeriod)
  have hDerivative :=
    ((hasDerivAt_const (x := scale)
      (tangent * intrinsicTotalScalarCurvature period hPeriod)).sub
        hVariable).const_mul
          (1 / (2 * couplings.gravitationalCoupling))
  have hDerivative' :
      HasDerivAt
        (fun varied =>
          (1 / (2 * couplings.gravitationalCoupling)) *
            (tangent * intrinsicTotalScalarCurvature period hPeriod -
              2 * tangent * varied *
                (2 * couplings.cosmologicalConstant *
                  intrinsicTotalLorentzVolume period hPeriod)))
        ((1 / (2 * couplings.gravitationalCoupling)) *
          -(2 * tangent *
            (2 * couplings.cosmologicalConstant *
              intrinsicTotalLorentzVolume period hPeriod)))
        scale := by
    simpa only [id_eq, Pi.sub_apply, one_mul, mul_one, zero_sub] using hDerivative
  exact hDerivative'.congr_deriv (by ring)

theorem homotheticEinsteinHilbertAffineFirstVariation_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (scale first second : Real) :
    HasDerivAt
      (fun parameter =>
        homotheticEinsteinHilbertAffineFirstVariation period hPeriod couplings
          (scale + parameter * second) first)
      (homotheticEinsteinHilbertAffineHessian
        period hPeriod couplings first second)
      0 := by
  have hScaleRaw :=
    ((hasDerivAt_id (x := 0)).mul_const second).const_add scale
  have hScale :
      HasDerivAt (fun parameter => scale + parameter * second) second 0 := by
    exact hScaleRaw.congr_deriv (by ring)
  have hComposite :=
    (homotheticEinsteinHilbertAffineFirstVariation_hasDerivAt_scale
      period hPeriod couplings (scale + 0 * second) first).comp 0 hScale
  refine (hComposite.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun _ => rfl
  · unfold homotheticEinsteinHilbertAffineHessian
    ring

/-! ## Positive exponential homothety -/

def positiveHomotheticScaleCurve
    (direction parameter : Real) : Real :=
  Real.exp (parameter * direction)

theorem positiveHomotheticScaleCurve_pos
    (direction parameter : Real) :
    0 < positiveHomotheticScaleCurve direction parameter :=
  Real.exp_pos _

theorem positiveHomotheticScaleCurve_hasDerivAt
    (direction parameter : Real) :
    HasDerivAt
      (positiveHomotheticScaleCurve direction)
      (direction * positiveHomotheticScaleCurve direction parameter)
      parameter := by
  unfold positiveHomotheticScaleCurve
  have hExponential :=
    ((hasDerivAt_id (x := parameter)).mul_const direction).exp
  apply hExponential.congr_deriv
  simpa only [id_eq, one_mul] using
    (mul_comm (Real.exp (parameter * direction)) direction)

def homotheticLorentzMetricCurve
    (direction parameter : Real) :
    SmoothGeneralLorentzMetric period hPeriod :=
  homotheticLorentzMetric period hPeriod
    (positiveHomotheticScaleCurve direction parameter)
    (positiveHomotheticScaleCurve_pos direction parameter)

def homotheticEinsteinHilbertActionCurve
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) : Real :=
  homotheticEinsteinHilbertAction period hPeriod
    (positiveHomotheticScaleCurve direction parameter)
    (positiveHomotheticScaleCurve_pos direction parameter) couplings

def homotheticEinsteinHilbertActionFirstDerivativeCurve
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) : Real :=
  let scale := positiveHomotheticScaleCurve direction parameter
  let totalCurvature := intrinsicTotalScalarCurvature period hPeriod
  let volume := intrinsicTotalLorentzVolume period hPeriod
  let cosmologicalWeight :=
    2 * couplings.cosmologicalConstant * volume
  (1 / (2 * couplings.gravitationalCoupling)) *
    ((direction * scale) * totalCurvature -
      ((2 * direction) * scale ^ 2) * cosmologicalWeight)

def homotheticEinsteinHilbertActionSecondDerivativeCurve
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) : Real :=
  let scale := positiveHomotheticScaleCurve direction parameter
  let totalCurvature := intrinsicTotalScalarCurvature period hPeriod
  let volume := intrinsicTotalLorentzVolume period hPeriod
  let cosmologicalWeight :=
    2 * couplings.cosmologicalConstant * volume
  (1 / (2 * couplings.gravitationalCoupling)) *
    ((direction ^ 2 * scale) * totalCurvature -
      ((4 * direction ^ 2) * scale ^ 2) * cosmologicalWeight)

theorem homotheticEinsteinHilbertActionCurve_eq_reduced
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) :
    homotheticEinsteinHilbertActionCurve
        period hPeriod couplings direction parameter =
      homotheticEinsteinHilbertReducedAction period hPeriod couplings
        (positiveHomotheticScaleCurve direction parameter) := by
  exact homotheticEinsteinHilbertAction_eq_reduced period hPeriod
    (positiveHomotheticScaleCurve direction parameter)
    (positiveHomotheticScaleCurve_pos direction parameter) couplings

theorem homotheticEinsteinHilbertActionFirstDerivativeCurve_eq_affine
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) :
    homotheticEinsteinHilbertActionFirstDerivativeCurve
        period hPeriod couplings direction parameter =
      homotheticEinsteinHilbertAffineFirstVariation period hPeriod couplings
        (positiveHomotheticScaleCurve direction parameter)
        (direction * positiveHomotheticScaleCurve direction parameter) := by
  unfold homotheticEinsteinHilbertActionFirstDerivativeCurve
    homotheticEinsteinHilbertAffineFirstVariation
  ring

theorem homotheticEinsteinHilbertActionSecondDerivativeCurve_eq_hessian_add_acceleration
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) :
    homotheticEinsteinHilbertActionSecondDerivativeCurve
        period hPeriod couplings direction parameter =
      homotheticEinsteinHilbertAffineHessian period hPeriod couplings
          (direction * positiveHomotheticScaleCurve direction parameter)
          (direction * positiveHomotheticScaleCurve direction parameter) +
        homotheticEinsteinHilbertAffineFirstVariation period hPeriod couplings
          (positiveHomotheticScaleCurve direction parameter)
          (direction ^ 2 *
            positiveHomotheticScaleCurve direction parameter) := by
  unfold homotheticEinsteinHilbertActionSecondDerivativeCurve
    homotheticEinsteinHilbertAffineHessian
    homotheticEinsteinHilbertAffineFirstVariation
  ring

theorem homotheticEinsteinHilbertActionCurve_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) :
    HasDerivAt
      (homotheticEinsteinHilbertActionCurve
        period hPeriod couplings direction)
      (homotheticEinsteinHilbertActionFirstDerivativeCurve
        period hPeriod couplings direction parameter)
      parameter := by
  have hScale :=
    positiveHomotheticScaleCurve_hasDerivAt direction parameter
  have hOuter :=
    homotheticEinsteinHilbertReducedAction_hasDerivAt period hPeriod couplings
      (positiveHomotheticScaleCurve direction parameter)
  have hComposite := hOuter.comp parameter hScale
  refine (hComposite.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun varied =>
      homotheticEinsteinHilbertActionCurve_eq_reduced
        period hPeriod couplings direction varied
  · rw [homotheticEinsteinHilbertActionFirstDerivativeCurve_eq_affine]
    unfold homotheticEinsteinHilbertAffineFirstVariation
    ring

theorem homotheticEinsteinHilbertActionFirstDerivativeCurve_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction parameter : Real) :
    HasDerivAt
      (homotheticEinsteinHilbertActionFirstDerivativeCurve
        period hPeriod couplings direction)
      (homotheticEinsteinHilbertActionSecondDerivativeCurve
        period hPeriod couplings direction parameter)
      parameter := by
  have hScale :=
    positiveHomotheticScaleCurve_hasDerivAt direction parameter
  have hCurvature :=
    ((hScale.const_mul direction).mul_const
      (intrinsicTotalScalarCurvature period hPeriod))
  have hCosmological :=
    (((hScale.pow 2).const_mul (2 * direction)).mul_const
      (2 * couplings.cosmologicalConstant *
        intrinsicTotalLorentzVolume period hPeriod))
  have hDerivative :=
    (hCurvature.sub hCosmological).const_mul
      (1 / (2 * couplings.gravitationalCoupling))
  unfold homotheticEinsteinHilbertActionFirstDerivativeCurve
    homotheticEinsteinHilbertActionSecondDerivativeCurve
  refine (hDerivative.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun varied => by
      simp only [Pi.sub_apply, Pi.pow_apply]
  · simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
    ring

theorem homotheticEinsteinHilbertActionCurve_contDiff_infinity
    (couplings : EinsteinHilbertCouplings)
    (direction : Real) :
    ContDiff Real ∞
      (homotheticEinsteinHilbertActionCurve
        period hPeriod couplings direction) := by
  rw [show
    homotheticEinsteinHilbertActionCurve
        period hPeriod couplings direction =
      fun parameter =>
        homotheticEinsteinHilbertReducedAction period hPeriod couplings
          (positiveHomotheticScaleCurve direction parameter) by
    funext parameter
    exact homotheticEinsteinHilbertActionCurve_eq_reduced
      period hPeriod couplings direction parameter]
  unfold homotheticEinsteinHilbertReducedAction
    positiveHomotheticScaleCurve
  fun_prop

theorem homotheticEinsteinHilbertActionCurve_contDiff_two
    (couplings : EinsteinHilbertCouplings)
    (direction : Real) :
    ContDiff Real 2
      (homotheticEinsteinHilbertActionCurve
        period hPeriod couplings direction) :=
  (homotheticEinsteinHilbertActionCurve_contDiff_infinity
    period hPeriod couplings direction).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem homotheticEinsteinHilbertActionSecondDerivativeCurve_zero
    (couplings : EinsteinHilbertCouplings)
    (direction : Real) :
    homotheticEinsteinHilbertActionSecondDerivativeCurve
        period hPeriod couplings direction 0 =
      direction ^ 2 * (1 / (2 * couplings.gravitationalCoupling)) *
        (intrinsicTotalScalarCurvature period hPeriod -
          8 * couplings.cosmologicalConstant *
            intrinsicTotalLorentzVolume period hPeriod) := by
  unfold homotheticEinsteinHilbertActionSecondDerivativeCurve
    positiveHomotheticScaleCurve
  rw [zero_mul, Real.exp_zero]
  ring

end

end P0EFTJanusMappingTorusHomotheticEinsteinHilbertHessian4D
end JanusFormal
