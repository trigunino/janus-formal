import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

/-! # Global smooth Einstein coefficients in the regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Filter
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def localRegularFrameRicciCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Fin 4) (coordinate : CoordinateVector) : Real :=
  localRicciCurvatureBilinearMap period hPeriod metric.metric patch coordinate
    (pulledRegularFrameVector period hPeriod metric patch first coordinate)
    (pulledRegularFrameVector period hPeriod metric patch second coordinate)

private theorem localRegularFrameRicciCoefficient_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Fin 4) :
    ContDiff Real ∞
      (localRegularFrameRicciCoefficient period hPeriod metric patch first
        second) := by
  let left := pulledRegularFrameVector period hPeriod metric patch first
  let right := pulledRegularFrameVector period hPeriod metric patch second
  have hLeft : ContDiff Real ∞ left :=
    pulledRegularFrameVector_contDiff period hPeriod metric patch first
  have hRight : ContDiff Real ∞ right :=
    pulledRegularFrameVector_contDiff period hPeriod metric patch second
  have hExpansion :
      localRegularFrameRicciCoefficient period hPeriod metric patch first
          second =
        fun coordinate =>
          ∑ row : Fin 4, ∑ column : Fin 4,
            left coordinate row *
                localRicciCurvature period hPeriod metric.metric patch
                  coordinate row column *
              right coordinate column := by
    funext coordinate
    change
      localRicciCurvatureBilinearMap period hPeriod metric.metric patch
          coordinate (left coordinate) (right coordinate) = _
    calc
      _ = Matrix.toBilin'
          (localRicciCurvatureMatrix period hPeriod metric.metric patch
            coordinate) (left coordinate) (right coordinate) := by
        rw [← localRicciCurvatureBilinearMap_toMatrix period hPeriod
          metric.metric patch coordinate]
        rw [LinearMap.BilinForm.toMatrix_basisFun,
          Matrix.toBilin'_toMatrix']
      _ = _ := Matrix.toBilin'_apply _ _ _
  rw [hExpansion]
  apply ContDiff.sum
  intro row _
  apply ContDiff.sum
  intro column _
  exact (((contDiff_pi.mp hLeft) row).mul
    (localRicciCurvature_contDiff period hPeriod metric.metric patch row
      column)).mul ((contDiff_pi.mp hRight) column)

/-- The regular-frame coefficients of the intrinsic Ricci tensor are smooth
global scalar fields, rather than merely continuous completed coefficients. -/
theorem regularGeneralMetricC0Ricci_zero_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (regularGeneralMetricC0Ricci period hPeriod metric 0 first second) := by
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let localDiffeomorph := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hRepresentative :
      ContMDiffAt coverModelWithCorners (modelWithCornersSelf Real Real) ∞
        (localRegularFrameRicciCoefficient period hPeriod metric patch first
            second ∘ localDiffeomorph.localInverse)
        (patch.coordinateMap coordinate) :=
    (localRegularFrameRicciCoefficient_contDiff period hPeriod metric patch
      first second).contMDiff.contMDiffAt.comp _
        localDiffeomorph.localInverse_contMDiffAt
  apply hRepresentative.congr_of_eventuallyEq
  filter_upwards [localDiffeomorph.localInverse_eventuallyEq_right] with
    nearby hNearby
  have hRight :
      patch.coordinateMap (localDiffeomorph.localInverse nearby) = nearby := by
    simpa only [Function.comp_apply, id_eq] using hNearby
  change
    regularGeneralMetricC0Ricci period hPeriod metric 0 first second nearby =
      localRegularFrameRicciCoefficient period hPeriod metric patch first
        second (localDiffeomorph.localInverse nearby)
  calc
    regularGeneralMetricC0Ricci period hPeriod metric 0 first second nearby =
        regularGeneralMetricC0Ricci period hPeriod metric 0 first second
          (patch.coordinateMap (localDiffeomorph.localInverse nearby)) :=
      congrArg
        (regularGeneralMetricC0Ricci period hPeriod metric 0 first second)
        hRight.symm
    _ = _ := regularGeneralMetricC0Ricci_zero_apply period hPeriod metric patch
      (localDiffeomorph.localInverse nearby) first second

/-- Bundled smooth Ricci coefficient in the genuine global regular frame. -/
def regularGeneralMetricSmoothRicciCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) : SmoothScalarField period hPeriod where
  toFun := regularGeneralMetricC0Ricci period hPeriod metric 0 first second
  contMDiff_toFun := regularGeneralMetricC0Ricci_zero_contMDiff period hPeriod
    metric first second

/-- Einstein bilinear form with cosmological constant on arbitrary local
coordinate vectors. -/
def localEinsteinBilinearValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : CoordinateVector) : Real :=
  localRicciCurvatureBilinearMap period hPeriod metric patch coordinate first
      second -
    1 / 2 * localMetricCoordinateForm period hPeriod metric patch coordinate
        first second *
      localScalarCurvature period hPeriod metric patch coordinate +
    cosmologicalConstant *
      localMetricCoordinateForm period hPeriod metric patch coordinate first
        second

/-- On the coordinate basis, the bilinear presentation is exactly the
previously derived local Einstein tensor. -/
theorem localEinsteinBilinearValue_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    localEinsteinBilinearValue period hPeriod metric cosmologicalConstant patch
        coordinate (Pi.single first 1) (Pi.single second 1) =
      localEinsteinTensor period hPeriod metric cosmologicalConstant patch
        coordinate first second := by
  unfold localEinsteinBilinearValue localEinsteinTensor
  rw [show
      localRicciCurvatureBilinearMap period hPeriod metric patch coordinate
          (Pi.single first 1) (Pi.single second 1) =
        localRicciCurvature period hPeriod metric patch coordinate first
          second by
    exact localRicciCurvatureVector_basis period hPeriod metric patch
      coordinate first second]
  simp [localMetricCoordinateForm, Matrix.toBilin'_apply, Pi.single_apply]

/-- Smooth global regular-frame coefficient of `G + Λg`. -/
def regularGeneralMetricSmoothEinsteinCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real) (first second : Fin 4) :
    SmoothScalarField period hPeriod :=
  regularGeneralMetricSmoothRicciCoefficient period hPeriod metric first second -
    (1 / 2 : Real) • smoothScalarFieldMul period hPeriod
      (regularFrameMetricMatrix period hPeriod metric first second)
      (globalSmoothScalarCurvature period hPeriod metric.metric) +
    cosmologicalConstant •
      regularFrameMetricMatrix period hPeriod metric first second

/-- Global regular-frame coefficient value of `G + Λg`. -/
def regularGeneralMetricEinsteinCoefficientValue
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) : Real :=
  regularGeneralMetricSmoothEinsteinCoefficient period hPeriod metric
    cosmologicalConstant first second point

/-- Every global Einstein coefficient value is smooth. -/
theorem regularGeneralMetricEinsteinCoefficientValue_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real) (first second : Fin 4) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
        cosmologicalConstant first second) := by
  exact (regularGeneralMetricSmoothEinsteinCoefficient period hPeriod metric
    cosmologicalConstant first second).contMDiff_toFun

/-- The global coefficient evaluates in every canonical chart to the intrinsic
local Einstein bilinear form on the pulled regular-frame vectors. -/
theorem regularGeneralMetricEinsteinCoefficientValue_apply_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoordinateVector) (first second : Fin 4) :
    regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
        cosmologicalConstant first second (patch.coordinateMap coordinate) =
      localEinsteinBilinearValue period hPeriod metric.metric
        cosmologicalConstant patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        (pulledRegularFrameVector period hPeriod metric patch second
          coordinate) := by
  simp only [regularGeneralMetricEinsteinCoefficientValue,
    regularGeneralMetricSmoothEinsteinCoefficient,
    regularGeneralMetricSmoothRicciCoefficient,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    smoothScalarFieldSmul_toFun, smoothScalarFieldMul_apply]
  unfold localEinsteinBilinearValue
  rw [regularGeneralMetricC0Ricci_zero_apply period hPeriod,
    localMetricCoordinateForm_pulledRegularFrameVector period hPeriod,
    globalSmoothScalarCurvature_apply_local period hPeriod]
  ring

/-- Gate marker: all sixteen regular-frame coefficients of the unrestricted
Einstein tensor are genuine smooth global fields and agree with the local
intrinsic formula. -/
theorem regular_general_metric_global_smooth_einstein_coefficients_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real) :
    (∀ first second : Fin 4,
      ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
        (regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
          cosmologicalConstant first second)) ∧
      (∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
          (coordinate : CoordinateVector) (first second : Fin 4),
        regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
            cosmologicalConstant first second (patch.coordinateMap coordinate) =
          localEinsteinBilinearValue period hPeriod metric.metric
            cosmologicalConstant patch coordinate
            (pulledRegularFrameVector period hPeriod metric patch first
              coordinate)
            (pulledRegularFrameVector period hPeriod metric patch second
              coordinate)) := by
  exact ⟨fun first second =>
      regularGeneralMetricEinsteinCoefficientValue_contMDiff period hPeriod
        metric cosmologicalConstant first second,
    fun patch coordinate first second =>
      regularGeneralMetricEinsteinCoefficientValue_apply_local period hPeriod
        metric cosmologicalConstant patch coordinate first second⟩

end
end P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D
end JanusFormal
