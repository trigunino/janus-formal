import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D

/-! # C0 gauge curvature from completed C2 frame coefficients -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev GaugeC2Core :=
  RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

private abbrev GaugeCurvatureC0Matrix :=
  Fin 4 → Fin 4 → C0Scalar period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

/-- Continuous evaluation of one coefficient in the finite C² packet. -/
def gaugeCoefficientC2CoreComponentCLM
    (frameIndex : Fin 4) (component : Fin 2) :
    GaugeC2Core period hPeriod →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj component :
      (Fin 2 → C2Scalar period hPeriod) →L[Real] C2Scalar period hPeriod).comp
    (ContinuousLinearMap.proj frameIndex :
      GaugeC2Core period hPeriod →L[Real]
        (Fin 2 → C2Scalar period hPeriod))

/-- One Cartan curvature coefficient. Spatial differentiation loses one
derivative, hence the natural target is C⁰. -/
def regularFrameGaugeCurvatureC0FromC2Coefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    C0Scalar period hPeriod :=
  regularFrameC2FirstDerivative period hPeriod metric first
      (coefficients second component) -
    regularFrameC2FirstDerivative period hPeriod metric second
      (coefficients first component) -
    ∑ upper : Fin 4,
      regularFrameStructureCoefficientContinuous period hPeriod metric
          first second upper *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (coefficients upper component)

/-- Matrix of completed Cartan coefficients for one Abelian component. -/
def regularFrameGaugeCurvatureC0MatrixFromC2Coefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod)
    (component : Fin 2) : GaugeCurvatureC0Matrix period hPeriod :=
  fun first second =>
    regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
      coefficients component first second

/-- Smooth dependence on the completed coefficient packet. -/
theorem regularFrameGaugeCurvatureC0FromC2Coefficients_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (component : Fin 2) (first second : Fin 4) :
    ContDiff Real ∞
      (fun coefficients : GaugeC2Core period hPeriod =>
        regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
          coefficients component first second) := by
  have hFirst :=
    (regularFrameC2FirstDerivative_contDiff period hPeriod metric first).comp
      (gaugeCoefficientC2CoreComponentCLM period hPeriod second component
        ).contDiff
  have hSecond :=
    (regularFrameC2FirstDerivative_contDiff period hPeriod metric second).comp
      (gaugeCoefficientC2CoreComponentCLM period hPeriod first component
        ).contDiff
  have hBracket : ContDiff Real ∞
      (fun coefficients : GaugeC2Core period hPeriod =>
        ∑ upper : Fin 4,
          regularFrameStructureCoefficientContinuous period hPeriod metric
              first second upper *
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
              (coefficients upper component)) := by
    apply ContDiff.sum
    intro upper _
    exact contDiff_const.mul
      (((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
        (gaugeCoefficientC2CoreComponentCLM period hPeriod upper component)
          ).contDiff)
  exact (hFirst.sub hSecond).sub hBracket

/-- The whole curvature matrix depends smoothly on the C² packet. -/
theorem regularFrameGaugeCurvatureC0MatrixFromC2Coefficients_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (component : Fin 2) :
    ContDiff Real ∞
      (regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod
        metric · component) := by
  rw [contDiff_pi]
  intro first
  rw [contDiff_pi]
  intro second
  exact regularFrameGaugeCurvatureC0FromC2Coefficients_contDiff period hPeriod
    metric component first second

/-- On exact smooth coefficients, the completed C⁰ formula is the genuine
curvature of the reconstructed intrinsic potential. -/
theorem regularFrameGaugeCurvatureC0FromC2Coefficients_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients)
        component first second =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameGaugeCurvatureCoefficient period hPeriod metric
          (regularFrameGaugePotentialFromCoefficients period hPeriod metric
            coefficients) component first second) := by
  apply ContinuousMap.ext
  intro point
  change regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients)
      component first second point =
    regularFrameGaugeCurvatureCoefficient period hPeriod metric
      (regularFrameGaugePotentialFromCoefficients period hPeriod metric
        coefficients) component first second point
  rw [regularFrameGaugeCurvatureCoefficient_reconstructed]
  unfold regularFrameGaugeCurvatureC0FromC2Coefficients
  simp only [smoothGaugeCoefficientC2CoreLinearMap_apply,
    ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply]
  rw [regularFrameC2FirstDerivative_smooth,
    regularFrameC2FirstDerivative_smooth]
  simp_rw [canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

/-- Matrix form of the exact smooth agreement. -/
theorem regularFrameGaugeCurvatureC0MatrixFromC2Coefficients_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) :
    regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients)
        component =
      fun first second => smoothToCanonicalPhysicalContinuousScalar
        period hPeriod
          (regularFrameGaugeCurvatureCoefficient period hPeriod metric
            (regularFrameGaugePotentialFromCoefficients period hPeriod metric
              coefficients) component first second) := by
  funext first second
  exact regularFrameGaugeCurvatureC0FromC2Coefficients_smooth period hPeriod
    metric coefficients component first second

/-- Gate marker: gauge C² coefficients now produce the exact reconstructed
Maxwell curvature in C⁰ with smooth parameter dependence. -/
theorem regular_frame_gauge_curvature_c0_from_c2_coefficients_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (∀ component,
      ContDiff Real ∞
        (regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod
          metric · component)) ∧
      (∀ (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
          component,
        regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod
            metric
            (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients)
            component =
          fun first second => smoothToCanonicalPhysicalContinuousScalar
            period hPeriod
              (regularFrameGaugeCurvatureCoefficient period hPeriod metric
                (regularFrameGaugePotentialFromCoefficients period hPeriod
                  metric coefficients) component first second)) := by
  exact ⟨regularFrameGaugeCurvatureC0MatrixFromC2Coefficients_contDiff
      period hPeriod metric,
    regularFrameGaugeCurvatureC0MatrixFromC2Coefficients_smooth period hPeriod
      metric⟩

end

end P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
end JanusFormal
