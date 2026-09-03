import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

/-! # Exact Cartan curvature of a reconstructed gauge potential -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Reconstruction has exactly the supplied regular-frame coefficient. -/
@[simp]
theorem regularFramePotentialCoefficient_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (index : Fin 4) :
    regularFramePotentialCoefficient period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric
          coefficients) component index =
      regularFrameGaugeCoefficient period hPeriod coefficients
        (index, component) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change regularFrameGaugeCovectorFromCoefficients period hPeriod metric
      coefficients component point (metric.frame index point) =
    coefficients point (index, component)
  exact regularFrameGaugeCovectorFromCoefficients_frame period hPeriod metric
    coefficients component point index

/-- The derivative term in Cartan's formula is the frame derivative of the
supplied scalar coefficient. -/
@[simp]
theorem regularFramePotentialDerivative_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (direction index : Fin 4) :
    regularFramePotentialDerivative period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric
          coefficients) component direction index =
      frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameGaugeCoefficient period hPeriod coefficients
          (index, component)) direction := by
  change frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFramePotentialCoefficient period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric
          coefficients) component index) direction = _
  rw [regularFramePotentialCoefficient_reconstructed]

/-- The bracket term is the contraction with the regular-frame structure
coefficients. -/
@[simp]
theorem regularFrameBracketPotentialCoefficient_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameBracketPotentialCoefficient period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric
          coefficients) component first second =
      ∑ upper : Fin 4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric first second
            upper)
          (regularFrameGaugeCoefficient period hPeriod coefficients
            (upper, component)) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hBracket := regularFrameStructureCoefficient_reconstructs period hPeriod
    metric first second point
  have hApplied := congrArg
    (fun vector => regularFrameGaugeCovectorFromCoefficients period hPeriod
      metric coefficients component point vector) hBracket
  change regularFrameGaugeCovectorFromCoefficients period hPeriod metric
      coefficients component point
        (regularFrameLieBracket period hPeriod metric first second point) =
    ∑ upper : Fin 4,
      regularFrameStructureCoefficient period hPeriod metric first second
          upper point * coefficients point (upper, component)
  simpa only [map_sum, map_smul, smul_eq_mul, smoothScalarFieldMul_apply,
    regularFrameGaugeCovectorFromCoefficients_frame] using hApplied

/-- Exact Cartan curvature formula in terms of the supplied coefficient
packet. -/
theorem regularFrameGaugeCurvatureCoefficient_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (first second : Fin 4) :
    regularFrameGaugeCurvatureCoefficient period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric
          coefficients) component first second =
      frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameGaugeCoefficient period hPeriod coefficients
            (second, component)) first -
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameGaugeCoefficient period hPeriod coefficients
            (first, component)) second -
        ∑ upper : Fin 4,
          smoothScalarFieldMul period hPeriod
            (regularFrameStructureCoefficient period hPeriod metric first
              second upper)
            (regularFrameGaugeCoefficient period hPeriod coefficients
              (upper, component)) := by
  rw [regularFrameGaugeCurvatureCoefficient,
    regularFramePotentialDerivative_reconstructed,
    regularFramePotentialDerivative_reconstructed,
    regularFrameBracketPotentialCoefficient_reconstructed]

/-- Gate marker for exact curvature reconstruction. -/
theorem regular_frame_gauge_curvature_reconstruction_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    ∀ component first second,
      regularFrameGaugeCurvatureCoefficient period hPeriod metric
          (regularFrameGaugePotentialFromCoefficients period hPeriod metric
            coefficients) component first second =
        frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            (regularFrameGaugeCoefficient period hPeriod coefficients
              (second, component)) first -
          frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            (regularFrameGaugeCoefficient period hPeriod coefficients
              (first, component)) second -
          ∑ upper : Fin 4,
            smoothScalarFieldMul period hPeriod
              (regularFrameStructureCoefficient period hPeriod metric first
                second upper)
              (regularFrameGaugeCoefficient period hPeriod coefficients
                (upper, component)) :=
  regularFrameGaugeCurvatureCoefficient_reconstructed period hPeriod metric
    coefficients

end

end P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D
end JanusFormal
