import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D

/-! # Exact gauge coefficients and their ordered first derivatives

The coefficients of `dc` are the regular-frame first derivatives of the
ghost. Differentiating those coefficients uses the existing ordered second
derivative of the ghost, with no third-jet assumption.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameExactGaugeCoefficients4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The exact potential's stored coefficient is the ghost's first derivative. -/
theorem regularFrameGaugeCoefficient_exact
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (index : Fin 4) :
    regularFrameGaugeCoefficient period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric
          (exactGaugePotential period hPeriod ghost)) (index, component) =
      frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (ghostComponent period hPeriod ghost component) index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (frameDerivative_eq_mfderiv period hPeriod Real
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (ghostComponent period hPeriod ghost component) point index).symm

/-- The same identity in the intrinsic potential-coefficient API. -/
theorem regularFramePotentialCoefficient_exact
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (index : Fin 4) :
    regularFramePotentialCoefficient period hPeriod metric
        (exactGaugePotential period hPeriod ghost) component index =
      frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (ghostComponent period hPeriod ghost component) index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (frameDerivative_eq_mfderiv period hPeriod Real
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (ghostComponent period hPeriod ghost component) point index).symm

/-- A derivative of an exact gauge coefficient is the ordered ghost second derivative. -/
theorem regularFrameGaugeCoefficient_exact_derivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (outer inner : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameGaugeCoefficient period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric
            (exactGaugePotential period hPeriod ghost)) (inner, component)) point outer =
      frameSecondDerivative period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (ghostComponent period hPeriod ghost component) point outer inner := by
  simp only [regularFrameGaugeCoefficient_exact, frameSecondDerivative]

/-- The intrinsic derivative coefficient exposes the same ordered second jet. -/
theorem regularFramePotentialDerivative_exact
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (outer inner : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFramePotentialDerivative period hPeriod metric
        (exactGaugePotential period hPeriod ghost) component outer inner point =
      frameSecondDerivative period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (ghostComponent period hPeriod ghost component) point outer inner := by
  change frameDerivative period hPeriod Real
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (regularFramePotentialCoefficient period hPeriod metric
      (exactGaugePotential period hPeriod ghost) component inner) point outer = _
  simp only [regularFramePotentialCoefficient_exact, frameSecondDerivative]

end
end P0EFTJanusRegularFrameExactGaugeCoefficients4D
end JanusFormal
