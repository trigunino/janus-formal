import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameExactGaugeCoefficients4D

/-! # The variable-metric C² FP expression is the actual Faddeev--Popov operator

The ghost's scalar second jets suffice. No completed C² jet of its derivative
is formed: the intrinsic Lorenz trace is applied to the smooth exact potential
and its coefficients are identified with the first and second ghost derivatives.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2FPSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
open P0EFTJanusRegularFrameLorenzCovariantTrace4D
open P0EFTJanusVariableMetricC2LorenzFPFeatures4D
open P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
open P0EFTJanusRegularFrameExactGaugeCoefficients4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Componentwise lift of the smooth ghost into its scalar C² core. -/
def smoothAbelianGhostC2Core
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    AbelianGhostC2Core period hPeriod :=
  fun component => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (ghostComponent period hPeriod ghost component)

/-- Exact smooth agreement with the varied metric's genuine `δ_g d`. -/
theorem variableMetricC2FPComponentExpression_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    variableMetricC2FPComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
        (smoothAbelianGhostC2Core period hPeriod ghost) component =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost) component) := by
  apply ContinuousMap.ext
  intro point
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  have hInverse := variableMetricC2InverseMatrix_eq_lorenzMetricInverse period hPeriod
    reference tensor metric hMetric hVariation (witness.patch.coordinateMap witness.coordinate)
  change (∑ first : Fin 4, ∑ second : Fin 4,
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
          first second (witness.patch.coordinateMap witness.coordinate) *
        (regularFrameC2SecondDerivative period hPeriod reference first second
            (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
              (ghostComponent period hPeriod ghost component))
            (witness.patch.coordinateMap witness.coordinate) -
          ∑ upper : Fin 4,
            regularGeneralMetricC0Christoffel period hPeriod reference
                (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
                upper first second (witness.patch.coordinateMap witness.coordinate) *
              regularFrameC2FirstDerivative period hPeriod reference upper
                (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
                  (ghostComponent period hPeriod ghost component))
                (witness.patch.coordinateMap witness.coordinate))) =
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
      (exactGaugePotential period hPeriod ghost)
      (witness.patch.coordinateMap witness.coordinate) component
  rw [globalGeneralMetricAbelianLorenzCodifferential_eq_regularFrameCovariantTrace
    period hPeriod reference metric _ component witness.patch witness.coordinate]
  simp only [regularFrameC2SecondDerivative_smooth,
    regularFrameC2FirstDerivative_smooth, regularFramePotentialCoefficient_exact]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  have hEntry := congrArg (fun matrix : Matrix (Fin 4) (Fin 4) Real =>
    matrix first second) hInverse
  rw [show regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference
      (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
      first second (witness.patch.coordinateMap witness.coordinate) =
    (regularFrameLorenzMetricMatrix period hPeriod reference metric
      (witness.patch.coordinateMap witness.coordinate))⁻¹ first second from hEntry]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro upper _
  congr 1
  exact regularGeneralMetricC0Christoffel_smooth_apply period hPeriod reference
    tensor metric hMetric hVariation witness.patch witness.coordinate upper first second

end
end P0EFTJanusVariableMetricC2FPSmoothAgreement4D
end JanusFormal
