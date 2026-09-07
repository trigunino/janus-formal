import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2LorenzFPFeatures4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameLorenzCovariantTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D

/-! # The variable-metric completed Lorenz expression is the actual operator

The reference frame stays fixed while the metric varies.  On every smooth
admissible variation the C⁰ expression agrees with the intrinsic Lorenz
codifferential, without freezing its metric argument.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D

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
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusRegularFrameLorenzCovariantTrace4D
open P0EFTJanusVariableMetricC2LorenzFPFeatures4D

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

theorem variableMetricC2InverseMatrix_eq_lorenzMetricInverse
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0SmoothInverseMatrix period hPeriod reference tensor point =
      (regularFrameLorenzMetricMatrix period hPeriod reference metric point)⁻¹ := by
  rw [regularGeneralMetricC0InverseMetricMatrix_smooth_eq_inv
    period hPeriod reference tensor hVariation point]
  congr 1
  ext row column
  exact candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
    period hPeriod reference tensor metric hMetric row column point

/-- Exact smooth realization with the varied intrinsic metric and fixed coefficient frame. -/
theorem variableMetricC2LorenzComponentExpression_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + tensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) :
    variableMetricC2LorenzComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) component =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
            (regularFrameGaugePotentialFromCoefficients period hPeriod reference coefficients))
          component) := by
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
        (regularFrameC2FirstDerivative period hPeriod reference first
            (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients second component)
            (witness.patch.coordinateMap witness.coordinate) -
          ∑ upper : Fin 4,
            regularGeneralMetricC0Christoffel period hPeriod reference
                (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
                upper first second (witness.patch.coordinateMap witness.coordinate) *
              canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
                (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients upper component)
                (witness.patch.coordinateMap witness.coordinate))) =
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric
      (regularFrameGaugePotentialFromCoefficients period hPeriod reference coefficients)
      (witness.patch.coordinateMap witness.coordinate) component
  rw [globalGeneralMetricAbelianLorenzCodifferential_eq_regularFrameCovariantTrace
    period hPeriod reference metric _ component witness.patch witness.coordinate]
  simp only [smoothGaugeCoefficientC2CoreLinearMap_apply,
    regularFrameC2FirstDerivative_smooth,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    regularFramePotentialCoefficient_reconstructed]
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
end P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
end JanusFormal
