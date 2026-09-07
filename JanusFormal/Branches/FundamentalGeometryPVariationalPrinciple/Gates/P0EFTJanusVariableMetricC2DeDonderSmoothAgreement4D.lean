import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameSymmetricTensorDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! # Completed De Donder features agree with the actual variable-metric operator

The covariant divergence and trace differential are both retained. The
reference frame is fixed independently of the smooth varied metric.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2DeDonderSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffel4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusRegularFrameLorenzCovariantTrace4D
open P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

variable (reference : RegularGeneralLorentzMetric period hPeriod)
  (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (metric : SmoothGeneralLorentzMetric period hPeriod)
  (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
  (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor ∈
    regularGeneralMetricC2Domain period hPeriod reference)
  (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)

include hMetric hVariation

private theorem completed_divergence_smooth
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (component : Fin 4) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          first second (patch.coordinateMap coordinate) *
        (regularFrameC2FirstDerivative period hPeriod reference first
            (smoothTensorC2Coefficients period hPeriod reference tensor second component)
            (patch.coordinateMap coordinate) -
          (∑ upper : Fin 4,
            regularGeneralMetricC0Christoffel period hPeriod reference
                (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
                upper first second (patch.coordinateMap coordinate) *
              canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
                (smoothTensorC2Coefficients period hPeriod reference tensor upper component)
                (patch.coordinateMap coordinate)) -
          (∑ upper : Fin 4,
            regularGeneralMetricC0Christoffel period hPeriod reference
                (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
                upper first component (patch.coordinateMap coordinate) *
              canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
                (smoothTensorC2Coefficients period hPeriod reference tensor second upper)
                (patch.coordinateMap coordinate)))) =
      globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor.tensor
        (patch.coordinateMap coordinate) (reference.frame component (patch.coordinateMap coordinate)) := by
  have hInverse := variableMetricC2InverseMatrix_eq_lorenzMetricInverse period hPeriod
    reference variationTensor metric hMetric hVariation (patch.coordinateMap coordinate)
  have hEntry (first second : Fin 4) :
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          first second (patch.coordinateMap coordinate) =
        (regularFrameLorenzMetricMatrix period hPeriod reference metric
          (patch.coordinateMap coordinate))⁻¹ first second :=
    congrArg (fun matrix : Matrix (Fin 4) (Fin 4) Real => matrix first second) hInverse
  have hChristoffel (upper first second : Fin 4) :
      regularGeneralMetricC0Christoffel period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          upper first second (patch.coordinateMap coordinate) =
        regularFrameTensorChristoffelCoefficient period hPeriod reference metric patch coordinate
          upper first second := by
    exact regularGeneralMetricC0Christoffel_smooth_apply period hPeriod reference
      variationTensor metric hMetric hVariation patch coordinate upper first second
  rw [globalGeneralMetricSymmetricTensorDivergence_eq_regularFrameCovariantTrace
    period hPeriod reference metric tensor patch coordinate component]
  simp only [hEntry, hChristoffel, smoothTensorC2Coefficients,
    smoothGeneralMetricTensorToC2Matrix_apply, regularFrameC2FirstDerivative_smooth,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth, regularFrameSymmetricTensorCoefficient]
  rfl

/-- Equality at every quotient point, with no third spatial derivative. -/
theorem variableMetricC2DeDonderComponentExpression_smooth_apply
    (point : EffectiveQuotient period hPeriod) (component : Fin 4) :
    variableMetricC2DeDonderComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothTensorC2Coefficients period hPeriod reference tensor) component point =
      globalGeneralMetricDeDonder period hPeriod metric tensor point
        (reference.frame component point) := by
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  have hTrace := variableMetricC2TensorTraceDerivativeExpression_smooth period hPeriod reference
    variationTensor metric hMetric hVariation tensor
    (witness.patch.coordinateMap witness.coordinate) component
  unfold variableMetricC2DeDonderComponentExpression
  simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rw [completed_divergence_smooth period hPeriod reference variationTensor metric hMetric
    hVariation tensor witness.patch witness.coordinate component]
  change _ - (1 / 2 : Real) *
    variableMetricC2TensorTraceDerivativeExpression period hPeriod reference
      (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
      (smoothTensorC2Coefficients period hPeriod reference tensor) component
      (witness.patch.coordinateMap witness.coordinate) = _
  rw [hTrace, globalGeneralMetricDeDonder_apply]
  change _ - (1 / 2 : Real) * _ = _ + (-1 / 2 : Real) * _
  ring_nf
  rfl

/-- The completed C⁰ feature equals the smooth intrinsic one-form component. -/
theorem variableMetricC2DeDonderComponentExpression_smooth
    (component : Fin 4) :
    variableMetricC2DeDonderComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothTensorC2Coefficients period hPeriod reference tensor) component =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalCovectorVectorPairingField period hPeriod
          (globalGeneralMetricDeDonder period hPeriod metric tensor) (reference.frame component)) := by
  apply ContinuousMap.ext
  intro point
  exact variableMetricC2DeDonderComponentExpression_smooth_apply period hPeriod reference
    variationTensor metric hMetric hVariation tensor point component

/-- The same agreement holds in the physical L² completion. -/
theorem variableMetricC2DeDonderComponentL2_smooth
    (component : Fin 4) :
    variableMetricC2DeDonderComponentL2 period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothTensorC2Coefficients period hPeriod reference tensor) component =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalCovectorVectorPairingField period hPeriod
          (globalGeneralMetricDeDonder period hPeriod metric tensor) (reference.frame component)) := by
  unfold variableMetricC2DeDonderComponentL2
  rw [variableMetricC2DeDonderComponentExpression_smooth period hPeriod reference variationTensor
    metric hMetric hVariation tensor component, continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]

end
end P0EFTJanusVariableMetricC2DeDonderSmoothAgreement4D
end JanusFormal
