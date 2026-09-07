import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricCartanCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2CartanFirstJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D

/-! # Smooth agreement of the completed metric Cartan first jet

The intrinsic coefficient identity is differentiated as an equality of smooth
scalar fields. Only the ordered second jets of metric and ghost coefficients
are used; no C² extension of the Cartan tensor itself is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2CartanSmoothJet4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusVariableMetricDeDonderFirstJet4D
open P0EFTJanusVariableMetricC2CartanFirstJet4D
open P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Scalar := SmoothScalarField period hPeriod
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

private theorem scalarSum_apply (fields : Fin 4 → Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ index, fields index) point = ∑ index, fields index point := by
  let evaluation : Scalar period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation fields Finset.univ

private theorem scalarAdd_apply (first second : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (first + second) point = first point + second point := rfl

private theorem scalarSub_apply (first second : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (first - second) point = first point - second point := rfl

private theorem scalarMul_apply (first second : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothScalarFieldMul period hPeriod first second point = first point * second point := rfl

private theorem smoothScalarContinuous_apply (field : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D.smoothToCanonicalPhysicalContinuousScalar
        period hPeriod field point = field point := rfl

private theorem frameComponent_apply (reference : RegularGeneralLorentzMetric period hPeriod)
    (field : Scalar period hPeriod) (index : Fin 4) (point : EffectiveQuotient period hPeriod) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) field index point =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) field point index := rfl

private def frameDEval (reference : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    Scalar period hPeriod →ₗ[Real] Real where
  toFun := fun field => frameDerivative period hPeriod Real
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) field point index
  map_add' first second := by
    have h := congrFun (congrFun
      (frameDerivative_add period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) first second) point) index
    simpa only [Pi.add_apply] using h
  map_smul' scalar field := by
    have h := congrFun (congrFun
      (frameDerivative_smul period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) scalar field) point) index
    simpa only [Pi.smul_apply, RingHom.id_apply] using h

private theorem frameDEval_apply (reference : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) (field : Scalar period hPeriod) :
    frameDEval period hPeriod reference point index field =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) field point index := rfl

private theorem frameDEval_mul (reference : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4)
    (first second : Scalar period hPeriod) :
    frameDEval period hPeriod reference point index (smoothScalarFieldMul period hPeriod first second) =
      first point * frameDEval period hPeriod reference point index second +
        second point * frameDEval period hPeriod reference point index first :=
  congrFun (congrFun (frameDerivative_mul period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) first second) point) index

private def smoothCartanCoefficientFormula
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin 4 → Scalar period hPeriod) (first second : Fin 4) :
    Scalar period hPeriod :=
  let h := regularFrameSymmetricTensorCoefficient period hPeriod reference tensor
  let d := fun field index => frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) field index
  let mul := smoothScalarFieldMul period hPeriod
  let bracketCoefficient := regularFrameStructureCoefficient period hPeriod reference
  ∑ index : Fin 4,
    (mul (coefficients index) (d (h first second) index) +
      mul (d (coefficients index) first) (h index second) +
      mul (d (coefficients index) second) (h first index) -
      ∑ upper : Fin 4,
        (mul (mul (coefficients index) (bracketCoefficient index first upper)) (h upper second) +
          mul (mul (coefficients index) (bracketCoefficient index second upper)) (h first upper)))

private theorem smoothCartanCoefficient_eq_formula
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin 4 → Scalar period hPeriod) (first second : Fin 4) :
    regularFrameSymmetricTensorCoefficient period hPeriod reference
        (smoothMetricCartanAction period hPeriod
          (regularFrameGhostFromCoefficients period hPeriod reference coefficients) tensor)
        first second =
      smoothCartanCoefficientFormula period hPeriod reference tensor coefficients first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simpa only [smoothCartanCoefficientFormula, scalarSum_apply, scalarAdd_apply,
    scalarSub_apply, scalarMul_apply, frameComponent_apply] using
    smoothMetricCartanAction_regularFrameCoefficient period hPeriod reference coefficients
      tensor point first second

private theorem smoothMetricC2Matrix_eq_coefficients
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor) :
    regularGeneralMetricC2MetricMatrix period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor) =
      fun first second => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameSymmetricTensorCoefficient period hPeriod reference metric.tensor first second) := by
  change regularGeneralMetricC2MetricMatrix period hPeriod reference
    (smoothToGeneralMetricRelativeC2Core period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
      reference.metric variationTensor) = _
  rw [candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth]
  funext first second
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod reference variationTensor first second) = _
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_apply_eq_variedMetric
    period hPeriod reference variationTensor metric hMetric first second point

theorem variableMetricC2CartanComponentExpression_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
    (coefficients : Fin 4 → Scalar period hPeriod) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    variableMetricC2CartanComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients index))
        first second point =
      regularFrameSymmetricTensorCoefficient period hPeriod reference
        (smoothMetricCartanAction period hPeriod
          (regularFrameGhostFromCoefficients period hPeriod reference coefficients) metric.tensor)
        first second point := by
  simp only [variableMetricC2CartanComponentExpression,
    regularGeneralMetricC0MetricCoefficient, regularGeneralMetricC0MetricFirstDerivative,
    smoothMetricC2Matrix_eq_coefficients period hPeriod reference variationTensor metric hMetric,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    regularFrameC2FirstDerivative_smooth, regularFrameStructureCoefficientContinuous_apply]
  exact (smoothMetricCartanAction_regularFrameCoefficient period hPeriod reference coefficients
    metric.tensor point first second).symm

theorem variableMetricC2CartanComponentFirstDerivative_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
    (coefficients : Fin 4 → Scalar period hPeriod) (outer first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    variableMetricC2CartanComponentFirstDerivative period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients index))
        outer first second point =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        (regularFrameSymmetricTensorCoefficient period hPeriod reference
          (smoothMetricCartanAction period hPeriod
            (regularFrameGhostFromCoefficients period hPeriod reference coefficients) metric.tensor)
          first second) point outer := by
  rw [smoothCartanCoefficient_eq_formula]
  change _ = frameDEval period hPeriod reference point outer
    (smoothCartanCoefficientFormula period hPeriod reference metric.tensor coefficients first second)
  simp only [smoothCartanCoefficientFormula, map_sum, map_add, map_sub,
    frameDEval_mul, scalarMul_apply]
  simp only [variableMetricC2CartanComponentFirstDerivative,
    regularGeneralMetricC0MetricCoefficient, regularGeneralMetricC0MetricFirstDerivative,
    regularGeneralMetricC0MetricSecondDerivative,
    smoothMetricC2Matrix_eq_coefficients period hPeriod reference variationTensor metric hMetric,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    regularFrameC2FirstDerivative_smooth, regularFrameC2SecondDerivative_smooth,
    regularFrameStructureCoefficientContinuous_apply,
    regularFrameStructureCoefficientDerivativeContinuous_apply,
    frameDEval_apply, frameComponent_apply, frameSecondDerivative,
    smoothScalarContinuous_apply]
  apply Finset.sum_congr rfl
  intro index _
  apply congrArg₂ (fun left right : Real => left - right)
  · ring
  · apply Finset.sum_congr rfl
    intro upper _
    ring

/-- The completed first jet is exactly the first jet of the genuine smooth Cartan tensor. -/
theorem variableMetricC2CartanFirstJet_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
    (coefficients : Fin 4 → Scalar period hPeriod) :
    variableMetricC2CartanFirstJet period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients index)) =
      tensorC2ToC0FirstJetCLM period hPeriod reference
        (smoothTensorC2Coefficients period hPeriod reference
          (smoothMetricCartanAction period hPeriod
            (regularFrameGhostFromCoefficients period hPeriod reference coefficients) metric.tensor)) := by
  rw [tensorC2ToC0FirstJetCLM_apply]
  apply Prod.ext
  · funext first second
    apply ContinuousMap.ext
    intro point
    simp only [variableMetricC2CartanFirstJet, smoothTensorC2Coefficients,
      smoothGeneralMetricTensorToC2Matrix_apply, canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    exact variableMetricC2CartanComponentExpression_smooth period hPeriod reference
      variationTensor metric hMetric coefficients first second point
  · funext outer first second
    apply ContinuousMap.ext
    intro point
    simp only [variableMetricC2CartanFirstJet, smoothTensorC2Coefficients,
      smoothGeneralMetricTensorToC2Matrix_apply, regularFrameC2FirstDerivative_smooth]
    exact variableMetricC2CartanComponentFirstDerivative_smooth period hPeriod reference
      variationTensor metric hMetric coefficients outer first second point

end
end P0EFTJanusVariableMetricC2CartanSmoothJet4D
end JanusFormal
