import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DeDonderFeatures4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D

/-! # Smooth realization of the completed tensor-trace derivative

The inverse metric varies, while the tensor coefficients use the fixed reference
frame. Both terms of the differentiated contraction are retained.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelDerivative4D
open P0EFTJanusRegularFrameLorenzCovariantTrace4D
open P0EFTJanusRegularFrameMetricTensorTrace4D
open P0EFTJanusVariableMetricC2LorenzSmoothAgreement4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
private abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
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

/-- The smooth tensor lift uses the same fixed frame as the completed features. -/
def smoothTensorC2Coefficients
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    TensorC2Coefficients period hPeriod :=
  smoothGeneralMetricTensorToC2Matrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor

/-- The unscaled trace-gradient term in the completed De Donder expression. -/
def variableMetricC2TensorTraceDerivativeExpression
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod reference)
    (tensor : TensorC2Coefficients period hPeriod) (direction : Fin 4) :
    C0Scalar period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    (regularGeneralMetricC0InverseMetricDerivative period hPeriod reference variation
        direction first second *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (tensor first second) +
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference variation
        first second *
      regularFrameC2FirstDerivative period hPeriod reference direction (tensor first second))

private theorem inverseCoefficient_local_differentiableAt
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference tensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (row column : Fin 4) :
    DifferentiableAt Real (fun current =>
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor)
        row column (patch.coordinateMap current)) coordinate := by
  classical
  let variation := regularGeneralMetricSmoothC2Variation period hPeriod reference tensor
  let matrix : Vector4 → Matrix4 := fun current row column =>
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period hPeriod
      reference tensor row column (patch.coordinateMap current)
  let inverse : Vector4 → Matrix4 := fun current row column =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference variation
      row column (patch.coordinateMap current)
  have hMatrixContDiff : ContDiff Real ∞ matrix := by
    have hFormula : matrix = fun current =>
        ∑ currentRow : Fin 4, ∑ currentColumn : Fin 4,
          matrix current currentRow currentColumn •
            Matrix.single currentRow currentColumn (1 : Real) := by
      funext current
      simpa using (Matrix.matrix_eq_sum_single (matrix current))
    rw [hFormula]
    apply ContDiff.sum
    intro currentRow _
    apply ContDiff.sum
    intro currentColumn _
    exact (((candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix period hPeriod
      reference tensor currentRow currentColumn).contMDiff_toFun.comp
        patch.coordinateMap_contMDiff).contDiff).smul_const _
  have hMatrix : DifferentiableAt Real matrix coordinate :=
    hMatrixContDiff.differentiable (by simp) coordinate
  have hLeft (current : Vector4) : inverse current * matrix current = 1 := by
    ext currentRow currentColumn
    exact regularGeneralMetricC0InverseMetricCoefficient_smooth_mul_actualMatrix
      period hPeriod reference tensor hVariation (patch.coordinateMap current)
        currentRow currentColumn
  have hUnit : IsUnit (matrix coordinate) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_left_inverse (hLeft coordinate)
  have hFunction : inverse = Ring.inverse ∘ matrix := by
    funext current
    change inverse current = Ring.inverse (matrix current)
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    exact (Matrix.inv_eq_left_inv (hLeft current)).symm
  let unitMetric : Matrix4ˣ := hUnit.unit
  have hInverse : DifferentiableAt Real inverse coordinate := by
    rw [hFunction]
    exact ((hasFDerivAt_ringInverse (𝕜 := Real) unitMetric).comp coordinate
      hMatrix.hasFDerivAt).differentiableAt
  simpa only [inverse] using
    (differentiableAt_pi.mp (differentiableAt_pi.mp hInverse row) column)

/-- The two completed product-rule terms give the actual varied-metric trace differential. -/
theorem variableMetricC2TensorTraceDerivativeExpression_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor ∈
      regularGeneralMetricC2Domain period hPeriod reference)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (direction : Fin 4) :
    variableMetricC2TensorTraceDerivativeExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothTensorC2Coefficients period hPeriod reference tensor) direction point =
      generalMetricTensorTraceDifferential period hPeriod metric tensor point
        (reference.frame direction point) := by
  classical
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  let field := generalMetricFrameCoefficient period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor
  let inverse : Fin 4 → Fin 4 → Vector4 → Real := fun first second current =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod reference
      (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
      first second (witness.patch.coordinateMap current)
  let coefficient : Fin 4 → Fin 4 → Vector4 → Real := fun first second =>
    (field first second).toFun ∘ witness.patch.coordinateMap
  let vector := pulledRegularFrameVector period hPeriod reference witness.patch direction
    witness.coordinate
  have hInverseDiff (first second : Fin 4) :
      DifferentiableAt Real (inverse first second) witness.coordinate :=
    inverseCoefficient_local_differentiableAt period hPeriod reference variationTensor
      hVariation witness.patch witness.coordinate first second
  have hCoefficientDiff (first second : Fin 4) :
      DifferentiableAt Real (coefficient first second) witness.coordinate :=
    (((field first second).contMDiff_toFun.comp
      witness.patch.coordinateMap_contMDiff).contDiff).differentiable (by simp) witness.coordinate
  have hFunction :
      (fun current => ∑ first : Fin 4, ∑ second : Fin 4,
        (regularFrameLorenzMetricMatrix period hPeriod reference metric
          (witness.patch.coordinateMap current))⁻¹ first second *
          tensor.tensor (witness.patch.coordinateMap current)
            (reference.frame first (witness.patch.coordinateMap current))
            (reference.frame second (witness.patch.coordinateMap current))) =
      (fun current => ∑ first : Fin 4, ∑ second : Fin 4,
        inverse first second current * coefficient first second current) := by
    funext current
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    have hEntry := congrArg (fun matrix : Matrix4 => matrix first second)
      (variableMetricC2InverseMatrix_eq_lorenzMetricInverse period hPeriod reference
        variationTensor metric hMetric hVariation (witness.patch.coordinateMap current))
    change _ * _ = _ * _
    congr 1
    exact hEntry.symm
  have hProduct := HasFDerivAt.fun_sum (u := Finset.univ) (fun first _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun second _ =>
      (hInverseDiff first second).hasFDerivAt.mul
        (hCoefficientDiff first second).hasFDerivAt))
  have hDerivative :
      fderiv Real (fun current => ∑ first : Fin 4, ∑ second : Fin 4,
        inverse first second current * coefficient first second current)
        witness.coordinate vector =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (inverse first second witness.coordinate *
            fderiv Real (coefficient first second) witness.coordinate vector +
          coefficient first second witness.coordinate *
            fderiv Real (inverse first second) witness.coordinate vector) := by
    have hApplied :=
      congrArg (fun derivative : Vector4 →L[Real] Real => derivative vector) hProduct.fderiv
    simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, Pi.mul_apply] at hApplied
    exact hApplied
  have hValue (first second : Fin 4) :
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (smoothTensorC2Coefficients period hPeriod reference tensor first second)
          (witness.patch.coordinateMap witness.coordinate) =
        coefficient first second witness.coordinate :=
    congrArg (fun value : C0Scalar period hPeriod =>
      value (witness.patch.coordinateMap witness.coordinate))
      (canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod (field first second))
  have hFirstDerivative (first second : Fin 4) :
      regularFrameC2FirstDerivative period hPeriod reference direction
          (smoothTensorC2Coefficients period hPeriod reference tensor first second)
          (witness.patch.coordinateMap witness.coordinate) =
        fderiv Real (coefficient first second) witness.coordinate vector :=
    (regularFrameC2FirstDerivative_smooth period hPeriod reference direction
      (field first second) (witness.patch.coordinateMap witness.coordinate)).trans
      (fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod reference
        (field first second) witness.patch witness.coordinate direction).symm
  have hInverseDerivative (first second : Fin 4) :
      fderiv Real (inverse first second) witness.coordinate vector =
        regularGeneralMetricC0InverseMetricDerivative period hPeriod reference
          (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
          direction first second (witness.patch.coordinateMap witness.coordinate) :=
    regularGeneralMetricC0InverseMetricCoefficient_smooth_local_fderiv period hPeriod
      reference variationTensor hVariation witness.patch witness.coordinate direction first second
  rw [generalMetricTensorTraceDifferential_eq_regularFrameLocalDerivative,
    hFunction, hDerivative]
  change (∑ first : Fin 4, ∑ second : Fin 4,
    (regularGeneralMetricC0InverseMetricDerivative period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        direction first second (witness.patch.coordinateMap witness.coordinate) *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (smoothTensorC2Coefficients period hPeriod reference tensor first second)
        (witness.patch.coordinateMap witness.coordinate) +
    inverse first second witness.coordinate *
      regularFrameC2FirstDerivative period hPeriod reference direction
        (smoothTensorC2Coefficients period hPeriod reference tensor first second)
        (witness.patch.coordinateMap witness.coordinate))) = _
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [hValue, hFirstDerivative, hInverseDerivative]
  ring

end
end P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D
end JanusFormal
