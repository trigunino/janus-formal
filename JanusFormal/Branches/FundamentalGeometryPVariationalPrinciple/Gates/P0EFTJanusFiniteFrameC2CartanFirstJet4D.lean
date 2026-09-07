import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2KoszulConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricCartanGlobalAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D

/-! # The genuine Cartan first jet in finite generating families

The polynomial uses metric and ghost C² coefficients, including the ordered
second derivatives and the derivatives of the fixed bracket coefficients.
Its smooth agreement is an identity for the intrinsic Lie derivative.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2CartanFirstJet4D

set_option autoImplicit false

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
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusMetricCartanFiberCore4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Scalar := SmoothScalarField period hPeriod
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

abbrev FiniteFrameCartanC0FirstJet (frame : SmoothD8Frame period hPeriod) :=
  (Fin frame.count → Fin frame.count → C0Scalar period hPeriod) ×
    (Fin frame.count → Fin frame.count → Fin frame.count → C0Scalar period hPeriod)

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "MetricCore" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "GhostCore" => FiniteFrameDiffeomorphismC2Core period hPeriod frame

private def metricSecondDerivative (outer inner first second : Fin frame.count)
    (variation : MetricCore) : C0Scalar period hPeriod :=
  finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame outer inner
    (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric variation first second)

private def bracketDerivative (outer first second upper : Fin frame.count) : C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (frameDerivativeComponentField period hPeriod frame
      (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second upper) outer)

def finiteFrameC2CartanComponentExpression (variation : MetricCore) (ghost : GhostCore)
    (first second : Fin frame.count) : C0Scalar period hPeriod :=
  let g := fun i j => finiteFrameMetricC0Coefficient period hPeriod frame baseMetric i j variation
  let dg := fun a i j => finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric a i j variation
  let c := fun a => canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (ghost a)
  let dc := fun i a => finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame i (ghost a)
  let bracket := finiteFrameStructureC0Coefficient period hPeriod frame baseMetric
  ∑ a : Fin frame.count,
    (c a * dg a first second + dc first a * g a second + dc second a * g first a -
      ∑ b : Fin frame.count,
        (c a * bracket a first b * g b second + c a * bracket a second b * g first b))

def finiteFrameC2CartanComponentFirstDerivative (variation : MetricCore) (ghost : GhostCore)
    (outer first second : Fin frame.count) : C0Scalar period hPeriod :=
  let g := fun i j => finiteFrameMetricC0Coefficient period hPeriod frame baseMetric i j variation
  let dg := fun a i j => finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric a i j variation
  let ddg := fun a b i j => metricSecondDerivative period hPeriod frame baseMetric a b i j variation
  let c := fun a => canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (ghost a)
  let dc := fun i a => finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame i (ghost a)
  let ddc := fun i j a => finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame i j (ghost a)
  let bracket := finiteFrameStructureC0Coefficient period hPeriod frame baseMetric
  let dBracket := bracketDerivative period hPeriod frame baseMetric
  ∑ a : Fin frame.count,
    ((dc outer a * dg a first second + c a * ddg outer a first second) +
      (ddc outer first a * g a second + dc first a * dg outer a second) +
      (ddc outer second a * g first a + dc second a * dg outer first a) -
      ∑ b : Fin frame.count,
        ((dc outer a * bracket a first b * g b second + c a * dBracket outer a first b * g b second +
          c a * bracket a first b * dg outer b second) +
        (dc outer a * bracket a second b * g first b + c a * dBracket outer a second b * g first b +
          c a * bracket a second b * dg outer first b)))

def finiteFrameC2CartanFirstJet (variation : MetricCore) (ghost : GhostCore) :
    FiniteFrameCartanC0FirstJet period hPeriod frame :=
  (finiteFrameC2CartanComponentExpression period hPeriod frame baseMetric variation ghost,
    finiteFrameC2CartanComponentFirstDerivative period hPeriod frame baseMetric variation ghost)

/-- Global joint smoothness needs neither metric inversion nor an admissibility hypothesis. -/
theorem finiteFrameC2CartanFirstJet_contDiff :
    ContDiff Real ∞ (fun input : MetricCore × GhostCore =>
      finiteFrameC2CartanFirstJet period hPeriod frame baseMetric input.1 input.2) := by
  let Input := MetricCore × GhostCore
  have hG (i j : Fin frame.count) : ContDiff Real ∞ (fun input : Input =>
      finiteFrameMetricC0Coefficient period hPeriod frame baseMetric i j input.1) :=
    (finiteFrameMetricC0Coefficient_contDiff period hPeriod frame baseMetric i j).comp contDiff_fst
  have hDG (a i j : Fin frame.count) : ContDiff Real ∞ (fun input : Input =>
      finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric a i j input.1) :=
    (finiteFrameMetricC0FirstDerivative_contDiff period hPeriod frame baseMetric a i j).comp contDiff_fst
  have hDDG (a b i j : Fin frame.count) : ContDiff Real ∞ (fun input : Input =>
      metricSecondDerivative period hPeriod frame baseMetric a b i j input.1) :=
    (finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame a b).contDiff.comp
      (((contDiff_apply Real (C2Scalar period hPeriod) j).comp
        ((contDiff_apply Real (Fin frame.count → C2Scalar period hPeriod) i).comp
          (finiteFrameMetricC2Coefficients_contDiff period hPeriod frame baseMetric))).comp contDiff_fst)
  have hGhost (a : Fin frame.count) : ContDiff Real ∞ (fun input : Input => input.2 a) :=
    (contDiff_apply Real (C2Scalar period hPeriod) a).comp contDiff_snd
  have hC (a : Fin frame.count) : ContDiff Real ∞ (fun input : Input =>
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (input.2 a)) :=
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp (hGhost a)
  have hDC (i a : Fin frame.count) : ContDiff Real ∞ (fun input : Input =>
      finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame i (input.2 a)) :=
    (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame i).contDiff.comp (hGhost a)
  have hDDC (i j a : Fin frame.count) : ContDiff Real ∞ (fun input : Input =>
      finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame i j (input.2 a)) :=
    (finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame i j).contDiff.comp (hGhost a)
  unfold finiteFrameC2CartanFirstJet
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro first
    apply contDiff_pi.mpr
    intro second
    dsimp only [finiteFrameC2CartanComponentExpression]
    apply ContDiff.sum
    intro a _
    apply ContDiff.sub
    · exact (((hC a).mul (hDG a first second)).add
        ((hDC first a).mul (hG a second))).add ((hDC second a).mul (hG first a))
    · apply ContDiff.sum
      intro b _
      exact (((hC a).mul contDiff_const).mul (hG b second)).add
        (((hC a).mul contDiff_const).mul (hG first b))
  · apply contDiff_pi.mpr
    intro outer
    apply contDiff_pi.mpr
    intro first
    apply contDiff_pi.mpr
    intro second
    dsimp only [finiteFrameC2CartanComponentFirstDerivative]
    apply ContDiff.sum
    intro a _
    apply ContDiff.sub
    · exact ((((hDC outer a).mul (hDG a first second)).add ((hC a).mul (hDDG outer a first second))).add
        (((hDDC outer first a).mul (hG a second)).add ((hDC first a).mul (hDG outer a second)))).add
          (((hDDC outer second a).mul (hG first a)).add ((hDC second a).mul (hDG outer first a)))
    · apply ContDiff.sum
      intro b _
      exact (((((hDC outer a).mul contDiff_const).mul (hG b second)).add
        (((hC a).mul contDiff_const).mul (hG b second))).add
          (((hC a).mul contDiff_const).mul (hDG outer b second))).add
            (((((hDC outer a).mul contDiff_const).mul (hG first b)).add
              (((hC a).mul contDiff_const).mul (hG first b))).add
                (((hC a).mul contDiff_const).mul (hDG outer first b)))

private theorem scalarFrameGhost_bracket
    (scalar : Scalar period hPeriod) (direction test : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (cInfinityScalarSmulGhost period hPeriod (analyticScalarToCInfinity period hPeriod scalar)
          (smoothFrameVectorSection period hPeriod frame direction))
        (smoothFrameVectorSection period hPeriod frame test) point =
      -(frameDerivative period hPeriod Real frame scalar point test) • frame.vectorAt point direction +
        scalar point • smoothGhostLieBracket period hPeriod
          (smoothFrameVectorSection period hPeriod frame direction)
          (smoothFrameVectorSection period hPeriod frame test) point :=
  VectorField.mlieBracket_smul_left (scalar.contMDiff_toFun.mdifferentiableAt (by simp))
    ((smoothFrameVectorSection period hPeriod frame direction).contMDiff.mdifferentiableAt (by simp))

private theorem scalarFrameGhost_cartanCoefficient
    (scalar : Scalar period hPeriod) (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (a first second : Fin frame.count) :
    generalMetricFrameCoefficient period hPeriod frame
        (smoothMetricCartanAction period hPeriod
          (cInfinityScalarSmulGhost period hPeriod (analyticScalarToCInfinity period hPeriod scalar)
            (smoothFrameVectorSection period hPeriod frame a)) tensor) first second point =
      scalar point * frameDerivative period hPeriod Real frame
          (generalMetricFrameCoefficient period hPeriod frame tensor first second) point a +
        frameDerivative period hPeriod Real frame scalar point first *
          generalMetricFrameCoefficient period hPeriod frame tensor a second point +
        frameDerivative period hPeriod Real frame scalar point second *
          generalMetricFrameCoefficient period hPeriod frame tensor first a point -
        ∑ b : Fin frame.count,
          (scalar point * finiteFrameStructureCoefficient period hPeriod frame baseMetric a first b point *
            generalMetricFrameCoefficient period hPeriod frame tensor b second point +
          scalar point * finiteFrameStructureCoefficient period hPeriod frame baseMetric a second b point *
            generalMetricFrameCoefficient period hPeriod frame tensor first b point) := by
  change (smoothMetricCartanAction period hPeriod
    (cInfinityScalarSmulGhost period hPeriod (analyticScalarToCInfinity period hPeriod scalar)
      (smoothFrameVectorSection period hPeriod frame a)) tensor).tensor point
      ((smoothFrameVectorSection period hPeriod frame first) point)
      ((smoothFrameVectorSection period hPeriod frame second) point) = _
  rw [smoothMetricCartanAction_apply]
  unfold metricCartanResidualAt
  change mvfderiv coverModelWithCorners
      (generalMetricFrameCoefficient period hPeriod frame tensor first second).toFun
      point (scalar point • frame.vectorAt point a) -
    tensor.tensor point
      (smoothGhostLieBracket period hPeriod
        (cInfinityScalarSmulGhost period hPeriod (analyticScalarToCInfinity period hPeriod scalar)
          (smoothFrameVectorSection period hPeriod frame a))
        (smoothFrameVectorSection period hPeriod frame first) point) (frame.vectorAt point second) -
    tensor.tensor point (frame.vectorAt point first)
      (smoothGhostLieBracket period hPeriod
        (cInfinityScalarSmulGhost period hPeriod (analyticScalarToCInfinity period hPeriod scalar)
          (smoothFrameVectorSection period hPeriod frame a))
        (smoothFrameVectorSection period hPeriod frame second) point) = _
  rw [map_smul, scalarFrameGhost_bracket, scalarFrameGhost_bracket,
    finiteFrameStructureCoefficient_reconstructs period hPeriod frame baseMetric,
    finiteFrameStructureCoefficient_reconstructs period hPeriod frame baseMetric]
  simp only [map_add, map_sum, map_smul, add_apply, sum_apply, smul_apply, smul_eq_mul]
  change scalar point * frameDerivative period hPeriod Real frame
      (generalMetricFrameCoefficient period hPeriod frame tensor first second) point a -
    (-(frameDerivative period hPeriod Real frame scalar point first) *
        generalMetricFrameCoefficient period hPeriod frame tensor a second point +
      scalar point * ∑ b : Fin frame.count,
        finiteFrameStructureCoefficient period hPeriod frame baseMetric a first b point *
          generalMetricFrameCoefficient period hPeriod frame tensor b second point) -
    (-(frameDerivative period hPeriod Real frame scalar point second) *
        generalMetricFrameCoefficient period hPeriod frame tensor first a point +
      scalar point * ∑ b : Fin frame.count,
        finiteFrameStructureCoefficient period hPeriod frame baseMetric a second b point *
          generalMetricFrameCoefficient period hPeriod frame tensor first b point) = _
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- Intrinsic Cartan formula for any smooth coefficients in the redundant family. -/
theorem smoothMetricCartanAction_finiteFrameCoefficient
    (coefficients : Fin frame.count → Scalar period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (first second : Fin frame.count) :
    generalMetricFrameCoefficient period hPeriod frame
        (smoothMetricCartanAction period hPeriod
          (finiteFrameVectorFromSmoothCoefficients period hPeriod frame coefficients) tensor)
        first second point =
      ∑ a : Fin frame.count,
        (coefficients a point * frameDerivative period hPeriod Real frame
            (generalMetricFrameCoefficient period hPeriod frame tensor first second) point a +
          frameDerivative period hPeriod Real frame (coefficients a) point first *
            generalMetricFrameCoefficient period hPeriod frame tensor a second point +
          frameDerivative period hPeriod Real frame (coefficients a) point second *
            generalMetricFrameCoefficient period hPeriod frame tensor first a point -
          ∑ b : Fin frame.count,
            (coefficients a point * finiteFrameStructureCoefficient period hPeriod frame baseMetric a first b point *
              generalMetricFrameCoefficient period hPeriod frame tensor b second point +
            coefficients a point * finiteFrameStructureCoefficient period hPeriod frame baseMetric a second b point *
              generalMetricFrameCoefficient period hPeriod frame tensor first b point)) := by
  let evaluation : CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real] Real :=
    { toFun := fun ghost => generalMetricFrameCoefficient period hPeriod frame
        (smoothMetricCartanAction period hPeriod ghost tensor) first second point
      map_add' := by intros; rw [smoothMetricCartanAction_add_acting]; rfl
      map_smul' := by intros; rw [smoothMetricCartanAction_smul_acting]; rfl }
  change evaluation (∑ a : Fin frame.count,
    cInfinityScalarSmulGhost period hPeriod (analyticScalarToCInfinity period hPeriod (coefficients a))
      (smoothFrameVectorSection period hPeriod frame a)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact scalarFrameGhost_cartanCoefficient period hPeriod frame baseMetric (coefficients a)
    tensor point a first second

private theorem scalarSum_apply (fields : Fin frame.count → Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ a, fields a) point = ∑ a, fields a point := by
  let evaluation : Scalar period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation fields Finset.univ

private theorem scalarAdd_apply (first second : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) : (first + second) point = first point + second point := rfl
private theorem scalarSub_apply (first second : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) : (first - second) point = first point - second point := rfl
private theorem scalarContinuous_apply (field : Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothToCanonicalPhysicalContinuousScalar period hPeriod field point = field point := rfl
private theorem frameComponent_apply (field : Scalar period hPeriod) (index : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    frameDerivativeComponentField period hPeriod frame field index point =
      frameDerivative period hPeriod Real frame field point index := rfl

private def frameDEval (point : EffectiveQuotient period hPeriod) (index : Fin frame.count) :
    Scalar period hPeriod →ₗ[Real] Real where
  toFun field := frameDerivative period hPeriod Real frame field point index
  map_add' first second := by
    have h := congrFun (congrFun (frameDerivative_add period hPeriod Real frame first second) point) index
    simpa only [Pi.add_apply] using h
  map_smul' scalar field := by
    have h := congrFun (congrFun (frameDerivative_smul period hPeriod Real frame scalar field) point) index
    simpa only [Pi.smul_apply, RingHom.id_apply] using h

private theorem frameDEval_apply (point : EffectiveQuotient period hPeriod) (index : Fin frame.count)
    (field : Scalar period hPeriod) :
    frameDEval period hPeriod frame point index field =
      frameDerivative period hPeriod Real frame field point index := rfl

private theorem frameDEval_mul (point : EffectiveQuotient period hPeriod) (index : Fin frame.count)
    (first second : Scalar period hPeriod) :
    frameDEval period hPeriod frame point index (smoothScalarFieldMul period hPeriod first second) =
      first point * frameDEval period hPeriod frame point index second +
        second point * frameDEval period hPeriod frame point index first :=
  congrFun (congrFun (frameDerivative_mul period hPeriod frame first second) point) index

private def smoothCartanCoefficientFormula
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin frame.count → Scalar period hPeriod) (first second : Fin frame.count) :
    Scalar period hPeriod :=
  let g := generalMetricFrameCoefficient period hPeriod frame tensor
  let d := fun field index => frameDerivativeComponentField period hPeriod frame field index
  let mul := smoothScalarFieldMul period hPeriod
  let bracket := finiteFrameStructureCoefficient period hPeriod frame baseMetric
  ∑ a : Fin frame.count,
    (mul (coefficients a) (d (g first second) a) + mul (d (coefficients a) first) (g a second) +
      mul (d (coefficients a) second) (g first a) -
      ∑ b : Fin frame.count,
        (mul (mul (coefficients a) (bracket a first b)) (g b second) +
          mul (mul (coefficients a) (bracket a second b)) (g first b)))

private theorem smoothCartanCoefficient_eq_formula
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin frame.count → Scalar period hPeriod) (first second : Fin frame.count) :
    generalMetricFrameCoefficient period hPeriod frame
        (smoothMetricCartanAction period hPeriod
          (finiteFrameVectorFromSmoothCoefficients period hPeriod frame coefficients) tensor) first second =
      smoothCartanCoefficientFormula period hPeriod frame baseMetric tensor coefficients first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simpa only [smoothCartanCoefficientFormula, scalarSum_apply, scalarAdd_apply, scalarSub_apply,
    smoothScalarFieldMul_apply, frameComponent_apply] using
    smoothMetricCartanAction_finiteFrameCoefficient period hPeriod frame baseMetric coefficients
      tensor point first second

theorem finiteFrameC2CartanComponentExpression_smooth
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variationTensor)
    (coefficients : Fin frame.count → Scalar period hPeriod) (first second : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameC2CartanComponentExpression period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variationTensor)
        (fun a => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients a)) first second point =
      generalMetricFrameCoefficient period hPeriod frame
        (smoothMetricCartanAction period hPeriod
          (finiteFrameVectorFromSmoothCoefficients period hPeriod frame coefficients) metric.tensor)
        first second point := by
  simp only [finiteFrameC2CartanComponentExpression, finiteFrameMetricC0Coefficient,
    finiteFrameMetricC0FirstDerivative,
    finiteFrameMetricC2Coefficients_smooth period hPeriod frame baseMetric variationTensor metric hMetric,
    smoothGeneralMetricTensorToC2Matrix_apply, ContinuousMap.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.mul_apply, canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    finiteFrameScalarC2FirstDerivative_smooth, finiteFrameStructureC0Coefficient, scalarContinuous_apply]
  exact (smoothMetricCartanAction_finiteFrameCoefficient period hPeriod frame baseMetric coefficients
    metric.tensor point first second).symm

theorem finiteFrameC2CartanComponentFirstDerivative_smooth
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variationTensor)
    (coefficients : Fin frame.count → Scalar period hPeriod) (outer first second : Fin frame.count)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameC2CartanComponentFirstDerivative period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variationTensor)
        (fun a => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients a)) outer first second point =
      frameDerivative period hPeriod Real frame
        (generalMetricFrameCoefficient period hPeriod frame
          (smoothMetricCartanAction period hPeriod
            (finiteFrameVectorFromSmoothCoefficients period hPeriod frame coefficients) metric.tensor)
          first second) point outer := by
  rw [smoothCartanCoefficient_eq_formula period hPeriod frame baseMetric]
  change _ = frameDEval period hPeriod frame point outer
    (smoothCartanCoefficientFormula period hPeriod frame baseMetric metric.tensor coefficients first second)
  simp only [smoothCartanCoefficientFormula, map_sum, map_add, map_sub,
    frameDEval_mul, smoothScalarFieldMul_apply]
  simp only [finiteFrameC2CartanComponentFirstDerivative, finiteFrameMetricC0Coefficient,
    finiteFrameMetricC0FirstDerivative, metricSecondDerivative,
    finiteFrameMetricC2Coefficients_smooth period hPeriod frame baseMetric variationTensor metric hMetric,
    smoothGeneralMetricTensorToC2Matrix_apply, ContinuousMap.sum_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.mul_apply, canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    finiteFrameScalarC2FirstDerivative_smooth, finiteFrameScalarC2SecondDerivative_smooth,
    finiteFrameStructureC0Coefficient, bracketDerivative, scalarContinuous_apply,
    frameDEval_apply, frameComponent_apply, frameSecondDerivative]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg₂ (fun left right : Real => left - right)
  · ring
  · apply Finset.sum_congr rfl
    intro b _
    ring

/-- The values and spatial first derivatives of an actual smooth tensor. -/
def finiteFrameSmoothTensorFirstJet (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    FiniteFrameCartanC0FirstJet period hPeriod frame :=
  (fun first second => smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (generalMetricFrameCoefficient period hPeriod frame tensor first second),
    fun outer first second => smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame tensor first second) outer))

theorem finiteFrameC2CartanFirstJet_smooth
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variationTensor)
    (coefficients : Fin frame.count → Scalar period hPeriod) :
    finiteFrameC2CartanFirstJet period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variationTensor)
        (fun a => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients a)) =
      finiteFrameSmoothTensorFirstJet period hPeriod frame
        (smoothMetricCartanAction period hPeriod
          (finiteFrameVectorFromSmoothCoefficients period hPeriod frame coefficients) metric.tensor) := by
  apply Prod.ext
  · funext first second
    apply ContinuousMap.ext
    intro point
    exact finiteFrameC2CartanComponentExpression_smooth period hPeriod frame baseMetric
      variationTensor metric hMetric coefficients first second point
  · funext outer first second
    apply ContinuousMap.ext
    intro point
    exact finiteFrameC2CartanComponentFirstDerivative_smooth period hPeriod frame baseMetric
      variationTensor metric hMetric coefficients outer first second point

/-- Canonical coefficients retain the same geometric ghost in the completed first jet. -/
theorem finiteFrameC2CartanFirstJet_smooth_canonical
    (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variationTensor)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    finiteFrameC2CartanFirstJet period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variationTensor)
        (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame baseMetric ghost) =
      finiteFrameSmoothTensorFirstJet period hPeriod frame
        (smoothMetricCartanAction period hPeriod ghost metric.tensor) := by
  unfold finiteFrameSmoothDiffeomorphismC2Coefficients
  rw [finiteFrameC2CartanFirstJet_smooth period hPeriod frame baseMetric variationTensor metric hMetric,
    finiteFrameVectorFromSmoothCoefficients_reconstructs]

end
end P0EFTJanusFiniteFrameC2CartanFirstJet4D
end JanusFormal
