import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryConnectionEvaluation4D

/-! Exact smooth agreement of moving-graph evaluations with the native
finite-frame Koszul connection. Raw first jets are identified on smooth
coefficients before using the native reconstructed directional derivative. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryConnectionSmooth4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameMetricContraction4D P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryMetricFirstEvaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
open P0EFTJanusProgramPT12FrameFreeBoundaryConnectionEvaluation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real

theorem frameFreeBoundaryActualMetricCoefficient_eq_native (row column : Index) (current : Input) :
    frameFreeBoundaryActualMetricCoefficient period hPeriod metric row column current.1.1 =
      finiteFrameMetricC2Coefficients period hPeriod frame metric
        (frameFreeBoundaryAmbientCore period hPeriod metric current) row column := rfl

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

include hVaried in
theorem frameFreeBoundaryActualMetricCoefficient_smooth (row column : Index) :
    frameFreeBoundaryActualMetricCoefficient period hPeriod metric row column
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)).1 =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (generalMetricFrameCoefficient period hPeriod frame variedMetric.tensor row column) := by
  have hNative := frameFreeBoundaryActualMetricCoefficient_eq_native period hPeriod metric row column
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), 0)
  apply hNative.trans
  change finiteFrameMetricC2Coefficients period hPeriod frame metric
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor) row column = _
  exact congrFun (congrFun
    (finiteFrameMetricC2Coefficients_smooth period hPeriod frame metric tensor variedMetric hVaried) row) column

include hVaried in
theorem frameFreeBoundaryConnectionMetricEvaluation_smooth (row column : Index) (boundary : Boundary) :
    frameFreeBoundaryActualMetricEvaluation period hPeriod metric row column
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      generalMetricFrameCoefficient period hPeriod frame variedMetric.tensor row column
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  rw [frameFreeBoundaryActualMetricEvaluation_eq_valueJet,
    frameFreeBoundaryActualMetricCoefficient_smooth period hPeriod metric tensor variedMetric hVaried displacement]
  change generalMetricFrameCoefficient period hPeriod frame variedMetric.tensor row column
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth]

include hVaried in
theorem frameFreeBoundaryActualMetricFirstEvaluation_smooth (row column spatial : Index) (boundary : Boundary) :
    frameFreeBoundaryActualMetricFirstEvaluation period hPeriod metric row column spatial
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      frameDerivative period hPeriod Real frame
        (generalMetricFrameCoefficient period hPeriod frame variedMetric.tensor row column)
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) spatial := by
  rw [frameFreeBoundaryActualMetricFirstEvaluation_eq_firstJet,
    frameFreeBoundaryActualMetricCoefficient_smooth period hPeriod metric tensor variedMetric hVaried displacement]
  change frameDerivative period hPeriod Real frame
    (generalMetricFrameCoefficient period hPeriod frame variedMetric.tensor row column)
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) spatial = _
  rw [normalBoundaryC2Graph_smooth]

private theorem structureEvaluation_smooth (first second upper : Index) (boundary : Boundary) :
    frameFreeBoundaryStructureEvaluation period hPeriod metric first second upper
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      finiteFrameStructureCoefficient period hPeriod frame metric first second upper
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  rw [frameFreeBoundaryStructureEvaluation_apply]
  change finiteFrameStructureCoefficient period hPeriod frame metric first second upper
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth]

include hVaried in
theorem frameFreeBoundaryKoszulLowerEvaluation_smooth (first second lower : Index) (boundary : Boundary) :
    frameFreeBoundaryKoszulLowerEvaluation period hPeriod metric first second lower
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      finiteFrameKoszulLowerCoefficient period hPeriod frame metric variedMetric first second lower
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  have hMetric := frameFreeBoundaryConnectionMetricEvaluation_smooth period hPeriod metric
    tensor variedMetric hVaried displacement parameter
  have hDerivative := frameFreeBoundaryActualMetricFirstEvaluation_smooth period hPeriod metric
    tensor variedMetric hVaried displacement parameter
  have hStructure := structureEvaluation_smooth period hPeriod metric tensor displacement parameter
  rw [finiteFrameKoszulLowerCoefficient_apply]
  simp only [frameFreeBoundaryKoszulLowerEvaluation, frameFreeBoundaryStructureMetricEvaluation,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply, hMetric, hDerivative, hStructure, smul_eq_mul]

include hVaried in
/-- Genuine smooth Koszul connection, hence the native local Levi-Civita connection. -/
theorem frameFreeBoundaryConnectionEvaluation_smooth
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (upper first second : Index) (boundary : Boundary) :
    frameFreeBoundaryConnectionEvaluation period hPeriod metric upper first second
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric variedMetric upper first second
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  rw [finiteFrameKoszulChristoffelCoefficient_apply]
  simp only [frameFreeBoundaryConnectionEvaluation, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  apply congrArg₂ (fun first second : Real => first * second)
  · simpa only [finiteFrameInverseMetricCoefficient_apply] using
      frameFreeBoundaryAmbientInverseEvaluation_smooth period hPeriod metric tensor variedMetric hVaried
        displacement parameter hCurrent upper lower boundary
  · exact frameFreeBoundaryKoszulLowerEvaluation_smooth period hPeriod metric tensor variedMetric hVaried
      displacement parameter first second lower boundary

include hVaried in
theorem frameFreeBoundaryConnectionEvaluation_smooth_eq_native
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (upper first second : Index) (boundary : Boundary) :
    frameFreeBoundaryConnectionEvaluation period hPeriod metric upper first second
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      finiteFrameChristoffelC0Coefficient period hPeriod frame metric upper first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor)
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  have hDomain : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame metric := hCurrent
  have hNative := congrArg (fun field : C(Q period hPeriod, Real) =>
      field (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)))
    (finiteFrameChristoffelC0Coefficient_smooth period hPeriod frame metric tensor variedMetric hVaried
      hDomain upper first second)
  exact (frameFreeBoundaryConnectionEvaluation_smooth period hPeriod metric tensor variedMetric hVaried
    displacement parameter hCurrent upper first second boundary).trans hNative.symm

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryConnectionSmooth4D
