import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryScalarC2Evaluation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D

/-! The existing faithful C² inverse metric, evaluated on the same moving graph.
No ambient Gram matrix is inverted. The domain contains the zero field at parameter one. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryScalarC2Evaluation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : TopologicalSpace.MetrizableSpace Boundary := Manifold.metrizableSpace throatCoverModelWithCorners _
local instance : MetricSpace Boundary := TopologicalSpace.metrizableSpaceMetric _
local notation "Scalar" => CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : NormedAddCommGroup Scalar := (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real Scalar := inferInstance
local instance : CompleteSpace Scalar := canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Joint" => FrameFreeBoundaryJointCore period hPeriod frame metric
local notation "Input" => Joint × Real
local notation "Graph" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryAmbientCore (current : Input) : Model :=
  frameFreeBoundaryC3CoreToC2 period hPeriod frame metric current.1.1

theorem frameFreeBoundaryAmbientCore_contDiff :
    ContDiff Real ∞ (frameFreeBoundaryAmbientCore period hPeriod metric) :=
  (frameFreeBoundaryC3CoreToC2 period hPeriod frame metric).contDiff.comp (contDiff_fst.comp contDiff_fst)

def frameFreeBoundaryAmbientDomain : Set Input :=
  frameFreeBoundaryAmbientCore period hPeriod metric ⁻¹' generalMetricRelativeC2OpenDomain period hPeriod frame metric

theorem frameFreeBoundaryAmbientDomain_isOpen : IsOpen (frameFreeBoundaryAmbientDomain period hPeriod metric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame metric).preimage
    (frameFreeBoundaryAmbientCore_contDiff period hPeriod metric).continuous

theorem zero_mem_frameFreeBoundaryAmbientDomain (parameter : Real) :
    ((0 : Joint), parameter) ∈ frameFreeBoundaryAmbientDomain period hPeriod metric := by
  change (0 : Model) ∈ generalMetricRelativeC2OpenDomain period hPeriod frame metric
  exact zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric

private def inverseEntry (row column : Index) (current : Input) : Scalar :=
  finiteFrameInverseMetricC2Coefficients period hPeriod frame metric
    (frameFreeBoundaryAmbientCore period hPeriod metric current) row column

private theorem inverseEntry_contDiffOn_two (row column : Index) :
    ContDiffOn Real 2 (inverseEntry period hPeriod metric row column)
      (frameFreeBoundaryAmbientDomain period hPeriod metric) := by
  have hInverse : ContDiffOn Real ∞
      (fun current : Input => finiteFrameInverseMetricC2Coefficients period hPeriod frame metric
        (frameFreeBoundaryAmbientCore period hPeriod metric current))
      (frameFreeBoundaryAmbientDomain period hPeriod metric) :=
    (finiteFrameInverseMetricC2Coefficients_contDiffOn period hPeriod frame metric).comp
      (frameFreeBoundaryAmbientCore_contDiff period hPeriod metric).contDiffOn (fun _ hCurrent => hCurrent)
  have hRow := (contDiff_apply Real (Index → Scalar) row).comp_contDiffOn hInverse
  exact ((contDiff_apply Real Scalar column).comp_contDiffOn hRow).of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

def frameFreeBoundaryAmbientInverseEvaluation (row column : Index) (current : Input) : Graph :=
  frameFreeBoundaryScalarC2Evaluation period hPeriod metric
    (inverseEntry period hPeriod metric row column current,
      normalBoundaryC2ScaledRawGraph period hPeriod (frameFreeBoundaryNormalInput period hPeriod metric current))

theorem frameFreeBoundaryAmbientInverseEvaluation_contDiffOn_two (row column : Index) :
    ContDiffOn Real 2 (frameFreeBoundaryAmbientInverseEvaluation period hPeriod metric row column)
      (frameFreeBoundaryAmbientDomain period hPeriod metric) :=
  (frameFreeBoundaryScalarC2Evaluation_contDiff_two period hPeriod metric).comp_contDiffOn
    ((inverseEntry_contDiffOn_two period hPeriod metric row column).prodMk
      (((normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod).comp
        (frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric)).contDiffOn))

theorem frameFreeBoundaryAmbientInverseEvaluation_apply (row column : Index)
    (current : Input) (boundary : Boundary) :
    frameFreeBoundaryAmbientInverseEvaluation period hPeriod metric row column current boundary =
      finiteFrameInverseMetricC0Coefficient period hPeriod frame metric row column
        (frameFreeBoundaryAmbientCore period hPeriod metric current)
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2 boundary) := by
  unfold frameFreeBoundaryAmbientInverseEvaluation
  rw [frameFreeBoundaryScalarC2Evaluation_apply]
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (inverseEntry period hPeriod metric row column current)
    (normalBoundaryLatitudeFiberPoint period hPeriod boundary
      (normalBoundaryC2LatitudeGraph period hPeriod (current.1.2, current.2) boundary)) = _
  rw [normalBoundaryLatitudeFiberPoint_graph]
  rfl

theorem frameFreeBoundaryAmbientInverseEvaluation_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (row column : Index) (boundary : Boundary) :
    let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
    frameFreeBoundaryAmbientInverseEvaluation period hPeriod metric row column
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      inverseMetricContraction period hPeriod variedMetric point
        (generalMetricFiniteFrameCoefficientAt period hPeriod frame metric point row)
        (generalMetricFiniteFrameCoefficientAt period hPeriod frame metric point column) := by
  dsimp only
  have hCore : frameFreeBoundaryAmbientCore period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) =
      smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor := rfl
  have hDomain : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame metric := by
    change frameFreeBoundaryAmbientCore period hPeriod metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
        generalMetricRelativeC2OpenDomain period hPeriod frame metric at hCurrent
    rwa [hCore] at hCurrent
  rw [frameFreeBoundaryAmbientInverseEvaluation_apply, hCore,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame metric tensor variedMetric hVaried hDomain row column]
  change finiteFrameInverseMetricCoefficient period hPeriod frame metric variedMetric row column
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth, finiteFrameInverseMetricCoefficient_apply]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
