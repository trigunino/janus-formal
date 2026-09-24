import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

/-! The actual metric/normal completion and its continuous moving-graph evaluations.
The open domain below is the relative-metric domain; no GHY non-null or C²
substitution assertion is included in this continuity gate. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : CompactSpace (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local instance : CompleteSpace (NormalBoundaryC2JetCore period hPeriod) :=
  normalBoundaryC2JetCoreCompleteSpace period hPeriod
variable (frame : SmoothD8Frame period hPeriod)
  (metric : SmoothGeneralLorentzMetric period hPeriod)

abbrev FrameFreeBoundaryJointCore :=
  FrameFreeBoundaryC3Core period hPeriod frame metric × NormalBoundaryC2JetCore period hPeriod
local notation "Joint" => FrameFreeBoundaryJointCore period hPeriod frame metric
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "GraphInput" => (Joint × Real) × CutThroatBoundary period hPeriod

instance frameFreeBoundaryJointCoreNormedAddCommGroup : NormedAddCommGroup Joint := inferInstance
instance frameFreeBoundaryJointCoreNormedSpace : NormedSpace Real Joint := inferInstance
instance frameFreeBoundaryJointCoreCompleteSpace : CompleteSpace Joint := inferInstance

def smoothToFrameFreeBoundaryJointCore :
    (SmoothSymmetricCovariantTwoTensor period hPeriod × SmoothNormalDisplacement period hPeriod)
      →ₗ[Real] Joint :=
  (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric).prodMap
    (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod)

theorem smoothToFrameFreeBoundaryJointCore_injective :
    Function.Injective (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric) := by
  intro first second hEqual
  apply Prod.ext
  · exact smoothToFrameFreeBoundaryC3Core_injective period hPeriod frame metric
      (congrArg Prod.fst hEqual)
  · exact smoothNormalDisplacementToBoundaryC2JetCore_injective period hPeriod
      (congrArg Prod.snd hEqual)

theorem smoothToFrameFreeBoundaryJointCore_denseRange :
    DenseRange (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric) := by
  change DenseRange (Prod.map (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric)
    (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod))
  exact (smoothToFrameFreeBoundaryC3Core_denseRange period hPeriod frame metric).prodMap
    (smoothNormalDisplacementToBoundaryC2JetCore_denseRange period hPeriod)

def frameFreeBoundaryJointMetricProjection :
    Joint →L[Real] FrameFreeBoundaryC3Core period hPeriod frame metric :=
  ContinuousLinearMap.fst Real _ _

def frameFreeBoundaryJointNormalProjection : Joint →L[Real] NormalBoundaryC2JetCore period hPeriod :=
  ContinuousLinearMap.snd Real _ _

def frameFreeBoundaryJointDomain : Set Joint :=
  Prod.fst ⁻¹' frameFreeBoundaryC3Domain period hPeriod frame metric

theorem frameFreeBoundaryJointDomain_isOpen :
    IsOpen (frameFreeBoundaryJointDomain period hPeriod frame metric) :=
  (frameFreeBoundaryC3Domain_isOpen period hPeriod frame metric).preimage continuous_fst

theorem zero_mem_frameFreeBoundaryJointDomain :
    (0 : Joint) ∈ frameFreeBoundaryJointDomain period hPeriod frame metric :=
  zero_mem_frameFreeBoundaryC3Domain period hPeriod frame metric

theorem frameFreeBoundaryJointDomain_mem_nhds_zero :
    frameFreeBoundaryJointDomain period hPeriod frame metric ∈ 𝓝 (0 : Joint) :=
  (frameFreeBoundaryJointDomain_isOpen period hPeriod frame metric).mem_nhds
    (zero_mem_frameFreeBoundaryJointDomain period hPeriod frame metric)

private def metricGraphInput (current : GraphInput) :
    FrameFreeBoundaryC3Core period hPeriod frame metric × EffectiveQuotient period hPeriod :=
  (current.1.1.1, normalBoundaryC2Graph period hPeriod current.1.1.2 current.1.2 current.2)

private theorem metricGraphInput_continuous :
    Continuous (metricGraphInput period hPeriod frame metric) := by
  have hMetric : Continuous (fun current : GraphInput => current.1.1.1) :=
    continuous_fst.comp (continuous_fst.comp continuous_fst)
  have hNormal : Continuous (fun current : GraphInput => current.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp continuous_fst)
  have hParameter : Continuous (fun current : GraphInput => current.1.2) :=
    continuous_snd.comp continuous_fst
  have hBoundary : Continuous (fun current : GraphInput => current.2) := continuous_snd
  have hInput : Continuous (fun current : GraphInput =>
      (((current.1.1.2, current.1.2), current.2) :
        (NormalBoundaryC2JetCore period hPeriod × Real) × CutThroatBoundary period hPeriod)) :=
    (hNormal.prodMk hParameter).prodMk hBoundary
  have hGraph : Continuous (fun current : GraphInput =>
      normalBoundaryC2Graph period hPeriod current.1.1.2 current.1.2 current.2) := by
    exact Continuous.comp
      (f := fun current : GraphInput => ((current.1.1.2, current.1.2), current.2))
      (g := fun current : (NormalBoundaryC2JetCore period hPeriod × Real) ×
          CutThroatBoundary period hPeriod =>
        normalBoundaryC2Graph period hPeriod current.1.1 current.1.2 current.2)
      (normalBoundaryC2Graph_joint_continuous period hPeriod) hInput
  exact hMetric.prodMk hGraph

private theorem continuous_evaluate_at_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (evaluation : FrameFreeBoundaryC3Core period hPeriod frame metric →L[Real]
      C(EffectiveQuotient period hPeriod, E)) :
    Continuous (fun current : GraphInput => evaluation current.1.1.1
      (normalBoundaryC2Graph period hPeriod current.1.1.2 current.1.2 current.2)) := by
  have hInput := metricGraphInput_continuous period hPeriod frame metric
  have hMetric : Continuous (fun current : GraphInput => current.1.1.1) := hInput.fst
  have hGraph : Continuous (fun current : GraphInput =>
      normalBoundaryC2Graph period hPeriod current.1.1.2 current.1.2 current.2) := hInput.snd
  have hEvaluation : Continuous (fun current : GraphInput => evaluation current.1.1.1) :=
    Continuous.comp (f := fun current : GraphInput => current.1.1.1)
      (g := evaluation) evaluation.continuous hMetric
  exact hEvaluation.eval hGraph

def frameFreeBoundaryRelativeEntryAtGraph (row column : Fin frame.count)
    (variation : Joint) (parameter : Real) (boundary : CutThroatBoundary period hPeriod) : Real :=
  frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column variation.1
    (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

def frameFreeBoundaryRelativeFirstEntryAtGraph (row column : Fin frame.count) (index : Index)
    (variation : Joint) (parameter : Real) (boundary : CutThroatBoundary period hPeriod) : Real :=
  frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index
    variation.1 (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

def frameFreeBoundaryRelativeSecondEntryAtGraph
    (row column : Fin frame.count) (outer inner : Index)
    (variation : Joint) (parameter : Real) (boundary : CutThroatBoundary period hPeriod) : Real :=
  frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner
    variation.1 (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

def frameFreeBoundaryThirdJetAtGraph (variation : Joint) (parameter : Real)
    (boundary : CutThroatBoundary period hPeriod) : FrameFreeMetricThirdJetFiber period hPeriod frame :=
  frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric variation.1
    (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

theorem frameFreeBoundaryRelativeEntryAtGraph_joint_continuous (row column : Fin frame.count) :
    Continuous (fun current : GraphInput => frameFreeBoundaryRelativeEntryAtGraph
      period hPeriod frame metric row column current.1.1 current.1.2 current.2) := by
  unfold frameFreeBoundaryRelativeEntryAtGraph
  exact continuous_evaluate_at_graph period hPeriod frame metric
    (frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column)

theorem frameFreeBoundaryRelativeFirstEntryAtGraph_joint_continuous
    (row column : Fin frame.count) (index : Index) :
    Continuous (fun current : GraphInput => frameFreeBoundaryRelativeFirstEntryAtGraph
      period hPeriod frame metric row column index current.1.1 current.1.2 current.2) := by
  unfold frameFreeBoundaryRelativeFirstEntryAtGraph
  exact continuous_evaluate_at_graph period hPeriod frame metric
    (frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index)

theorem frameFreeBoundaryRelativeSecondEntryAtGraph_joint_continuous
    (row column : Fin frame.count) (outer inner : Index) :
    Continuous (fun current : GraphInput => frameFreeBoundaryRelativeSecondEntryAtGraph
      period hPeriod frame metric row column outer inner current.1.1 current.1.2 current.2) := by
  unfold frameFreeBoundaryRelativeSecondEntryAtGraph
  exact continuous_evaluate_at_graph period hPeriod frame metric
    (frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner)

theorem frameFreeBoundaryThirdJetAtGraph_joint_continuous :
    Continuous (fun current : GraphInput => frameFreeBoundaryThirdJetAtGraph
      period hPeriod frame metric current.1.1 current.1.2 current.2) := by
  unfold frameFreeBoundaryThirdJetAtGraph
  exact continuous_evaluate_at_graph period hPeriod frame metric
    (frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric)

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (displacement : SmoothNormalDisplacement period hPeriod)
  (parameter : Real) (boundary : CutThroatBoundary period hPeriod)

@[simp] theorem frameFreeBoundaryRelativeEntryAtGraph_smooth (row column : Fin frame.count) :
    frameFreeBoundaryRelativeEntryAtGraph period hPeriod frame metric row column
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement))
      parameter boundary =
    smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  change frameFreeBoundaryC3RelativeEntryAt period hPeriod frame metric row column
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary)
    (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) = _
  rw [normalBoundaryC2Graph_smooth, frameFreeBoundaryC3RelativeEntryAt_smooth]

@[simp] theorem frameFreeBoundaryRelativeFirstEntryAtGraph_smooth
    (row column : Fin frame.count) (index : Index) :
    frameFreeBoundaryRelativeFirstEntryAtGraph period hPeriod frame metric row column index
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement))
      parameter boundary =
    frameDerivative period hPeriod Real (finiteSmoothTangentFrame period hPeriod)
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) index := by
  change frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index
    (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor)
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth, frameFreeBoundaryC3RelativeFirstEntry_smooth]

@[simp] theorem frameFreeBoundaryRelativeSecondEntryAtGraph_smooth
    (row column : Fin frame.count) (outer inner : Index) :
    frameFreeBoundaryRelativeSecondEntryAtGraph period hPeriod frame metric row column outer inner
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement))
      parameter boundary =
    frameSecondDerivative period hPeriod (finiteSmoothTangentFrame period hPeriod)
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) outer inner := by
  change frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner
    (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor)
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth, frameFreeBoundaryC3RelativeSecondEntry_smooth]

@[simp] theorem frameFreeBoundaryThirdJetAtGraph_smooth :
    frameFreeBoundaryThirdJetAtGraph period hPeriod frame metric
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement))
      parameter boundary =
    smoothFrameFreeMetricThirdJet period hPeriod frame metric tensor
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) := by
  change frameFreeBoundaryC3ThirdJetAt period hPeriod frame metric
    (normalBoundaryC2Graph period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary)
    (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) = _
  rw [normalBoundaryC2Graph_smooth, frameFreeBoundaryC3ThirdJetAt_smooth]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
