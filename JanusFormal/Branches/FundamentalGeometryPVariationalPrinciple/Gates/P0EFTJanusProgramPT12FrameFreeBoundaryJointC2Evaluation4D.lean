import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryRawSecondJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundarySpatialFirstJet4D

/-! The existing joint metric/normal graph evaluations are genuinely C².
The raw graph is the already constructed normal graph, with exact pointwise agreement. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryJointC2Evaluation4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryRawSecondJet4D
open P0EFTJanusProgramPT12FrameFreeBoundarySpatialFirstJet4D

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
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Core" => FrameFreeBoundaryC3Core period hPeriod frame metric
local notation "Joint" => FrameFreeBoundaryJointCore period hPeriod frame metric
local notation "Graph" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryJointFiberInput (current : Joint × Real) : Core × Graph :=
  (current.1.1, normalBoundaryC2ScaledRawGraph period hPeriod (current.1.2, current.2))

theorem frameFreeBoundaryJointFiberInput_contDiff_two :
    ContDiff Real 2 (frameFreeBoundaryJointFiberInput period hPeriod metric) := by
  have hMetric : ContDiff Real 2 (fun current : Joint × Real => current.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hNormal : ContDiff Real 2 (fun current : Joint × Real => current.1.2) :=
    contDiff_snd.comp contDiff_fst
  exact hMetric.prodMk ((normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod).comp
    (hNormal.prodMk contDiff_snd))

def frameFreeBoundaryJointValueEvaluation (row column : Index) (current : Joint × Real) : Graph :=
  frameFreeBoundaryValueEvaluation period hPeriod metric row column
    (frameFreeBoundaryJointFiberInput period hPeriod metric current)

def frameFreeBoundaryJointFirstEvaluation (row column spatial : Index) (current : Joint × Real) : Graph :=
  frameFreeBoundarySpatialFirstEvaluation period hPeriod metric row column spatial
    (frameFreeBoundaryJointFiberInput period hPeriod metric current)

theorem frameFreeBoundaryJointValueEvaluation_contDiff_two (row column : Index) :
    ContDiff Real 2 (frameFreeBoundaryJointValueEvaluation period hPeriod metric row column) :=
  (frameFreeBoundaryValueEvaluation_contDiff_two period hPeriod metric row column).comp
    (frameFreeBoundaryJointFiberInput_contDiff_two period hPeriod metric)

theorem frameFreeBoundaryJointFirstEvaluation_contDiff_two (row column spatial : Index) :
    ContDiff Real 2 (frameFreeBoundaryJointFirstEvaluation period hPeriod metric row column spatial) :=
  (frameFreeBoundarySpatialFirstEvaluation_contDiff_two period hPeriod metric row column spatial).comp
    (frameFreeBoundaryJointFiberInput_contDiff_two period hPeriod metric)

private theorem jointFiberInput_point (variation : Joint) (parameter : Real) (boundary : Boundary) :
    normalBoundaryLatitudeFiberPoint period hPeriod boundary
      (Real.arctan ((frameFreeBoundaryJointFiberInput period hPeriod metric (variation, parameter)).2 boundary)) =
      normalBoundaryC2Graph period hPeriod variation.2 parameter boundary := by
  change normalBoundaryLatitudeFiberPoint period hPeriod boundary
    (normalBoundaryC2LatitudeGraph period hPeriod (variation.2, parameter) boundary) = _
  exact normalBoundaryLatitudeFiberPoint_graph period hPeriod variation.2 parameter boundary

@[simp] theorem frameFreeBoundaryJointValueEvaluation_eq_atGraph (row column : Index)
    (variation : Joint) (parameter : Real) (boundary : Boundary) :
    frameFreeBoundaryJointValueEvaluation period hPeriod metric row column (variation, parameter) boundary =
      frameFreeBoundaryRelativeEntryAtGraph period hPeriod frame metric row column
        variation parameter boundary := by
  change frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column variation.1
    (normalBoundaryLatitudeFiberPoint period hPeriod boundary
      (Real.arctan ((frameFreeBoundaryJointFiberInput period hPeriod metric (variation, parameter)).2 boundary))) = _
  rw [jointFiberInput_point]
  rfl

@[simp] theorem frameFreeBoundaryJointFirstEvaluation_eq_atGraph (row column spatial : Index)
    (variation : Joint) (parameter : Real) (boundary : Boundary) :
    frameFreeBoundaryJointFirstEvaluation period hPeriod metric row column spatial (variation, parameter) boundary =
      frameFreeBoundaryRelativeFirstEntryAtGraph period hPeriod frame metric row column spatial
        variation parameter boundary := by
  change frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column spatial variation.1
    (normalBoundaryLatitudeFiberPoint period hPeriod boundary
      (Real.arctan ((frameFreeBoundaryJointFiberInput period hPeriod metric (variation, parameter)).2 boundary))) = _
  rw [jointFiberInput_point]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryJointC2Evaluation4D
