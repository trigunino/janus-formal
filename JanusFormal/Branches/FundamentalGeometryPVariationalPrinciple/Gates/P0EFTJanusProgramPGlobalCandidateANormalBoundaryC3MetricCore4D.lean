import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

/-!
# Boundary-enhanced C³ metric core for Candidate A

The moving GHY graph evaluates first metric derivatives at moving points.
Twice differentiating that evaluation requires one additional spatial metric
jet.  This file closes the genuine smooth relative-metric image in the product
of the existing bulk `C²` core and its continuous ordered third frame jet.
The resulting Banach core projects continuously to the unchanged bulk chart;
its smooth inclusion is faithful and dense.  This is an analytic domain
refinement, not a metric ansatz or a physical axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

open scoped Manifold ContDiff Topology
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Ordered third derivatives in an existing finite smooth spanning frame. -/
def generalMetricFrameThirdDerivative
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    Fin frame.count → Fin frame.count → Fin frame.count → Real :=
  fun outer middle inner =>
    frameDerivative period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame
        (frameDerivativeComponentField period hPeriod frame field inner)
        middle) point outer

theorem generalMetricFrameThirdDerivative_contMDiff
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ContMDiff coverModelWithCorners
      𝓘(Real, Fin frame.count → Fin frame.count → Fin frame.count → Real) ∞
      (generalMetricFrameThirdDerivative period hPeriod frame field) := by
  rw [contMDiff_pi_space]
  intro outer
  rw [contMDiff_pi_space]
  intro middle
  rw [contMDiff_pi_space]
  intro inner
  exact (contMDiff_pi_space.mp
    (frameDerivative_contMDiff period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame
        (frameDerivativeComponentField period hPeriod frame field inner)
        middle))) outer

theorem generalMetricFrameThirdDerivative_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    generalMetricFrameThirdDerivative period hPeriod frame (first + second) =
      generalMetricFrameThirdDerivative period hPeriod frame first +
        generalMetricFrameThirdDerivative period hPeriod frame second := by
  funext point outer middle inner
  unfold generalMetricFrameThirdDerivative
  rw [frameDerivativeComponentField_add,
    frameDerivativeComponentField_add, frameDerivative_add]
  rfl

theorem generalMetricFrameThirdDerivative_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real) (field : SmoothQuotientField period hPeriod Real) :
    generalMetricFrameThirdDerivative period hPeriod frame (scalar • field) =
      scalar • generalMetricFrameThirdDerivative period hPeriod frame field := by
  funext point outer middle inner
  unfold generalMetricFrameThirdDerivative
  rw [frameDerivativeComponentField_smul,
    frameDerivativeComponentField_smul, frameDerivative_smul]
  rfl

private abbrev RegularMetricFrameIndex
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  Fin (regularGeneralLorentzMetricSmoothD8Frame
    period hPeriod metric).count

private abbrev RegularMetricThirdJetFiber
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  RegularMetricFrameIndex period hPeriod metric →
    RegularMetricFrameIndex period hPeriod metric →
      RegularMetricFrameIndex period hPeriod metric →
        RegularMetricFrameIndex period hPeriod metric →
          RegularMetricFrameIndex period hPeriod metric → Real

/-- Third frame jet of the same relative metric endomorphism used by the
bulk C² chart. -/
def smoothRegularGeneralMetricRelativeThirdJet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    RegularMetricThirdJetFiber period hPeriod metric :=
  fun row column outer middle inner =>
    generalMetricFrameThirdDerivative period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row column)
      point outer middle inner

theorem smoothRegularGeneralMetricRelativeThirdJet_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff coverModelWithCorners
      𝓘(Real, RegularMetricThirdJetFiber period hPeriod metric) ∞
      (smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric
        tensor) := by
  rw [contMDiff_pi_space]
  intro row
  rw [contMDiff_pi_space]
  intro column
  rw [contMDiff_pi_space]
  intro outer
  rw [contMDiff_pi_space]
  intro middle
  rw [contMDiff_pi_space]
  intro inner
  have hThird := generalMetricFrameThirdDerivative_contMDiff period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor row column)
  have hOuter := (contMDiff_pi_space.mp hThird) outer
  have hMiddle := (contMDiff_pi_space.mp hOuter) middle
  exact (contMDiff_pi_space.mp hMiddle) inner

theorem smoothRegularGeneralMetricRelativeThirdJet_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric
        (first + second) =
      smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric first +
        smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric
          second := by
  funext point row column outer middle inner
  unfold smoothRegularGeneralMetricRelativeThirdJet
  have hEntry := congrFun (congrFun
    (smoothGeneralMetricRelativeEndomorphismMatrix_add period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric first second) row) column
  rw [hEntry]
  exact congrFun (congrFun (congrFun (congrFun
    (generalMetricFrameThirdDerivative_add period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric first row column)
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric second row column)) point) outer) middle) inner

theorem smoothRegularGeneralMetricRelativeThirdJet_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric
        (scalar • tensor) =
      scalar • smoothRegularGeneralMetricRelativeThirdJet period hPeriod
        metric tensor := by
  funext point row column outer middle inner
  unfold smoothRegularGeneralMetricRelativeThirdJet
  have hEntry := congrFun (congrFun
    (smoothGeneralMetricRelativeEndomorphismMatrix_smul period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric scalar tensor) row) column
  rw [hEntry]
  exact congrFun (congrFun (congrFun (congrFun
    (generalMetricFrameThirdDerivative_smul period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) scalar
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row column)) point) outer) middle) inner

private abbrev RegularMetricThirdJetAmbient
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  C(EffectiveQuotient period hPeriod,
    RegularMetricThirdJetFiber period hPeriod metric)

def smoothRegularGeneralMetricRelativeThirdJetLinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      RegularMetricThirdJetAmbient period hPeriod metric where
  toFun tensor :=
    ⟨smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric tensor,
      (smoothRegularGeneralMetricRelativeThirdJet_contMDiff period hPeriod
        metric tensor).continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    exact congrFun
      (smoothRegularGeneralMetricRelativeThirdJet_add period hPeriod metric
        first second) point
  map_smul' scalar tensor := by
    apply ContinuousMap.ext
    intro point
    exact congrFun
      (smoothRegularGeneralMetricRelativeThirdJet_smul period hPeriod metric
        scalar tensor) point

local instance regularGeneralMetricC2CoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (RegularGeneralMetricC2Core period hPeriod metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric).normedAddCommGroup

local instance regularGeneralMetricC2CoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (RegularGeneralMetricC2Core period hPeriod metric) :=
  inferInstance

local instance regularGeneralMetricC2CoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace (RegularGeneralMetricC2Core period hPeriod metric) :=
  generalMetricRelativeC2CoreCompleteSpace period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric

private abbrev RegularMetricBoundaryC3Ambient
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod metric ×
    RegularMetricThirdJetAmbient period hPeriod metric

def smoothRegularGeneralMetricBoundaryC3LinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      RegularMetricBoundaryC3Ambient period hPeriod metric where
  toFun tensor :=
    (smoothToGeneralMetricRelativeC2Core period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor,
    smoothRegularGeneralMetricRelativeThirdJetLinearMap period hPeriod
      metric tensor)
  map_add' first second := by
    apply Prod.ext
    · exact (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric).map_add first second
    · exact (smoothRegularGeneralMetricRelativeThirdJetLinearMap period
        hPeriod metric).map_add first second
  map_smul' scalar tensor := by
    apply Prod.ext
    · exact (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric).map_smul scalar tensor
    · exact (smoothRegularGeneralMetricRelativeThirdJetLinearMap period
        hPeriod metric).map_smul scalar tensor

def regularGeneralMetricBoundaryC3CoreSubmodule
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Submodule Real (RegularMetricBoundaryC3Ambient period hPeriod metric) :=
  (LinearMap.range
    (smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric)).topologicalClosure

abbrev RegularGeneralMetricBoundaryC3Core
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralMetricBoundaryC3CoreSubmodule period hPeriod metric

@[implicit_reducible]
def regularGeneralMetricBoundaryC3CoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  (regularGeneralMetricBoundaryC3CoreSubmodule
    period hPeriod metric).normedAddCommGroup

@[implicit_reducible]
def regularGeneralMetricBoundaryC3CoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  Submodule.normedSpace
    (regularGeneralMetricBoundaryC3CoreSubmodule period hPeriod metric)

@[implicit_reducible]
def regularGeneralMetricBoundaryC3CoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric))

def smoothToRegularGeneralMetricBoundaryC3Core
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      RegularGeneralMetricBoundaryC3Core period hPeriod metric where
  toFun tensor :=
    ⟨smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric tensor,
      (LinearMap.range
        (smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric)
          tensor)⟩
  map_add' first second := Subtype.ext
    ((smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric).map_add
      first second)
  map_smul' scalar tensor := Subtype.ext
    ((smoothRegularGeneralMetricBoundaryC3LinearMap period hPeriod metric).map_smul
      scalar tensor)

theorem smoothToRegularGeneralMetricBoundaryC3Core_injective
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric) := by
  intro first second hEqual
  apply smoothToGeneralMetricRelativeC2Core_injective period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
  exact congrArg (fun value => value.1.1) hEqual

theorem smoothToRegularGeneralMetricBoundaryC3Core_denseRange
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    DenseRange
      (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := smoothRegularGeneralMetricBoundaryC3LinearMap
    period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric) =
        (LinearMap.range inclusion :
          Set (RegularMetricBoundaryC3Ambient period hPeriod metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨tensor, rfl⟩, rfl⟩
      exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact ⟨smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor, ⟨tensor, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion :
      Set (RegularMetricBoundaryC3Ambient period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric))
  rw [hRange]

def regularGeneralMetricBoundaryC3CoreToAmbient
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RegularMetricBoundaryC3Ambient period hPeriod metric :=
  (regularGeneralMetricBoundaryC3CoreSubmodule
    period hPeriod metric).subtypeL

def regularGeneralMetricBoundaryC3CoreToC2
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RegularGeneralMetricC2Core period hPeriod metric :=
  (ContinuousLinearMap.fst Real
    (RegularGeneralMetricC2Core period hPeriod metric)
    (RegularMetricThirdJetAmbient period hPeriod metric)).comp
      (regularGeneralMetricBoundaryC3CoreToAmbient period hPeriod metric)

def regularGeneralMetricBoundaryC3CoreToThirdJet
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RegularMetricThirdJetAmbient period hPeriod metric :=
  (ContinuousLinearMap.snd Real
    (RegularGeneralMetricC2Core period hPeriod metric)
    (RegularMetricThirdJetAmbient period hPeriod metric)).comp
      (regularGeneralMetricBoundaryC3CoreToAmbient period hPeriod metric)

@[simp]
theorem regularGeneralMetricBoundaryC3CoreToC2_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
          tensor) =
      smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor :=
  rfl

@[simp]
theorem regularGeneralMetricBoundaryC3CoreToThirdJet_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
          tensor) =
      smoothRegularGeneralMetricRelativeThirdJetLinearMap period hPeriod
        metric tensor :=
  rfl

/-- Summary certificate for the boundary-enhanced metric domain. -/
theorem regular_general_metric_boundary_c3_core_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric) ∧
      DenseRange
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric) ∧
      Continuous
        (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric) ∧
      Continuous
        (regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric) :=
  ⟨smoothToRegularGeneralMetricBoundaryC3Core_injective
      period hPeriod metric,
    smoothToRegularGeneralMetricBoundaryC3Core_denseRange
      period hPeriod metric,
    (regularGeneralMetricBoundaryC3CoreToC2
      period hPeriod metric).continuous,
    (regularGeneralMetricBoundaryC3CoreToThirdJet
      period hPeriod metric).continuous⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
end JanusFormal
