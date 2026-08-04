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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

abbrev BoundaryMetricJetIndex :=
  Fin (finiteSmoothTangentFrame period hPeriod).count

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

abbrev RegularMetricThirdJetFiber
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  Fin 4 → Fin 4 →
    BoundaryMetricJetIndex period hPeriod →
      BoundaryMetricJetIndex period hPeriod →
        BoundaryMetricJetIndex period hPeriod → Real

/-- Third frame jet of the same relative metric endomorphism used by the
bulk C² chart. -/
def smoothRegularGeneralMetricRelativeThirdJet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    RegularMetricThirdJetFiber period hPeriod metric :=
  fun row column outer middle inner =>
    generalMetricFrameThirdDerivative period hPeriod
      (finiteSmoothTangentFrame period hPeriod)
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
    (finiteSmoothTangentFrame period hPeriod)
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
      (finiteSmoothTangentFrame period hPeriod)
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
      (finiteSmoothTangentFrame period hPeriod) scalar
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row column)) point) outer) middle) inner

abbrev RegularMetricThirdJetAmbient
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

/-! ## Reuse of the existing metric chart and scalar-jet evaluators -/

/-- The admissible metric set is exactly the preimage of the existing bulk
`C²` domain.  The extra boundary jet does not impose a second notion of
metric admissibility. -/
def regularGeneralMetricBoundaryC3Domain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric ⁻¹'
    regularGeneralMetricC2Domain period hPeriod metric

theorem regularGeneralMetricBoundaryC3Domain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricBoundaryC3Domain period hPeriod metric) :=
  (regularGeneralMetricC2Domain_isOpen period hPeriod metric).preimage
    (regularGeneralMetricBoundaryC3CoreToC2
      period hPeriod metric).continuous

theorem zero_mem_regularGeneralMetricBoundaryC3Domain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : RegularGeneralMetricBoundaryC3Core period hPeriod metric) ∈
      regularGeneralMetricBoundaryC3Domain period hPeriod metric := by
  change regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric 0 ∈
    regularGeneralMetricC2Domain period hPeriod metric
  rw [map_zero]
  exact zero_mem_regularGeneralMetricC2Domain period hPeriod metric

/-- Continuous reuse of the relative-metric matrix stored by the bulk chart. -/
def regularGeneralMetricBoundaryC3CoreToRelativeMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      C2FiniteMatrix period hPeriod 4 :=
  (generalMetricRelativeC2CoreToMatrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric).comp
      (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric)

/-- One relative-metric coefficient, still carrying its complete scalar
`C²` jet. -/
def regularGeneralMetricBoundaryC3RelativeEntry
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj column).comp
    ((ContinuousLinearMap.proj row).comp
      (regularGeneralMetricBoundaryC3CoreToRelativeMatrix
        period hPeriod metric))

private def boundaryMetricScalarJetFirstCoordinate
    (index : BoundaryMetricJetIndex period hPeriod) :
    ScalarFrameJet2 (BoundaryMetricJetIndex period hPeriod) →L[Real] Real :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.fst Real
      (BoundaryMetricJetIndex period hPeriod → Real)
      (BoundaryMetricJetIndex period hPeriod →
        BoundaryMetricJetIndex period hPeriod → Real)).comp
    (ContinuousLinearMap.snd Real Real
      ((BoundaryMetricJetIndex period hPeriod → Real) ×
        (BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod → Real))))

private def boundaryMetricScalarJetSecondCoordinate
    (outer inner : BoundaryMetricJetIndex period hPeriod) :
    ScalarFrameJet2 (BoundaryMetricJetIndex period hPeriod) →L[Real] Real :=
  (ContinuousLinearMap.proj inner).comp
    ((ContinuousLinearMap.proj outer).comp
      ((ContinuousLinearMap.snd Real
        (BoundaryMetricJetIndex period hPeriod → Real)
        (BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod → Real)).comp
      (ContinuousLinearMap.snd Real Real
        ((BoundaryMetricJetIndex period hPeriod → Real) ×
          (BoundaryMetricJetIndex period hPeriod →
            BoundaryMetricJetIndex period hPeriod → Real)))))

/-- Continuous first frame derivative of one completed relative-metric
coefficient. -/
def regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  ((boundaryMetricScalarJetFirstCoordinate period hPeriod index)
      |>.compLeftContinuous Real (EffectiveQuotient period hPeriod)).comp
    ((canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod).comp
      (regularGeneralMetricBoundaryC3RelativeEntry period hPeriod metric
        row column))

/-- Continuous ordered second frame derivative of one completed
relative-metric coefficient. -/
def regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  ((boundaryMetricScalarJetSecondCoordinate period hPeriod outer inner)
      |>.compLeftContinuous Real (EffectiveQuotient period hPeriod)).comp
    ((canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod).comp
      (regularGeneralMetricBoundaryC3RelativeEntry period hPeriod metric
        row column))

@[simp]
theorem regularGeneralMetricBoundaryC3RelativeFirstEntry_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous period hPeriod
        metric row column index
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
          tensor) point =
      frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod)
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor row column) point index :=
  rfl

@[simp]
theorem regularGeneralMetricBoundaryC3RelativeSecondEntry_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous period hPeriod
        metric row column outer inner
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
          tensor) point =
      frameSecondDerivative period hPeriod
        (finiteSmoothTangentFrame period hPeriod)
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor row column) point outer inner :=
  rfl

/-- Continuous value field of one completed relative-metric coefficient. -/
def regularGeneralMetricBoundaryC3RelativeEntryToContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
    (regularGeneralMetricBoundaryC3RelativeEntry period hPeriod metric
      row column)

/-- Point evaluation of one completed relative-metric coefficient. -/
private def regularGeneralMetricBoundaryC3ContinuousValueAt
    (point : EffectiveQuotient period hPeriod) :
    C(EffectiveQuotient period hPeriod, Real) →L[Real] Real :=
  LinearMap.mkContinuous
    { toFun := fun field => field point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by
      change ‖field point‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using
        (ContinuousMap.norm_coe_le_norm field point))

def regularGeneralMetricBoundaryC3RelativeEntryAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real] Real :=
  (regularGeneralMetricBoundaryC3ContinuousValueAt
    period hPeriod point).comp
      (regularGeneralMetricBoundaryC3RelativeEntryToContinuous
        period hPeriod metric row column)

@[simp]
theorem regularGeneralMetricBoundaryC3RelativeEntryAt_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricBoundaryC3RelativeEntryAt period hPeriod metric
        row column point
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
          tensor) =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row column point :=
  rfl

/-- Joint continuity of coefficient evaluation in the completed metric and
the moving ambient point. -/
theorem regularGeneralMetricBoundaryC3RelativeEntry_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3RelativeEntryToContinuous
        period hPeriod metric row column current.1 current.2) :=
  ((regularGeneralMetricBoundaryC3RelativeEntryToContinuous
    period hPeriod metric row column).continuous.comp continuous_fst).eval
      continuous_snd

theorem regularGeneralMetricBoundaryC3RelativeFirstEntry_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod) :
    Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous
        period hPeriod metric row column index current.1 current.2) :=
  ((regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous
    period hPeriod metric row column index).continuous.comp continuous_fst).eval
      continuous_snd

theorem regularGeneralMetricBoundaryC3RelativeSecondEntry_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod) :
    Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous
        period hPeriod metric row column outer inner current.1 current.2) :=
  ((regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous
    period hPeriod metric row column outer inner).continuous.comp
      continuous_fst).eval continuous_snd

/-- Continuous evaluation of the additional ordered third jet. -/
private def regularGeneralMetricBoundaryC3ContinuousThirdJetAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    RegularMetricThirdJetAmbient period hPeriod metric →L[Real]
      RegularMetricThirdJetFiber period hPeriod metric :=
  LinearMap.mkContinuous
    { toFun := fun field => field point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by
      change ‖field point‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using
        (ContinuousMap.norm_coe_le_norm field point))

def regularGeneralMetricBoundaryC3ThirdJetAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RegularMetricThirdJetFiber period hPeriod metric :=
  (regularGeneralMetricBoundaryC3ContinuousThirdJetAt
    period hPeriod metric point).comp
    (regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric)

@[simp]
theorem regularGeneralMetricBoundaryC3ThirdJetAt_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricBoundaryC3ThirdJetAt period hPeriod metric point
        (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
          tensor) =
      smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric tensor
        point :=
  rfl

/-- Joint continuity of the extra third jet in the completed metric and the
evaluation point. -/
theorem regularGeneralMetricBoundaryC3ThirdJet_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric
        current.1 current.2) :=
  ((regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric).continuous
    |>.comp continuous_fst).eval continuous_snd

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

/-- Local-chart certificate inherited without alteration from the bulk `C²`
domain, together with the moving-point evaluators used by P2. -/
theorem regular_general_metric_boundary_c3_chart_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricBoundaryC3Domain period hPeriod metric) ∧
      (0 : RegularGeneralMetricBoundaryC3Core period hPeriod metric) ∈
        regularGeneralMetricBoundaryC3Domain period hPeriod metric ∧
      (∀ row column : Fin 4,
        Continuous (fun current :
          RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
            EffectiveQuotient period hPeriod =>
          regularGeneralMetricBoundaryC3RelativeEntryToContinuous
            period hPeriod metric row column current.1 current.2)) ∧
      Continuous (fun current :
        RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
          EffectiveQuotient period hPeriod =>
        regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric
          current.1 current.2) := by
  exact ⟨regularGeneralMetricBoundaryC3Domain_isOpen period hPeriod metric,
    zero_mem_regularGeneralMetricBoundaryC3Domain period hPeriod metric,
    fun row column =>
      regularGeneralMetricBoundaryC3RelativeEntry_joint_continuous
        period hPeriod metric row column,
    regularGeneralMetricBoundaryC3ThirdJet_joint_continuous
      period hPeriod metric⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
end JanusFormal
