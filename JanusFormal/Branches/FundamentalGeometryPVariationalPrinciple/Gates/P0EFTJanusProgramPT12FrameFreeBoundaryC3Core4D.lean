import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D

/-! Genuine boundary C³ completion in a finite spanning frame, with no global basis. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
variable (frame : SmoothD8Frame period hPeriod)
  (metric : SmoothGeneralLorentzMetric period hPeriod)

abbrev FrameFreeMetricThirdJetFiber :=
  Fin frame.count → Fin frame.count → Fin frame.count → Fin frame.count → Fin frame.count → Real

def smoothFrameFreeMetricThirdJet (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : FrameFreeMetricThirdJetFiber period hPeriod frame :=
  fun row column => generalMetricFrameThirdDerivative period hPeriod frame
    (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column) point

theorem smoothFrameFreeMetricThirdJet_contMDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, FrameFreeMetricThirdJetFiber period hPeriod frame) ∞
      (smoothFrameFreeMetricThirdJet period hPeriod frame metric tensor) := by
  apply contMDiff_pi_space.mpr
  intro row
  apply contMDiff_pi_space.mpr
  intro column
  exact generalMetricFrameThirdDerivative_contMDiff period hPeriod frame
    (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)

def frameFreeMetricThirdJetLinearMap :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      C(EffectiveQuotient period hPeriod, FrameFreeMetricThirdJetFiber period hPeriod frame) where
  toFun tensor := ⟨smoothFrameFreeMetricThirdJet period hPeriod frame metric tensor,
    (smoothFrameFreeMetricThirdJet_contMDiff period hPeriod frame metric tensor).continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    funext row column
    change generalMetricFrameThirdDerivative period hPeriod frame
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric
        (first + second) row column) point = _
    rw [smoothGeneralMetricRelativeEndomorphismMatrix_add]
    exact congrFun (generalMetricFrameThirdDerivative_add period hPeriod frame _ _) point
  map_smul' scalar tensor := by
    apply ContinuousMap.ext
    intro point
    funext row column
    change generalMetricFrameThirdDerivative period hPeriod frame
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric
        (scalar • tensor) row column) point = _
    rw [smoothGeneralMetricRelativeEndomorphismMatrix_smul]
    exact congrFun (generalMetricFrameThirdDerivative_smul period hPeriod frame scalar _) point

local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local instance : CompleteSpace (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  generalMetricRelativeC2CoreCompleteSpace period hPeriod frame metric

abbrev FrameFreeBoundaryC3Ambient :=
  GeneralMetricRelativeC2Core period hPeriod frame metric ×
    C(EffectiveQuotient period hPeriod, FrameFreeMetricThirdJetFiber period hPeriod frame)

def smoothFrameFreeBoundaryC3LinearMap :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      FrameFreeBoundaryC3Ambient period hPeriod frame metric :=
  (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric).prod
    (frameFreeMetricThirdJetLinearMap period hPeriod frame metric)

def frameFreeBoundaryC3CoreSubmodule :
    Submodule Real (FrameFreeBoundaryC3Ambient period hPeriod frame metric) :=
  (smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric).range.topologicalClosure

abbrev FrameFreeBoundaryC3Core := frameFreeBoundaryC3CoreSubmodule period hPeriod frame metric

instance frameFreeBoundaryC3CoreNormedAddCommGroup :
    NormedAddCommGroup (FrameFreeBoundaryC3Core period hPeriod frame metric) :=
  (frameFreeBoundaryC3CoreSubmodule period hPeriod frame metric).normedAddCommGroup
instance frameFreeBoundaryC3CoreNormedSpace :
    NormedSpace Real (FrameFreeBoundaryC3Core period hPeriod frame metric) :=
  Submodule.normedSpace (frameFreeBoundaryC3CoreSubmodule period hPeriod frame metric)
instance frameFreeBoundaryC3CoreCompleteSpace :
    CompleteSpace (FrameFreeBoundaryC3Core period hPeriod frame metric) :=
  Submodule.topologicalClosure.completeSpace
    (smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric).range

def smoothToFrameFreeBoundaryC3Core :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      FrameFreeBoundaryC3Core period hPeriod frame metric where
  toFun tensor := ⟨smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric tensor,
    (smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric).range.le_topologicalClosure
      (LinearMap.mem_range_self _ tensor)⟩
  map_add' first second := Subtype.ext
    ((smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric).map_add first second)
  map_smul' scalar tensor := Subtype.ext
    ((smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric).map_smul scalar tensor)

theorem smoothToFrameFreeBoundaryC3Core_injective :
    Function.Injective (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric) := by
  intro first second hEqual
  apply smoothToGeneralMetricRelativeC2Core_injective period hPeriod frame metric
  exact congrArg (fun value => value.1.1) hEqual

theorem smoothToFrameFreeBoundaryC3Core_denseRange :
    DenseRange (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := smoothFrameFreeBoundaryC3LinearMap period hPeriod frame metric
  have hRange : Subtype.val '' Set.range
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric) =
      (inclusion.range : Set (FrameFreeBoundaryC3Ambient period hPeriod frame metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨tensor, rfl⟩, rfl⟩
      exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact ⟨smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor, ⟨tensor, rfl⟩, rfl⟩
  change closure (inclusion.range : Set (FrameFreeBoundaryC3Ambient period hPeriod frame metric)) ⊆
    closure (Subtype.val '' Set.range (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric))
  rw [hRange]

def frameFreeBoundaryC3CoreToC2 :
    FrameFreeBoundaryC3Core period hPeriod frame metric →L[Real]
      GeneralMetricRelativeC2Core period hPeriod frame metric :=
  (ContinuousLinearMap.fst Real _ _).comp
    (frameFreeBoundaryC3CoreSubmodule period hPeriod frame metric).subtypeL

def frameFreeBoundaryC3CoreToThirdJet :
    FrameFreeBoundaryC3Core period hPeriod frame metric →L[Real]
      C(EffectiveQuotient period hPeriod, FrameFreeMetricThirdJetFiber period hPeriod frame) :=
  (ContinuousLinearMap.snd Real _ _).comp
    (frameFreeBoundaryC3CoreSubmodule period hPeriod frame metric).subtypeL

@[simp] theorem frameFreeBoundaryC3CoreToC2_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    frameFreeBoundaryC3CoreToC2 period hPeriod frame metric
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) =
      smoothToGeneralMetricRelativeC2Core period hPeriod frame metric tensor := rfl

@[simp] theorem frameFreeBoundaryC3CoreToThirdJet_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) point =
      smoothFrameFreeMetricThirdJet period hPeriod frame metric tensor point := rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
