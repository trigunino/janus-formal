import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D

/-! Open metric domain and continuous evaluation of actual redundant-frame boundary jets.
The scalar C² core retains its canonical derivative indices; the additional third
jet uses the supplied spanning frame. These two index systems are not identified. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D

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
variable (frame : SmoothD8Frame period hPeriod)
  (metric : SmoothGeneralLorentzMetric period hPeriod)
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local notation "Core" => FrameFreeBoundaryC3Core period hPeriod frame metric
local notation "Index" => BoundaryMetricJetIndex period hPeriod

def frameFreeBoundaryC3Domain : Set Core :=
  frameFreeBoundaryC3CoreToC2 period hPeriod frame metric ⁻¹'
    generalMetricRelativeC2OpenDomain period hPeriod frame metric

theorem frameFreeBoundaryC3Domain_isOpen :
    IsOpen (frameFreeBoundaryC3Domain period hPeriod frame metric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame metric).preimage
    (frameFreeBoundaryC3CoreToC2 period hPeriod frame metric).continuous

theorem zero_mem_frameFreeBoundaryC3Domain :
    (0 : Core) ∈ frameFreeBoundaryC3Domain period hPeriod frame metric := by
  change (0 : GeneralMetricRelativeC2Core period hPeriod frame metric) ∈
    generalMetricRelativeC2OpenDomain period hPeriod frame metric
  exact zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric

def frameFreeBoundaryC3CoreToRelativeMatrix :
    Core →L[Real] C2FiniteMatrix period hPeriod frame.count :=
  (generalMetricRelativeC2CoreToMatrix period hPeriod frame metric).comp
    (frameFreeBoundaryC3CoreToC2 period hPeriod frame metric)

def frameFreeBoundaryC3RelativeEntry (row column : Fin frame.count) :
    Core →L[Real] CanonicalPhysicalScalarC2JetCore period hPeriod :=
  (ContinuousLinearMap.proj column).comp ((ContinuousLinearMap.proj row).comp
    (frameFreeBoundaryC3CoreToRelativeMatrix period hPeriod frame metric))

private def scalarJetFirstCoordinate (index : Index) : ScalarFrameJet2 Index →L[Real] Real :=
  (ContinuousLinearMap.proj index).comp
    ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _))

private def scalarJetSecondCoordinate (outer inner : Index) : ScalarFrameJet2 Index →L[Real] Real :=
  (ContinuousLinearMap.proj inner).comp ((ContinuousLinearMap.proj outer).comp
    ((ContinuousLinearMap.snd Real (Index → Real) (Index → Index → Real)).comp
      (ContinuousLinearMap.snd Real Real ((Index → Real) × (Index → Index → Real)))))

def frameFreeBoundaryC3RelativeEntryToContinuous (row column : Fin frame.count) :
    Core →L[Real] C(EffectiveQuotient period hPeriod, Real) :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
    (frameFreeBoundaryC3RelativeEntry period hPeriod frame metric row column)

def frameFreeBoundaryC3RelativeFirstEntryToContinuous
    (row column : Fin frame.count) (index : Index) :
    Core →L[Real] C(EffectiveQuotient period hPeriod, Real) :=
  ((scalarJetFirstCoordinate period hPeriod index).compLeftContinuous Real
    (EffectiveQuotient period hPeriod)).comp
    ((canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod).comp
      (frameFreeBoundaryC3RelativeEntry period hPeriod frame metric row column))

def frameFreeBoundaryC3RelativeSecondEntryToContinuous
    (row column : Fin frame.count) (outer inner : Index) :
    Core →L[Real] C(EffectiveQuotient period hPeriod, Real) :=
  ((scalarJetSecondCoordinate period hPeriod outer inner).compLeftContinuous Real
    (EffectiveQuotient period hPeriod)).comp
    ((canonicalPhysicalScalarC2JetCoreToAmbient period hPeriod).comp
      (frameFreeBoundaryC3RelativeEntry period hPeriod frame metric row column))

private def continuousValueAt {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (point : EffectiveQuotient period hPeriod) : C(EffectiveQuotient period hPeriod, E) →L[Real] E :=
  LinearMap.mkContinuous
    { toFun := fun field => field point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by
      change ‖field point‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using ContinuousMap.norm_coe_le_norm field point)

def frameFreeBoundaryC3RelativeEntryAt
    (row column : Fin frame.count) (point : EffectiveQuotient period hPeriod) : Core →L[Real] Real :=
  (continuousValueAt period hPeriod point).comp
    (frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column)

def frameFreeBoundaryC3ThirdJetAt (point : EffectiveQuotient period hPeriod) :
    Core →L[Real] FrameFreeMetricThirdJetFiber period hPeriod frame :=
  (continuousValueAt period hPeriod point).comp
    (frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric)

@[simp] theorem frameFreeBoundaryC3CoreToRelativeMatrix_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    frameFreeBoundaryC3CoreToRelativeMatrix period hPeriod frame metric
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) =
      smoothGeneralMetricRelativeEndomorphismToC2 period hPeriod frame metric tensor := rfl

@[simp] theorem frameFreeBoundaryC3RelativeEntryAt_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    frameFreeBoundaryC3RelativeEntryAt period hPeriod frame metric row column point
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column point := rfl

@[simp] theorem frameFreeBoundaryC3RelativeFirstEntry_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) (index : Index) (point : EffectiveQuotient period hPeriod) :
    frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) point =
      frameDerivative period hPeriod Real (finiteSmoothTangentFrame period hPeriod)
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
        point index := rfl

@[simp] theorem frameFreeBoundaryC3RelativeSecondEntry_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) (outer inner : Index) (point : EffectiveQuotient period hPeriod) :
    frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) point =
      frameSecondDerivative period hPeriod (finiteSmoothTangentFrame period hPeriod)
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
        point outer inner := rfl

@[simp] theorem frameFreeBoundaryC3ThirdJetAt_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (point : EffectiveQuotient period hPeriod) :
    frameFreeBoundaryC3ThirdJetAt period hPeriod frame metric point
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) =
      smoothFrameFreeMetricThirdJet period hPeriod frame metric tensor point := rfl

theorem frameFreeBoundaryC3RelativeEntry_joint_continuous (row column : Fin frame.count) :
    Continuous (fun current : Core × EffectiveQuotient period hPeriod =>
      frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column
        current.1 current.2) :=
  ((frameFreeBoundaryC3RelativeEntryToContinuous period hPeriod frame metric row column).continuous.comp
    continuous_fst).eval continuous_snd

theorem frameFreeBoundaryC3RelativeFirstEntry_joint_continuous
    (row column : Fin frame.count) (index : Index) :
    Continuous (fun current : Core × EffectiveQuotient period hPeriod =>
      frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index
        current.1 current.2) :=
  ((frameFreeBoundaryC3RelativeFirstEntryToContinuous period hPeriod frame metric row column index).continuous.comp
    continuous_fst).eval continuous_snd

theorem frameFreeBoundaryC3RelativeSecondEntry_joint_continuous
    (row column : Fin frame.count) (outer inner : Index) :
    Continuous (fun current : Core × EffectiveQuotient period hPeriod =>
      frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner
        current.1 current.2) :=
  ((frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column outer inner).continuous.comp
    continuous_fst).eval continuous_snd

theorem frameFreeBoundaryC3ThirdJet_joint_continuous :
    Continuous (fun current : Core × EffectiveQuotient period hPeriod =>
      frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric current.1 current.2) :=
  ((frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric).continuous.comp
    continuous_fst).eval continuous_snd

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
