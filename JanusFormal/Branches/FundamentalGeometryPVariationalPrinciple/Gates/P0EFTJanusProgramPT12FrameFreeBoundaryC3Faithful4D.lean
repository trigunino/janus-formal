import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryC3Evaluation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFrameDerivativeClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

/-! Stokes compatibility and faithfulness of the C³ refinement when its
additional derivatives use the same finite spanning frame as the scalar C² core. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryC3Faithful4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeClosed4D
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
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : Measure.IsOpenPosMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Core" => FrameFreeBoundaryC3Core period hPeriod frame metric
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance

private def thirdCoordinate (row column outer middle inner : Index) :
    FrameFreeMetricThirdJetFiber period hPeriod frame →L[Real] Real :=
  (ContinuousLinearMap.proj inner).comp ((ContinuousLinearMap.proj middle).comp
    ((ContinuousLinearMap.proj outer).comp ((ContinuousLinearMap.proj column).comp
      (ContinuousLinearMap.proj row :
        (Index → Index → Index → Index → Index → Real) →L[Real]
          (Index → Index → Index → Index → Real)))))

def frameFreeBoundaryC3CanonicalThirdEntry
    (row column outer middle inner : Index) :
    Core →L[Real] C(EffectiveQuotient period hPeriod, Real) :=
  ((thirdCoordinate period hPeriod row column outer middle inner).compLeftContinuous Real
    (EffectiveQuotient period hPeriod)).comp
    (frameFreeBoundaryC3CoreToThirdJet period hPeriod frame metric)

@[simp] theorem frameFreeBoundaryC3CanonicalThirdEntry_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column outer middle inner : Index) (point : EffectiveQuotient period hPeriod) :
    frameFreeBoundaryC3CanonicalThirdEntry period hPeriod metric row column outer middle inner
      (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) point =
      frameDerivative period hPeriod Real frame
        (frameDerivativeComponentField period hPeriod frame
          (frameDerivativeComponentField period hPeriod frame
            (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
            inner) middle) point outer := rfl

/-- The third coordinate is the genuine weak derivative of the stored second coordinate. -/
theorem frameFreeBoundaryC3CanonicalDerivativeGraph_mem
    (row column outer middle inner : Index) (x : Core) :
    (continuousToCanonicalPhysicalBulkL2 period hPeriod
      (frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric
        row column middle inner x),
     continuousToCanonicalPhysicalBulkL2 period hPeriod
      (frameFreeBoundaryC3CanonicalThirdEntry period hPeriod metric row column outer middle inner x)) ∈
      (canonicalFrameDerivativeMinimal period hPeriod frame outer).graph := by
  let second := frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric
    row column middle inner
  let third := frameFreeBoundaryC3CanonicalThirdEntry period hPeriod metric row column outer middle inner
  let inclusion := (continuousToCanonicalPhysicalBulkL2 period hPeriod).comp second
  let derivative := (continuousToCanonicalPhysicalBulkL2 period hPeriod).comp third
  let operator := canonicalFrameDerivativeMinimal period hPeriod frame outer
  have hClosed : IsClosed ((inclusion.prod derivative) ⁻¹' (operator.graph : Set _)) :=
    (frameFreeCanonicalFrameDerivativeMinimal_isClosed period hPeriod frame outer).preimage
      (inclusion.prod derivative).continuous
  have hSmooth : Set.range (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric) ⊆
      (inclusion.prod derivative) ⁻¹' (operator.graph : Set _) := by
    rintro _ ⟨tensor, rfl⟩
    let field := frameDerivativeComponentField period hPeriod frame
      (frameDerivativeComponentField period hPeriod frame
        (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor row column)
        inner) middle
    have hSecond : second (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) =
        smoothToCanonicalPhysicalContinuousScalar period hPeriod field := by
      apply ContinuousMap.ext
      intro point
      rfl
    have hThird : third (smoothToFrameFreeBoundaryC3Core period hPeriod frame metric tensor) =
        smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (canonicalFrameDerivativeSmooth period hPeriod frame outer field) := by
      apply ContinuousMap.ext
      intro point
      rfl
    change (continuousToCanonicalPhysicalBulkL2 period hPeriod (second _),
      continuousToCanonicalPhysicalBulkL2 period hPeriod (third _)) ∈ operator.graph
    rw [hSecond, hThird, continuousToCanonicalPhysicalBulkL2_agrees_on_smooth,
      continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]
    apply operator.mem_graph_iff.mpr
    exact ⟨⟨smoothToCanonicalPhysicalBulkL2 period hPeriod field,
      canonicalFrameDerivativeMinimal_smooth_mem period hPeriod frame outer field⟩, rfl,
      frameFreeCanonicalFrameDerivativeMinimal_smooth_apply period hPeriod frame outer field⟩
  exact closure_minimal hSmooth hClosed
    (smoothToFrameFreeBoundaryC3Core_denseRange period hPeriod frame metric x)

/-- No independent third-jet value appears in the completion over its C² projection. -/
theorem frameFreeBoundaryC3CanonicalToC2_injective :
    Function.Injective (frameFreeBoundaryC3CoreToC2 period hPeriod frame metric) := by
  intro x y hValue
  have hL2inj : Function.Injective (continuousToCanonicalPhysicalBulkL2 period hPeriod) :=
    ContinuousMap.toLp_injective (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hThird (row column outer middle inner : Index) :
      frameFreeBoundaryC3CanonicalThirdEntry period hPeriod metric row column outer middle inner x =
      frameFreeBoundaryC3CanonicalThirdEntry period hPeriod metric row column outer middle inner y := by
    apply hL2inj
    let operator := canonicalFrameDerivativeMinimal period hPeriod frame outer
    have hDifference := operator.graph.sub_mem
      (frameFreeBoundaryC3CanonicalDerivativeGraph_mem period hPeriod metric row column outer middle inner x)
      (frameFreeBoundaryC3CanonicalDerivativeGraph_mem period hPeriod metric row column outer middle inner y)
    have hSecond :
        frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column middle inner x =
        frameFreeBoundaryC3RelativeSecondEntryToContinuous period hPeriod frame metric row column middle inner y := by
      simp only [frameFreeBoundaryC3RelativeSecondEntryToContinuous, frameFreeBoundaryC3RelativeEntry,
        frameFreeBoundaryC3CoreToRelativeMatrix, ContinuousLinearMap.comp_apply]
      rw [hValue]
    exact sub_eq_zero.mp (operator.graph_fst_eq_zero_snd hDifference
      (sub_eq_zero.mpr (congrArg (continuousToCanonicalPhysicalBulkL2 period hPeriod) hSecond)))
  apply Subtype.ext
  apply Prod.ext
  · exact hValue
  · apply ContinuousMap.ext
    intro point
    funext row column outer middle inner
    exact congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
      (hThird row column outer middle inner)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryC3Faithful4D
