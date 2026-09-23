import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D

/-! The actual metric tensor coordinates and the paired Cartan outputs use equivalent L² completions. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

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

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12PairedRegularFrameCartan4D
open P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)

def regularTensorL2 : SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] CartanTensorL2 period hPeriod :=
  frameTensorL2 period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)

theorem frameTensorL2_finite_eq_actual :
    frameTensorL2 period hPeriod (finiteSmoothTangentFrame period hPeriod) =
      globalGeneralMetricTensorFrameL2LinearMap period hPeriod := by
  ext tensor row
  rfl

def regularTensorL2Transport : CartanTensorL2 period hPeriod →L[Real] GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  frameTensorL2Transport period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    (finiteSmoothTangentFrame period hPeriod) reference.metric

def regularTensorL2Recovery : GlobalGeneralMetricTensorFrameL2 period hPeriod →L[Real] CartanTensorL2 period hPeriod :=
  frameTensorL2Transport period hPeriod (finiteSmoothTangentFrame period hPeriod)
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric

theorem regularTensorL2Transport_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularTensorL2Transport period hPeriod reference (regularTensorL2 period hPeriod reference tensor) =
      globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor :=
  frameTensorL2Transport_smooth period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    (finiteSmoothTangentFrame period hPeriod) reference.metric tensor

theorem regularTensorL2Recovery_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularTensorL2Recovery period hPeriod reference (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
      regularTensorL2 period hPeriod reference tensor :=
  frameTensorL2Transport_smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric tensor

def regularTensorL2Equiv :
    FrameTensorL2Completion period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) ≃L[Real]
      FrameTensorL2Completion period hPeriod (finiteSmoothTangentFrame period hPeriod) :=
  frameTensorL2Equiv period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    (finiteSmoothTangentFrame period hPeriod) reference.metric

theorem finiteTensorL2Space_eq_actual :
    frameTensorL2Space period hPeriod (finiteSmoothTangentFrame period hPeriod) =
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod).range.topologicalClosure := by
  unfold frameTensorL2Space
  rw [frameTensorL2_finite_eq_actual]

theorem regularFrameCartanL2_eq_tensorL2 (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameCartanL2 period hPeriod reference tensor coefficients =
      regularTensorL2 period hPeriod reference
        (smoothMetricCartanAction period hPeriod
          (regularFrameGhostFromCoefficients period hPeriod reference coefficients) tensor) := by
  apply PiLp.ext
  intro row
  exact regularFrameCartanL2_actual period hPeriod reference tensor coefficients row.1 row.2

theorem regularTensorL2Transport_cartan (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularTensorL2Transport period hPeriod reference
      (regularFrameCartanL2 period hPeriod reference tensor coefficients) =
      globalGeneralMetricTensorFrameL2LinearMap period hPeriod
        (smoothMetricCartanAction period hPeriod
          (regularFrameGhostFromCoefficients period hPeriod reference coefficients) tensor) := by
  rw [regularFrameCartanL2_eq_tensorL2, regularTensorL2Transport_smooth]

theorem pairedCartanMinimal_output_mem
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (graph : (pairedCartanMinimal period hPeriod reference metric).graph) :
    WithLp.fst graph.val.2 ∈ frameTensorL2Space period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) ∧
    WithLp.snd graph.val.2 ∈ frameTensorL2Space period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) := by
  let space : Submodule Real (CartanTensorL2 period hPeriod) := frameTensorL2Space period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
  have hClosedSpace : IsClosed (space : Set (CartanTensorL2 period hPeriod)) :=
    (regularTensorL2 period hPeriod reference).range.isClosed_topologicalClosure
  have hClosed : IsClosed {pair : CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod |
      WithLp.fst pair.2 ∈ space ∧ WithLp.snd pair.2 ∈ space} :=
    (hClosedSpace.preimage ((WithLp.fstL 2 Real _ _).continuous.comp continuous_snd)).inter
      (hClosedSpace.preimage ((WithLp.sndL 2 Real _ _).continuous.comp continuous_snd))
  have hGraph := graph.property
  change graph.val ∈ (pairedCartanSmoothRestriction period hPeriod reference metric).closure.graph at hGraph
  rw [← (pairedCartanSmoothRestriction_isClosable period hPeriod reference metric).graph_closure_eq_closure_graph] at hGraph
  apply (closure_minimal _ hClosed) hGraph
  intro pair hPair
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hPair
  obtain ⟨coefficients, hCoefficients⟩ := field.property.1
  have hAction : pairedCartanSmoothRestriction period hPeriod reference metric field =
      pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients :=
    (LinearPMap.domRestrict_apply
      (y := ⟨_, pairedCartan_smooth_mem period hPeriod reference metric coefficients⟩) hCoefficients.symm).trans
      (pairedCartan_smooth_apply period hPeriod reference metric coefficients)
  have hValue := hOutput.symm.trans hAction
  change WithLp.fst pair.2 ∈ space ∧ WithLp.snd pair.2 ∈ space
  rw [hValue]
  constructor
  · change regularFrameCartanL2 period hPeriod reference (metric .plus).tensor coefficients ∈ space
    exact (regularTensorL2 period hPeriod reference).range.le_topologicalClosure
      ⟨_, (regularFrameCartanL2_eq_tensorL2 period hPeriod reference (metric .plus).tensor coefficients).symm⟩
  · change regularFrameCartanL2 period hPeriod reference (metric .minus).tensor coefficients ∈ space
    exact (regularTensorL2 period hPeriod reference).range.le_topologicalClosure
      ⟨_, (regularFrameCartanL2_eq_tensorL2 period hPeriod reference (metric .minus).tensor coefficients).symm⟩

end
end JanusFormal.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
