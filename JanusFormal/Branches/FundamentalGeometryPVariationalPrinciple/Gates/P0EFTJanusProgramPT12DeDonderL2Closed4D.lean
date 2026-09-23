import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D

/-! Minimal closed de Donder realization on the original symmetric-tensor L² completion. -/
namespace JanusFormal.P0EFTJanusProgramPT12DeDonderL2Closed4D
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
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12DeDonderRowAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularTensorL2Bridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (reference : RegularGeneralLorentzMetric period hPeriod)

abbrev DeDonderTensorL2 := FrameTensorL2Completion period hPeriod (finiteSmoothTangentFrame period hPeriod)

theorem deDonderTensorSmooth_injective : Function.Injective
    (frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)) := by
  intro first second h
  apply globalGeneralMetricTensorFrameL2LinearMap_injective period hPeriod
  exact congrArg Subtype.val h

private def smoothEquivDomain : SmoothSymmetricCovariantTwoTensor period hPeriod ≃ₗ[Real]
    (frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).range :=
  LinearEquiv.ofInjective (frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod))
    (deDonderTensorSmooth_injective period hPeriod)

def deDonderL2Core : DeDonderTensorL2 period hPeriod →ₗ.[Real] GlobalGeneralMetricDeDonderFrameL2 period hPeriod where
  domain := (frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).range
  toFun := (globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric).comp
    (smoothEquivDomain period hPeriod).symm.toLinearMap

theorem deDonderL2Core_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    deDonderL2Core period hPeriod metric
      ⟨frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod) tensor, ⟨tensor, rfl⟩⟩ =
      globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric tensor := by
  change globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric
    ((smoothEquivDomain period hPeriod).symm ((smoothEquivDomain period hPeriod) tensor)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem deDonderL2_smooth_pairing (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real (globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric tensor row)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor)
        (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference row test) := by
  have hCoefficient : globalSmoothCovectorFrameCoefficientLinearMap period hPeriod row
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor) =
      deDonderRow period hPeriod (finiteSmoothTangentFrame period hPeriod) metric
        (generalMetricFrameCoefficient period hPeriod (finiteSmoothTangentFrame period hPeriod) tensor) row := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact (deDonderRow_actual period hPeriod (finiteSmoothTangentFrame period hPeriod) metric tensor point row).symm
  change inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
    (globalSmoothCovectorFrameCoefficientLinearMap period hPeriod row
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor))) _ = _
  rw [hCoefficient]
  exact deDonderRow_pairing period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference _ row test

theorem deDonderL2Core_pairing (field : (deDonderL2Core period hPeriod metric).domain)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real (deDonderL2Core period hPeriod metric field row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real field.val.val (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference row test) := by
  rcases field with ⟨field, hField⟩
  obtain ⟨tensor, rfl⟩ := hField
  rw [deDonderL2Core_smooth]
  exact deDonderL2_smooth_pairing period hPeriod metric reference tensor row test

theorem deDonderL2_closedGraph_pairing
    (pair : DeDonderTensorL2 period hPeriod × GlobalGeneralMetricDeDonderFrameL2 period hPeriod)
    (hPair : pair ∈ (deDonderL2Core period hPeriod metric).graph.topologicalClosure)
    (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real (pair.2 row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real pair.1.val (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference row test) := by
  have hClosed : IsClosed {value : DeDonderTensorL2 period hPeriod × GlobalGeneralMetricDeDonderFrameL2 period hPeriod |
      inner Real (value.2 row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
        inner Real value.1.val (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) metric reference row test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real (value.2 row) _ = inner Real value.1.val _
  rw [← hOutput, ← hInput]
  exact deDonderL2Core_pairing period hPeriod metric reference field row test

include reference in
theorem deDonderL2Core_isClosable : (deDonderL2Core period hPeriod metric).IsClosable := by
  refine ⟨(deDonderL2Core period hPeriod metric).graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hPair hZero
  change x = 0 at hZero
  subst x
  apply PiLp.ext
  intro row
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  exact (deDonderL2_closedGraph_pairing period hPeriod metric reference (0, y) hPair row test).trans (inner_zero_left _)

def deDonderL2Minimal : DeDonderTensorL2 period hPeriod →ₗ.[Real] GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (deDonderL2Core period hPeriod metric).closure

include reference in
theorem deDonderL2Minimal_isClosed : (deDonderL2Minimal period hPeriod metric).IsClosed :=
  (deDonderL2Core_isClosable period hPeriod metric reference).closure_isClosed

theorem deDonderL2Minimal_hasCore : (deDonderL2Minimal period hPeriod metric).HasCore
    (frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)).range :=
  (deDonderL2Core period hPeriod metric).closureHasCore

theorem deDonderL2Minimal_denseDomain : Dense ((deDonderL2Minimal period hPeriod metric).domain : Set (DeDonderTensorL2 period hPeriod)) :=
  (frameTensorL2Smooth_denseRange period hPeriod (finiteSmoothTangentFrame period hPeriod)).mono
    (fun _ h => (deDonderL2Core period hPeriod metric).le_closure.1 h)

theorem deDonderL2Minimal_smooth_mem (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod) tensor ∈
      (deDonderL2Minimal period hPeriod metric).domain :=
  (deDonderL2Core period hPeriod metric).le_closure.1 ⟨tensor, rfl⟩

theorem deDonderL2Minimal_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    deDonderL2Minimal period hPeriod metric
      ⟨frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod) tensor,
        deDonderL2Minimal_smooth_mem period hPeriod metric tensor⟩ =
      globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric tensor :=
  ((deDonderL2Core period hPeriod metric).le_closure.2 (x := ⟨_, ⟨tensor, rfl⟩⟩)
    (y := ⟨_, deDonderL2Minimal_smooth_mem period hPeriod metric tensor⟩) rfl).symm.trans
      (deDonderL2Core_smooth period hPeriod metric tensor)

end
end JanusFormal.P0EFTJanusProgramPT12DeDonderL2Closed4D
