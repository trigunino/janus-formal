import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Equiv4D

/-! Closed paired Cartan realization in the original ghost and symmetric-tensor L² coordinates. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedActualCartanClosed4D
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

open P0EFTJanusProgramPT12RegularTensorL2Bridge4D
open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPT12RegularGhostL2Equiv4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

abbrev ActualCartanGhostL2 := (regularGhostL2Transport period hPeriod reference (metric .plus)).range
abbrev ActualCartanTensorL2 := FrameTensorL2Completion period hPeriod (finiteSmoothTangentFrame period hPeriod)
abbrev ActualPairedCartanTensorL2 := WithLp 2 (ActualCartanTensorL2 period hPeriod × ActualCartanTensorL2 period hPeriod)

private def tensorRecovery : ActualCartanTensorL2 period hPeriod →L[Real] CartanTensorL2 period hPeriod :=
  (frameTensorL2Space period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)).subtypeL.comp
      (regularTensorL2Equiv period hPeriod reference).symm.toContinuousLinearMap

def pairedActualCartanRecovery : ActualPairedCartanTensorL2 period hPeriod →L[Real] PairedCartanTensorL2 period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.toContinuousLinearMap.comp
    (((tensorRecovery period hPeriod reference).comp (WithLp.fstL 2 Real _ _)).prod
      ((tensorRecovery period hPeriod reference).comp (WithLp.sndL 2 Real _ _)))

theorem pairedActualCartanRecovery_injective : Function.Injective (pairedActualCartanRecovery period hPeriod reference) := by
  intro first second h
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply (regularTensorL2Equiv period hPeriod reference).symm.injective
    apply Subtype.ext
    exact congrArg (fun value : PairedCartanTensorL2 period hPeriod => WithLp.fst value) h
  · apply (regularTensorL2Equiv period hPeriod reference).symm.injective
    apply Subtype.ext
    exact congrArg (fun value : PairedCartanTensorL2 period hPeriod => WithLp.snd value) h

private def graphRecovery :
    (ActualCartanGhostL2 period hPeriod reference metric × ActualPairedCartanTensorL2 period hPeriod) →L[Real]
      (CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod) :=
  ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst Real _ _)).prod
    ((pairedActualCartanRecovery period hPeriod reference).comp (ContinuousLinearMap.snd Real _ _))

def pairedActualCartanGraph : Submodule Real
    (ActualCartanGhostL2 period hPeriod reference metric × ActualPairedCartanTensorL2 period hPeriod) :=
  (pairedCartanMinimal period hPeriod reference metric).graph.comap
    (graphRecovery period hPeriod reference metric).toLinearMap

theorem pairedActualCartanGraph_isClosed : IsClosed (pairedActualCartanGraph period hPeriod reference metric :
    Set (ActualCartanGhostL2 period hPeriod reference metric × ActualPairedCartanTensorL2 period hPeriod)) :=
  (pairedCartanMinimal_isClosed period hPeriod reference metric).preimage
    (graphRecovery period hPeriod reference metric).continuous

theorem pairedActualCartanGraph_input_injective :
    Function.Injective (fun graph : pairedActualCartanGraph period hPeriod reference metric => graph.val.1) := by
  intro first second hInput
  apply Subtype.ext
  refine Prod.ext hInput ?_
  apply pairedActualCartanRecovery_injective period hPeriod reference
  have hDiff := (pairedCartanMinimal period hPeriod reference metric).graph.sub_mem first.property second.property
  have hZero : (graphRecovery period hPeriod reference metric first.val -
      graphRecovery period hPeriod reference metric second.val).1 = 0 :=
    sub_eq_zero.mpr (congrArg (regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm hInput)
  exact sub_eq_zero.mp ((pairedCartanMinimal period hPeriod reference metric).graph_fst_eq_zero_snd hDiff hZero)

def pairedActualCartanOperator :
    ActualCartanGhostL2 period hPeriod reference metric →ₗ.[Real] ActualPairedCartanTensorL2 period hPeriod :=
  (pairedActualCartanGraph period hPeriod reference metric).toLinearPMap

theorem pairedActualCartanOperator_graph : (pairedActualCartanOperator period hPeriod reference metric).graph =
    pairedActualCartanGraph period hPeriod reference metric := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun graph => graph.val.2)
    (pairedActualCartanGraph_input_injective period hPeriod reference metric (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem pairedActualCartanOperator_isClosed : (pairedActualCartanOperator period hPeriod reference metric).IsClosed := by
  rw [LinearPMap.IsClosed, pairedActualCartanOperator_graph]
  exact pairedActualCartanGraph_isClosed period hPeriod reference metric

def actualCartanGhostSmooth : (Fin 4 → SmoothScalarField period hPeriod) →ₗ[Real]
    ActualCartanGhostL2 period hPeriod reference metric :=
  (regularGhostL2EquivRange period hPeriod reference (metric .plus)).toLinearMap.comp
    (regularFrameGhostL2 period hPeriod)

def actualPairedCartanSmoothOutput (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    ActualPairedCartanTensorL2 period hPeriod :=
  WithLp.toLp 2
    (frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)
      (smoothMetricCartanAction period hPeriod (regularFrameGhostFromCoefficients period hPeriod reference coefficients)
        (metric .plus).tensor),
     frameTensorL2Smooth period hPeriod (finiteSmoothTangentFrame period hPeriod)
      (smoothMetricCartanAction period hPeriod (regularFrameGhostFromCoefficients period hPeriod reference coefficients)
        (metric .minus).tensor))

theorem pairedActualCartanRecovery_smooth (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    pairedActualCartanRecovery period hPeriod reference (actualPairedCartanSmoothOutput period hPeriod reference metric coefficients) =
      pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact (regularTensorL2Recovery_smooth period hPeriod reference _).trans
      (regularFrameCartanL2_eq_tensorL2 period hPeriod reference (metric .plus).tensor coefficients).symm
  · exact (regularTensorL2Recovery_smooth period hPeriod reference _).trans
      (regularFrameCartanL2_eq_tensorL2 period hPeriod reference (metric .minus).tensor coefficients).symm

theorem pairedActualCartan_smooth_graph (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    (actualCartanGhostSmooth period hPeriod reference metric coefficients,
      actualPairedCartanSmoothOutput period hPeriod reference metric coefficients) ∈
      (pairedActualCartanOperator period hPeriod reference metric).graph := by
  rw [pairedActualCartanOperator_graph]
  change ((regularGhostL2EquivRange period hPeriod reference (metric .plus)).symm
    ((regularGhostL2EquivRange period hPeriod reference (metric .plus)) (regularFrameGhostL2 period hPeriod coefficients)),
    pairedActualCartanRecovery period hPeriod reference (actualPairedCartanSmoothOutput period hPeriod reference metric coefficients)) ∈
      (pairedCartanMinimal period hPeriod reference metric).graph
  rw [ContinuousLinearEquiv.symm_apply_apply, pairedActualCartanRecovery_smooth]
  exact pairedCartanMinimal_smooth_graph period hPeriod reference metric coefficients

theorem actualCartanGhostSmooth_denseRange : DenseRange (actualCartanGhostSmooth period hPeriod reference metric) :=
  (regularGhostL2EquivRange period hPeriod reference (metric .plus)).surjective.denseRange.comp
    (regularFrameGhostL2_denseRange period hPeriod)
    (regularGhostL2EquivRange period hPeriod reference (metric .plus)).continuous

theorem pairedActualCartanOperator_denseDomain : Dense
    ((pairedActualCartanOperator period hPeriod reference metric).domain :
      Set (ActualCartanGhostL2 period hPeriod reference metric)) := by
  apply (actualCartanGhostSmooth_denseRange period hPeriod reference metric).mono
  rintro _ ⟨coefficients, rfl⟩
  obtain ⟨field, hField, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (pairedActualCartan_smooth_graph period hPeriod reference metric coefficients)
  exact (congrArg (fun value : ActualCartanGhostL2 period hPeriod reference metric =>
    value ∈ (pairedActualCartanOperator period hPeriod reference metric).domain) hField).mp field.property

end
end JanusFormal.P0EFTJanusProgramPT12PairedActualCartanClosed4D
