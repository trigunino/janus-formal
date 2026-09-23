import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

/-! Closed paired metric Cartan realization with a single shared L² ghost. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedRegularFrameCartan4D
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

variable (reference : RegularGeneralLorentzMetric period hPeriod)


open Set
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

abbrev PairedCartanTensorL2 := WithLp 2 (CartanTensorL2 period hPeriod × CartanTensorL2 period hPeriod)

private def plusReadout : (CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod) →L[Real]
    (CartanGhostL2 period hPeriod × CartanTensorL2 period hPeriod) :=
  (ContinuousLinearMap.fst Real _ _).prod
    ((WithLp.fstL 2 Real _ _).comp (ContinuousLinearMap.snd Real _ _))

private def minusReadout : (CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod) →L[Real]
    (CartanGhostL2 period hPeriod × CartanTensorL2 period hPeriod) :=
  (ContinuousLinearMap.fst Real _ _).prod
    ((WithLp.sndL 2 Real _ _).comp (ContinuousLinearMap.snd Real _ _))

/-- Intersection of the two closed graph conditions with one common ghost input. -/
def pairedRegularFrameCartanGraph : Submodule Real
    (CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod) :=
  (regularFrameCartanGraph period hPeriod reference (metric .plus).tensor).comap
    (plusReadout period hPeriod).toLinearMap ⊓
  (regularFrameCartanGraph period hPeriod reference (metric .minus).tensor).comap
    (minusReadout period hPeriod).toLinearMap

theorem pairedRegularFrameCartanGraph_isClosed :
    IsClosed (pairedRegularFrameCartanGraph period hPeriod reference metric :
      Set (CartanGhostL2 period hPeriod × PairedCartanTensorL2 period hPeriod)) := by
  have hPlus := (regularFrameCartanMinimal_isClosed period hPeriod reference (metric .plus).tensor)
  have hMinus := (regularFrameCartanMinimal_isClosed period hPeriod reference (metric .minus).tensor)
  rw [LinearPMap.IsClosed, regularFrameCartanMinimal_graph] at hPlus hMinus
  exact (hPlus.preimage (plusReadout period hPeriod).continuous).inter
    (hMinus.preimage (minusReadout period hPeriod).continuous)

theorem pairedRegularFrameCartanGraph_input_injective :
    Function.Injective (fun graph : pairedRegularFrameCartanGraph period hPeriod reference metric => graph.val.1) := by
  intro x y hInput
  apply Subtype.ext
  refine Prod.ext hInput ?_
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact congrArg (fun graph => graph.val.2)
      (regularFrameCartanGraph_input_injective period hPeriod reference (metric .plus).tensor
        (a₁ := ⟨plusReadout period hPeriod x.val, x.property.1⟩)
        (a₂ := ⟨plusReadout period hPeriod y.val, y.property.1⟩) hInput)
  · exact congrArg (fun graph => graph.val.2)
      (regularFrameCartanGraph_input_injective period hPeriod reference (metric .minus).tensor
        (a₁ := ⟨minusReadout period hPeriod x.val, x.property.2⟩)
        (a₂ := ⟨minusReadout period hPeriod y.val, y.property.2⟩) hInput)

def pairedRegularFrameCartanOperator :
    CartanGhostL2 period hPeriod →ₗ.[Real] PairedCartanTensorL2 period hPeriod :=
  (pairedRegularFrameCartanGraph period hPeriod reference metric).toLinearPMap

theorem pairedRegularFrameCartanOperator_graph :
    (pairedRegularFrameCartanOperator period hPeriod reference metric).graph =
      pairedRegularFrameCartanGraph period hPeriod reference metric := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun graph => graph.val.2)
    (pairedRegularFrameCartanGraph_input_injective period hPeriod reference metric
      (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem pairedRegularFrameCartanOperator_isClosed :
    (pairedRegularFrameCartanOperator period hPeriod reference metric).IsClosed := by
  rw [LinearPMap.IsClosed, pairedRegularFrameCartanOperator_graph]
  exact pairedRegularFrameCartanGraph_isClosed period hPeriod reference metric

def pairedRegularFrameCartanSmoothOutput (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    PairedCartanTensorL2 period hPeriod :=
  WithLp.toLp 2 (regularFrameCartanL2 period hPeriod reference (metric .plus).tensor coefficients,
    regularFrameCartanL2 period hPeriod reference (metric .minus).tensor coefficients)

theorem pairedRegularFrameCartanSmoothOutput_actual
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) (sector : Sector)
    (first second : Fin 4) :
    (match sector with
      | .plus => WithLp.fst (pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients)
      | .minus => WithLp.snd (pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients))
        (first, second) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (regularFrameSymmetricTensorCoefficient period hPeriod reference
          (globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap period hPeriod metric
            ⟨regularFrameGhostFromCoefficients period hPeriod reference coefficients⟩ sector) first second) := by
  cases sector with
  | plus => exact regularFrameCartanL2_actual period hPeriod reference (metric .plus).tensor coefficients first second
  | minus => exact regularFrameCartanL2_actual period hPeriod reference (metric .minus).tensor coefficients first second

theorem pairedRegularFrameCartan_smooth_graph (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    (regularFrameGhostL2 period hPeriod coefficients,
      pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients) ∈
      (pairedRegularFrameCartanOperator period hPeriod reference metric).graph := by
  rw [pairedRegularFrameCartanOperator_graph]
  exact ⟨Submodule.le_topologicalClosure _ ⟨coefficients, rfl⟩,
    Submodule.le_topologicalClosure _ ⟨coefficients, rfl⟩⟩

theorem pairedRegularFrameCartanOperator_denseDomain :
    Dense ((pairedRegularFrameCartanOperator period hPeriod reference metric).domain :
      Set (CartanGhostL2 period hPeriod)) := by
  apply (regularFrameGhostL2_denseRange period hPeriod).mono
  rintro _ ⟨coefficients, rfl⟩
  have h := pairedRegularFrameCartan_smooth_graph period hPeriod reference metric coefficients
  obtain ⟨x, hx, _⟩ := (pairedRegularFrameCartanOperator period hPeriod reference metric).mem_graph_iff.mp h
  exact (congrArg (fun value : CartanGhostL2 period hPeriod =>
    value ∈ (pairedRegularFrameCartanOperator period hPeriod reference metric).domain) hx).mp x.property

end
end JanusFormal.P0EFTJanusProgramPT12PairedRegularFrameCartan4D
