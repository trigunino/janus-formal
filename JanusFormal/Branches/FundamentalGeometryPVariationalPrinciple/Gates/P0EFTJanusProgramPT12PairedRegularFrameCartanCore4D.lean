import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedRegularFrameCartan4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

/-! Minimal paired Cartan realization with a genuine common smooth operator core. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
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

open P0EFTJanusProgramPT12PairedRegularFrameCartan4D

theorem pairedCartan_smooth_mem (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameGhostL2 period hPeriod coefficients ∈
      (pairedRegularFrameCartanOperator period hPeriod reference metric).domain := by
  obtain ⟨x, hx, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (pairedRegularFrameCartan_smooth_graph period hPeriod reference metric coefficients)
  exact (congrArg (fun value : CartanGhostL2 period hPeriod =>
    value ∈ (pairedRegularFrameCartanOperator period hPeriod reference metric).domain) hx).mp x.property

theorem pairedCartan_smooth_apply (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    pairedRegularFrameCartanOperator period hPeriod reference metric
      ⟨regularFrameGhostL2 period hPeriod coefficients,
        pairedCartan_smooth_mem period hPeriod reference metric coefficients⟩ =
      pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients := by
  obtain ⟨x, hx, hy⟩ := (LinearPMap.mem_graph_iff _).mp
    (pairedRegularFrameCartan_smooth_graph period hPeriod reference metric coefficients)
  exact (congrArg (pairedRegularFrameCartanOperator period hPeriod reference metric)
    (Subtype.ext hx.symm)).trans hy

def pairedCartanSmoothRestriction :
    CartanGhostL2 period hPeriod →ₗ.[Real] PairedCartanTensorL2 period hPeriod :=
  (pairedRegularFrameCartanOperator period hPeriod reference metric).domRestrict
    (regularFrameGhostL2 period hPeriod).range

theorem pairedCartanSmoothRestriction_domain :
    (pairedCartanSmoothRestriction period hPeriod reference metric).domain =
      (regularFrameGhostL2 period hPeriod).range := by
  apply inf_eq_left.mpr
  rintro _ ⟨coefficients, rfl⟩
  exact pairedCartan_smooth_mem period hPeriod reference metric coefficients

theorem pairedCartanSmoothRestriction_isClosable :
    (pairedCartanSmoothRestriction period hPeriod reference metric).IsClosable :=
  (pairedRegularFrameCartanOperator_isClosed period hPeriod reference metric).isClosable.leIsClosable
    LinearPMap.domRestrict_le

/-- Both physical metric outputs are approximated along the same smooth ghost sequence. -/
def pairedCartanMinimal :
    CartanGhostL2 period hPeriod →ₗ.[Real] PairedCartanTensorL2 period hPeriod :=
  (pairedCartanSmoothRestriction period hPeriod reference metric).closure

theorem pairedCartanMinimal_isClosed :
    (pairedCartanMinimal period hPeriod reference metric).IsClosed :=
  (pairedCartanSmoothRestriction_isClosable period hPeriod reference metric).closure_isClosed

theorem pairedCartanMinimal_hasCore :
    (pairedCartanMinimal period hPeriod reference metric).HasCore
      (regularFrameGhostL2 period hPeriod).range := by
  have h := (pairedCartanSmoothRestriction period hPeriod reference metric).closureHasCore
  rw [pairedCartanSmoothRestriction_domain] at h
  exact h

theorem pairedCartanMinimal_le :
    pairedCartanMinimal period hPeriod reference metric ≤
      pairedRegularFrameCartanOperator period hPeriod reference metric := by
  apply LinearPMap.le_of_le_graph
  unfold pairedCartanMinimal
  rw [← (pairedCartanSmoothRestriction_isClosable period hPeriod reference metric).graph_closure_eq_closure_graph]
  exact closure_minimal (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le)
    (pairedRegularFrameCartanOperator_isClosed period hPeriod reference metric)

theorem pairedCartanMinimal_smooth_graph (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    (regularFrameGhostL2 period hPeriod coefficients,
      pairedRegularFrameCartanSmoothOutput period hPeriod reference metric coefficients) ∈
      (pairedCartanMinimal period hPeriod reference metric).graph := by
  apply LinearPMap.le_graph_of_le (pairedCartanSmoothRestriction period hPeriod reference metric).le_closure
  apply (LinearPMap.mem_graph_iff _).mpr
  refine ⟨⟨regularFrameGhostL2 period hPeriod coefficients,
    ⟨⟨coefficients, rfl⟩, pairedCartan_smooth_mem period hPeriod reference metric coefficients⟩⟩, rfl, ?_⟩
  exact (LinearPMap.domRestrict_apply
    (y := ⟨_, pairedCartan_smooth_mem period hPeriod reference metric coefficients⟩) rfl).trans
      (pairedCartan_smooth_apply period hPeriod reference metric coefficients)

theorem pairedCartanMinimal_denseDomain :
    Dense ((pairedCartanMinimal period hPeriod reference metric).domain :
      Set (CartanGhostL2 period hPeriod)) := by
  apply (regularFrameGhostL2_denseRange period hPeriod).mono
  rintro _ ⟨coefficients, rfl⟩
  exact (pairedCartanMinimal_hasCore period hPeriod reference metric).le_domain ⟨coefficients, rfl⟩

end
end JanusFormal.P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
