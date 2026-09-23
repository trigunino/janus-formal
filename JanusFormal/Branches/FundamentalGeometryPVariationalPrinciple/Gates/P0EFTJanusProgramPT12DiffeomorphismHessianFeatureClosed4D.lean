import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Closed simultaneous de Donder and Faddeev--Popov features with one actual smooth core. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
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
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

open P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
open P0EFTJanusProgramPT12RegularGhostL2Recovery4D
open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FaddeevPopovL2Core4D
open P0EFTJanusProgramPT12FaddeevPopovL2Closed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusProgramPT12FrameCovectorL2Transport4D
open P0EFTJanusProgramPT12FrameCovectorL2Equiv4D
open P0EFTJanusProgramPT12RegularGhostL2Equiv4D
open P0EFTJanusProgramPT12PairedFaddeevPopovClosed4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

open P0EFTJanusProgramPT12ActualFaddeevPopovCore4D
open P0EFTJanusProgramPT12DeDonderL2Closed4D

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
variable (reference : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D

theorem hessianFeature_closedGraph_deDonder
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod)
    (hPair : pair ∈ (hessianFeatureCore period hPeriod metric).graph.topologicalClosure)
    (sector : Sector) (row : Fin (finiteSmoothTangentFrame period hPeriod).count) (test : SmoothScalarField period hPeriod) :
    inner Real ((pair.2 (0, sector)).val row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (diffeomorphismTensorReadout period hPeriod (metric .plus) sector pair.1)
        (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) (metric sector) reference row test) := by
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod |
      inner Real ((value.2 (0, sector)).val row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
        inner Real (diffeomorphismTensorReadout period hPeriod (metric .plus) sector value.1)
          (deDonderRowAdjoint period hPeriod (finiteSmoothTangentFrame period hPeriod) (metric sector) reference row test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real ((value.2 (0, sector)).val row) _ =
    inner Real (diffeomorphismTensorReadout period hPeriod (metric .plus) sector value.1) _
  rw [← hOutput, ← hInput]
  exact hessianFeatureCore_deDonder_pairing period hPeriod metric reference field sector row test

theorem hessianFeature_closedGraph_fp
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod)
    (hPair : pair ∈ (hessianFeatureCore period hPeriod metric).graph.topologicalClosure)
    (sector : Sector) (row : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (actualFPCovectorRecovery period hPeriod reference (pair.2 (1, sector)) row)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (regularGhostL2Recovery period hPeriod reference (metric .plus)
      (diffeomorphismTripletReadout period hPeriod (metric .plus) 0 pair.1))
      (fpRowAdjointTest period hPeriod reference (metric sector) row test) := by
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod |
      inner Real (actualFPCovectorRecovery period hPeriod reference (value.2 (1, sector)) row)
        (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (regularGhostL2Recovery period hPeriod reference (metric .plus)
        (diffeomorphismTripletReadout period hPeriod (metric .plus) 0 value.1))
        (fpRowAdjointTest period hPeriod reference (metric sector) row test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real (actualFPCovectorRecovery period hPeriod reference (value.2 (1, sector)) row) _ =
    inner Real (regularGhostL2Recovery period hPeriod reference (metric .plus)
      (diffeomorphismTripletReadout period hPeriod (metric .plus) 0 value.1)) _
  rw [← hOutput, ← hInput]
  exact hessianFeatureCore_fp_pairing period hPeriod metric reference field sector row test

include reference in
theorem hessianFeatureCore_isClosable : (hessianFeatureCore period hPeriod metric).IsClosable := by
  refine ⟨(hessianFeatureCore period hPeriod metric).graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hPair hZero
  change x = 0 at hZero
  subst x
  apply PiLp.ext
  rintro ⟨kind, sector⟩
  fin_cases kind
  · apply Subtype.ext
    apply PiLp.ext
    intro row
    apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    change inner Real ((y (0, sector)).val row) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) = 0
    have h := hessianFeature_closedGraph_deDonder period hPeriod metric reference (0, y) hPair sector row test
    exact h.trans (by simp only [map_zero, inner_zero_left])
  · apply actualFPCovectorRecovery_injective period hPeriod reference
    change actualFPCovectorRecovery period hPeriod reference (y (1, sector)) = actualFPCovectorRecovery period hPeriod reference 0
    rw [map_zero]
    apply PiLp.ext
    intro row
    apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    have h := hessianFeature_closedGraph_fp period hPeriod metric reference (0, y) hPair sector row test
    simpa only [map_zero, inner_zero_left] using h

def hessianFeatureMinimal : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real] HessianFeatureL2 period hPeriod :=
  (hessianFeatureCore period hPeriod metric).closure

include reference in
theorem hessianFeatureMinimal_isClosed : (hessianFeatureMinimal period hPeriod metric).IsClosed :=
  (hessianFeatureCore_isClosable period hPeriod metric reference).closure_isClosed

include reference in
theorem hessianFeatureMinimal_graph : (hessianFeatureMinimal period hPeriod metric).graph =
    (hessianFeatureCore period hPeriod metric).graph.topologicalClosure :=
  (hessianFeatureCore_isClosable period hPeriod metric reference).graph_closure_eq_closure_graph.symm

theorem hessianFeatureMinimal_hasCore : (hessianFeatureMinimal period hPeriod metric).HasCore
    (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  (hessianFeatureCore period hPeriod metric).closureHasCore

theorem hessianFeatureMinimal_denseDomain : Dense
    ((hessianFeatureMinimal period hPeriod metric).domain : Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).mono
    (fun _ h => (hessianFeatureCore period hPeriod metric).le_closure.1 h)

def hessianFeatureSmoothDomain (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFeatureMinimal period hPeriod metric).domain :=
  ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field, (hessianFeatureCore period hPeriod metric).le_closure.1 ⟨field, rfl⟩⟩

theorem hessianFeatureMinimal_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianFeatureMinimal period hPeriod metric (hessianFeatureSmoothDomain period hPeriod metric field) =
      hessianFeaturesSmooth period hPeriod metric field :=
  ((hessianFeatureCore period hPeriod metric).le_closure.2 (x := ⟨_, ⟨field, rfl⟩⟩)
    (y := hessianFeatureSmoothDomain period hPeriod metric field) rfl).symm.trans
      (hessianFeatureCore_smooth period hPeriod metric field)

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
