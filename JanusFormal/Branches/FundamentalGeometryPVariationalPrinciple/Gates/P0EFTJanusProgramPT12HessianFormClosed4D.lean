import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianFormSmoothCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SymmetricL2GraphClosure4D

/-! A closed symmetric realization of the BRST form between the minimal and maximal Hessians. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianFormClosed4D
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

open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureCore4D
open P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
open P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
open P0EFTJanusProgramPT12SignedBRSTGram4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace

open P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
open P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D

open P0EFTJanusProgramPT12HessianSmoothRiesz4D
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12HessianL2OperatorCore4D
open P0EFTJanusProgramPT12SymmetricL2Closure4D

open P0EFTJanusProgramPT12HessianL2OperatorClosed4D


open P0EFTJanusProgramPT12HessianL2Adjoint4D
open P0EFTJanusProgramPT12HessianFormGraphTests4D

open P0EFTJanusProgramPT12HessianFormAdjoint4D

open P0EFTJanusProgramPT12HessianFormOperator4D

open P0EFTJanusProgramPT12HessianFormSmoothCore4D
open P0EFTJanusProgramPT12SymmetricL2GraphClosure4D

def hessianFormClosed : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  (hessianL2FormOperator period hPeriod reference metric couplings).closure

theorem hessianFormClosed_graph : (hessianFormClosed period hPeriod reference metric couplings).graph =
    (hessianL2FormOperator period hPeriod reference metric couplings).graph.topologicalClosure :=
  (hessianL2FormOperator_isClosable period hPeriod reference metric couplings).graph_closure_eq_closure_graph.symm

theorem hessianFormClosed_isClosed : (hessianFormClosed period hPeriod reference metric couplings).IsClosed :=
  (hessianL2FormOperator_isClosable period hPeriod reference metric couplings).closure_isClosed

theorem hessianFormClosed_hasCore : (hessianFormClosed period hPeriod reference metric couplings).HasCore
    (hessianL2FormOperator period hPeriod reference metric couplings).domain :=
  (hessianL2FormOperator period hPeriod reference metric couplings).closureHasCore

theorem hessianL2FormOperator_le_closed : hessianL2FormOperator period hPeriod reference metric couplings ≤
    hessianFormClosed period hPeriod reference metric couplings :=
  (hessianL2FormOperator period hPeriod reference metric couplings).le_closure

theorem hessianFormClosed_denseDomain : Dense
    ((hessianFormClosed period hPeriod reference metric couplings).domain : Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  (hessianL2FormOperator_denseDomain period hPeriod reference metric couplings).mono
    (hessianL2FormOperator_le_closed period hPeriod reference metric couplings).1

theorem hessianFormClosedGraph_pairing_form
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (hessianL2FormOperator period hPeriod reference metric couplings).graph.topologicalClosure)
    (test : (hessianL2FormOperator period hPeriod reference metric couplings).domain) :
    inner Real pair.2 test.val = inner Real pair.1 (hessianL2FormOperator period hPeriod reference metric couplings test) := by
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus) |
      inner Real value.2 test.val = inner Real value.1 (hessianL2FormOperator period hPeriod reference metric couplings test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real value.2 test.val = inner Real value.1 _
  rw [← hInput, ← hOutput]
  exact hessianL2FormOperator_isFormalAdjoint period hPeriod reference metric couplings field test

theorem hessianFormClosed_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
      (F := DiffeomorphismL2 period hPeriod (metric .plus))
      (hessianFormClosed period hPeriod reference metric couplings)
      (hessianFormClosed period hPeriod reference metric couplings) := by
  intro first second
  have hFirst : (first.val, hessianFormClosed period hPeriod reference metric couplings first) ∈
      (hessianL2FormOperator period hPeriod reference metric couplings).graph.topologicalClosure := by
    rw [← hessianFormClosed_graph]
    exact (hessianFormClosed period hPeriod reference metric couplings).mem_graph first
  have hSecond : (second.val, hessianFormClosed period hPeriod reference metric couplings second) ∈
      (hessianL2FormOperator period hPeriod reference metric couplings).graph.topologicalClosure := by
    rw [← hessianFormClosed_graph]
    exact (hessianFormClosed period hPeriod reference metric couplings).mem_graph second
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus) |
      inner Real (hessianFormClosed period hPeriod reference metric couplings first) value.1 = inner Real first.val value.2} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hSecond
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  change inner Real (hessianFormClosed period hPeriod reference metric couplings first) value.1 = inner Real first.val value.2
  rw [← hInput, ← hOutput]
  exact hessianFormClosedGraph_pairing_form period hPeriod reference metric couplings _ hFirst field
theorem hessianL2Minimal_le_formClosed : hessianL2Minimal period hPeriod reference metric couplings ≤
    hessianFormClosed period hPeriod reference metric couplings :=
  (hessianL2FormOperator_isClosable period hPeriod reference metric couplings).closure_mono
    (hessianL2OperatorCore_le_formOperator period hPeriod reference metric couplings)

theorem hessianFormClosed_le_maximal : hessianFormClosed period hPeriod reference metric couplings ≤
    hessianL2Maximal period hPeriod reference metric couplings :=
by
  apply LinearPMap.le_of_le_graph
  rw [hessianFormClosed_graph]
  exact closure_minimal
    (LinearPMap.le_graph_of_le (hessianL2FormOperator_le_maximal period hPeriod reference metric couplings))
    (hessianL2Maximal_isClosed period hPeriod reference metric couplings)
def hessianFormClosedSmoothDomain (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFormClosed period hPeriod reference metric couplings).domain :=
  ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field,
    (hessianL2Minimal_le_formClosed period hPeriod reference metric couplings).1
      (hessianL2SmoothDomain period hPeriod reference metric couplings field).property⟩

theorem hessianFormClosed_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianFormClosed period hPeriod reference metric couplings
      (hessianFormClosedSmoothDomain period hPeriod reference metric couplings field) =
        hessianSmoothRiesz period hPeriod reference metric couplings field :=
  ((hessianL2Minimal_le_formClosed period hPeriod reference metric couplings).2
    (x := hessianL2SmoothDomain period hPeriod reference metric couplings field)
    (y := hessianFormClosedSmoothDomain period hPeriod reference metric couplings field) rfl).symm.trans
      (hessianL2Minimal_smooth period hPeriod reference metric couplings field)

theorem hessianFormClosed_smooth_actual_pairing
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (hessianFormClosed period hPeriod reference metric couplings
      (hessianFormClosedSmoothDomain period hPeriod reference metric couplings first))
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings metric first second := by
  rw [hessianFormClosed_smooth]
  exact hessianSmoothRiesz_actual_pairing period hPeriod reference metric couplings first second

theorem hessianFormClosed_pairing
    (input : (hessianFormClosed period hPeriod reference metric couplings).domain)
    (hDifferential : input.val ∈ (hessianFeatureMinimal period hPeriod metric).domain)
    (test : (hessianFeatureMinimal period hPeriod metric).domain) :
    inner Real (hessianFormClosed period hPeriod reference metric couplings input) test.val =
      hessianL2Form period hPeriod reference metric couplings ⟨input.val, hDifferential⟩ test :=
  (hessianL2Maximal_graph_iff_form period hPeriod reference metric couplings ⟨input.val, hDifferential⟩ _).mp
    (LinearPMap.le_graph_of_le (hessianFormClosed_le_maximal period hPeriod reference metric couplings)
      ((hessianFormClosed period hPeriod reference metric couplings).mem_graph input)) test

end
end JanusFormal.P0EFTJanusProgramPT12HessianFormClosed4D