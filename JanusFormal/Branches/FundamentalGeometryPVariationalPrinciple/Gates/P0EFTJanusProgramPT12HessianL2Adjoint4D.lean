import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianL2OperatorClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DenseL2AdjointGraph4D

/-! The actual BRST maximal Hessian, with an exact weak smooth-test domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianL2Adjoint4D
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
open P0EFTJanusProgramPT12DenseL2AdjointGraph4D

def hessianL2Maximal : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  LinearPMap.adjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (F := DiffeomorphismL2 period hPeriod (metric .plus))
    (hessianL2Minimal period hPeriod reference metric couplings)

theorem hessianL2Maximal_graph_iff (input output : DiffeomorphismL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianL2Maximal period hPeriod reference metric couplings).graph ↔
      ∀ test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod,
        inner Real output (diffeomorphismL2Smooth period hPeriod (metric .plus) test) =
          inner Real input (hessianSmoothRiesz period hPeriod reference metric couplings test) := by
  rw [hessianL2Maximal, adjoint_graph_iff (H := DiffeomorphismL2 period hPeriod (metric .plus)) (hessianL2Minimal period hPeriod reference metric couplings)
    (hessianL2Minimal_denseDomain period hPeriod reference metric couplings)]
  constructor
  · intro h test
    have hTest := h (hessianL2SmoothDomain period hPeriod reference metric couplings test)
    rw [hessianL2Minimal_smooth] at hTest
    exact hTest
  · intro h test
    have hPair : (test.val, hessianL2Minimal period hPeriod reference metric couplings test) ∈
        (hessianL2OperatorCore period hPeriod reference metric couplings).graph.topologicalClosure := by
      rw [← hessianL2Minimal_graph]
      exact (hessianL2Minimal period hPeriod reference metric couplings).mem_graph test
    have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) ×
        DiffeomorphismL2 period hPeriod (metric .plus) |
        inner Real output value.1 = inner Real input value.2} := by
      apply isClosed_eq <;> fun_prop
    apply (closure_minimal _ hClosed) hPair
    intro value hValue
    obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
    rcases field with ⟨field, hField⟩
    obtain ⟨smooth, rfl⟩ := hField
    change inner Real output value.1 = inner Real input value.2
    rw [← hInput, ← hOutput, hessianL2OperatorCore_smooth]
    exact h smooth

theorem hessianL2Maximal_domain_iff (input : DiffeomorphismL2 period hPeriod (metric .plus)) :
    input ∈ (hessianL2Maximal period hPeriod reference metric couplings).domain ↔
      ∃ output : DiffeomorphismL2 period hPeriod (metric .plus),
        ∀ test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod,
          inner Real output (diffeomorphismL2Smooth period hPeriod (metric .plus) test) =
            inner Real input (hessianSmoothRiesz period hPeriod reference metric couplings test) := by
  rw [LinearPMap.mem_domain_iff]
  exact exists_congr fun output => hessianL2Maximal_graph_iff period hPeriod reference metric couplings input output

theorem hessianL2Maximal_isClosed : (hessianL2Maximal period hPeriod reference metric couplings).IsClosed := by
  change IsClosed ((hessianL2Maximal period hPeriod reference metric couplings).graph :
    Set (DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus)))
  have hGraph : ((hessianL2Maximal period hPeriod reference metric couplings).graph :
      Set (DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))) =
      ⋂ test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod,
        {value | inner Real value.2 (diffeomorphismL2Smooth period hPeriod (metric .plus) test) =
          inner Real value.1 (hessianSmoothRiesz period hPeriod reference metric couplings test)} := by
    ext value
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact hessianL2Maximal_graph_iff period hPeriod reference metric couplings value.1 value.2
  rw [hGraph]
  apply isClosed_iInter
  intro test
  apply isClosed_eq <;> fun_prop
theorem hessianL2Minimal_le_maximal : hessianL2Minimal period hPeriod reference metric couplings ≤
    hessianL2Maximal period hPeriod reference metric couplings :=
  hessianL2Minimal_le_adjoint period hPeriod reference metric couplings

theorem hessianL2Maximal_denseDomain : Dense
    ((hessianL2Maximal period hPeriod reference metric couplings).domain : Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  (hessianL2Minimal_denseDomain period hPeriod reference metric couplings).mono
    (hessianL2Minimal_le_maximal period hPeriod reference metric couplings).1

end
end JanusFormal.P0EFTJanusProgramPT12HessianL2Adjoint4D