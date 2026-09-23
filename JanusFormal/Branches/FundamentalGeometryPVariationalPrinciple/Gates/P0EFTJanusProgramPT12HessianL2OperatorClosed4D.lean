import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianL2OperatorCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SymmetricL2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianSmoothRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianSmoothTestAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianL2Form4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismHessianFeatureClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricFlatL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SignedBRSTGram4D
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

/-! Minimal closed symmetric actual BRST Hessian in original L², with a dense smooth operator core. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianL2OperatorClosed4D
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

theorem hessianClosedGraph_pairing_smooth
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (hessianL2OperatorCore period hPeriod reference metric couplings).graph.topologicalClosure)
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real pair.2 (diffeomorphismL2Smooth period hPeriod (metric .plus) test) =
      inner Real pair.1 (hessianSmoothRiesz period hPeriod reference metric couplings test) := by
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus) |
      inner Real value.2 (diffeomorphismL2Smooth period hPeriod (metric .plus) test) =
        inner Real value.1 (hessianSmoothRiesz period hPeriod reference metric couplings test)} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hPair
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  rcases field with ⟨field, hField⟩
  obtain ⟨smooth, rfl⟩ := hField
  change inner Real value.2 _ = inner Real value.1 _
  rw [← hOutput, ← hInput, hessianL2OperatorCore_smooth]
  exact hessianSmoothRiesz_symmetric period hPeriod reference metric couplings smooth test

theorem hessianL2OperatorCore_isClosable : (hessianL2OperatorCore period hPeriod reference metric couplings).IsClosable := by
  refine ⟨(hessianL2OperatorCore period hPeriod reference metric couplings).graph.topologicalClosure.toLinearPMap, ?_⟩
  symm
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ hPair hZero
  change x = 0 at hZero
  subst x
  apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  have h := hessianClosedGraph_pairing_smooth period hPeriod reference metric couplings (0, y) hPair test
  exact h.trans (by simp only [inner_zero_left])
def hessianL2Minimal : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real] DiffeomorphismL2 period hPeriod (metric .plus) :=
  (hessianL2OperatorCore period hPeriod reference metric couplings).closure

theorem hessianL2Minimal_graph : (hessianL2Minimal period hPeriod reference metric couplings).graph =
    (hessianL2OperatorCore period hPeriod reference metric couplings).graph.topologicalClosure :=
  (hessianL2OperatorCore_isClosable period hPeriod reference metric couplings).graph_closure_eq_closure_graph.symm

theorem hessianL2Minimal_isClosed : (hessianL2Minimal period hPeriod reference metric couplings).IsClosed :=
  (hessianL2OperatorCore_isClosable period hPeriod reference metric couplings).closure_isClosed

theorem hessianL2Minimal_hasCore : (hessianL2Minimal period hPeriod reference metric couplings).HasCore
    (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  (hessianL2OperatorCore period hPeriod reference metric couplings).closureHasCore

theorem hessianL2Minimal_denseDomain : Dense
    ((hessianL2Minimal period hPeriod reference metric couplings).domain : Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).mono
    (fun _ h => (hessianL2OperatorCore period hPeriod reference metric couplings).le_closure.1 h)

def hessianL2SmoothDomain (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianL2Minimal period hPeriod reference metric couplings).domain :=
  ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field,
    (hessianL2OperatorCore period hPeriod reference metric couplings).le_closure.1 ⟨field, rfl⟩⟩

theorem hessianL2Minimal_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianL2Minimal period hPeriod reference metric couplings (hessianL2SmoothDomain period hPeriod reference metric couplings field) =
      hessianSmoothRiesz period hPeriod reference metric couplings field :=
  ((hessianL2OperatorCore period hPeriod reference metric couplings).le_closure.2 (x := ⟨_, ⟨field, rfl⟩⟩)
    (y := hessianL2SmoothDomain period hPeriod reference metric couplings field) rfl).symm.trans
      (hessianL2OperatorCore_smooth period hPeriod reference metric couplings field)

theorem hessianL2Minimal_smooth_actual_pairing (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (hessianL2Minimal period hPeriod reference metric couplings
      (hessianL2SmoothDomain period hPeriod reference metric couplings first))
      (diffeomorphismL2Smooth period hPeriod (metric .plus) second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings metric first second := by
  rw [hessianL2Minimal_smooth]
  exact hessianSmoothRiesz_actual_pairing period hPeriod reference metric couplings first second

theorem hessianL2Minimal_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
      (F := DiffeomorphismL2 period hPeriod (metric .plus))
      (hessianL2Minimal period hPeriod reference metric couplings)
      (hessianL2Minimal period hPeriod reference metric couplings) := by
  intro first second
  have hFirst : (first.val, hessianL2Minimal period hPeriod reference metric couplings first) ∈
      (hessianL2OperatorCore period hPeriod reference metric couplings).graph.topologicalClosure := by
    rw [← hessianL2Minimal_graph]
    exact (hessianL2Minimal period hPeriod reference metric couplings).mem_graph first
  have hSecond : (second.val, hessianL2Minimal period hPeriod reference metric couplings second) ∈
      (hessianL2OperatorCore period hPeriod reference metric couplings).graph.topologicalClosure := by
    rw [← hessianL2Minimal_graph]
    exact (hessianL2Minimal period hPeriod reference metric couplings).mem_graph second
  have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus) |
      inner Real (hessianL2Minimal period hPeriod reference metric couplings first) value.1 = inner Real first.val value.2} := by
    apply isClosed_eq <;> fun_prop
  apply (closure_minimal _ hClosed) hSecond
  intro value hValue
  obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
  rcases field with ⟨field, hField⟩
  obtain ⟨smooth, rfl⟩ := hField
  change inner Real (hessianL2Minimal period hPeriod reference metric couplings first) value.1 = inner Real first.val value.2
  rw [← hInput, ← hOutput, hessianL2OperatorCore_smooth]
  exact hessianClosedGraph_pairing_smooth period hPeriod reference metric couplings _ hFirst smooth

theorem hessianL2Minimal_le_adjoint : hessianL2Minimal period hPeriod reference metric couplings ≤
    LinearPMap.adjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
      (F := DiffeomorphismL2 period hPeriod (metric .plus)) (hessianL2Minimal period hPeriod reference metric couplings) :=
  symmetric_le_adjoint (H := DiffeomorphismL2 period hPeriod (metric .plus))
    (hessianL2Minimal period hPeriod reference metric couplings)
    (hessianL2Minimal_denseDomain period hPeriod reference metric couplings)
    (hessianL2Minimal_isFormalAdjoint period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12HessianL2OperatorClosed4D
