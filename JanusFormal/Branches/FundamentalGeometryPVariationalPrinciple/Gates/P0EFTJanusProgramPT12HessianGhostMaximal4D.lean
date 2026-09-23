import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMinimal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianL2Adjoint4D

/-! The maximal actual Hessian also reduces under the ghost and boson projections. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianGhostMaximal4D
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

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

open P0EFTJanusProgramPT12HessianGhostSmooth4D
open P0EFTJanusProgramPT12HessianSmoothRiesz4D
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12HessianGhostCommutation4D
open P0EFTJanusProgramPT12HessianL2OperatorCore4D
open P0EFTJanusProgramPT12HessianL2OperatorClosed4D

open P0EFTJanusProgramPT12HessianGhostMinimal4D
open P0EFTJanusProgramPT12HessianL2Adjoint4D

theorem hessianL2Maximal_graph_ghost
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (hessianL2Maximal period hPeriod reference metric couplings).graph) :
    (diffeomorphismGhostProjection period hPeriod (metric .plus) pair.1,
      diffeomorphismGhostProjection period hPeriod (metric .plus) pair.2) ∈
        (hessianL2Maximal period hPeriod reference metric couplings).graph := by
  apply (hessianL2Maximal_graph_iff period hPeriod reference metric couplings _ _).mpr
  intro test
  have hTest := (hessianL2Maximal_graph_iff period hPeriod reference metric couplings pair.1 pair.2).mp
    hPair (hessianGhostSmooth period hPeriod test)
  have hLeft := diffeomorphismGhostProjection_pairing period hPeriod (metric .plus) pair.2
    (diffeomorphismL2Smooth period hPeriod (metric .plus) test)
  rw [hessianGhostSmooth_L2] at hLeft
  have hRight := diffeomorphismGhostProjection_pairing period hPeriod (metric .plus) pair.1
    (hessianSmoothRiesz period hPeriod reference metric couplings test)
  rw [hessianSmoothRiesz_ghost_commutes] at hTest
  exact hLeft.trans (hTest.trans hRight.symm)

def hessianMaximalGhostDomain (field : (hessianL2Maximal period hPeriod reference metric couplings).domain) :
    (hessianL2Maximal period hPeriod reference metric couplings).domain := by
  refine ⟨diffeomorphismGhostProjection period hPeriod (metric .plus) field.val, ?_⟩
  have hPair := hessianL2Maximal_graph_ghost period hPeriod reference metric couplings
    (field.val, hessianL2Maximal period hPeriod reference metric couplings field)
    ((hessianL2Maximal period hPeriod reference metric couplings).mem_graph field)
  obtain ⟨projected, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp hPair
  change projected.val = diffeomorphismGhostProjection period hPeriod (metric .plus) field.val at hInput
  rw [← hInput]
  exact projected.property
theorem hessianL2Maximal_ghost_commutes
    (field : (hessianL2Maximal period hPeriod reference metric couplings).domain) :
    hessianL2Maximal period hPeriod reference metric couplings
      (hessianMaximalGhostDomain period hPeriod reference metric couplings field) =
    diffeomorphismGhostProjection period hPeriod (metric .plus)
      (hessianL2Maximal period hPeriod reference metric couplings field) := by
  obtain ⟨projected, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (hessianL2Maximal_graph_ghost period hPeriod reference metric couplings _
      ((hessianL2Maximal period hPeriod reference metric couplings).mem_graph field))
  have hEqual : projected = hessianMaximalGhostDomain period hPeriod reference metric couplings field := Subtype.ext hInput
  exact (congrArg (hessianL2Maximal period hPeriod reference metric couplings) hEqual).symm.trans hOutput

theorem hessianL2Maximal_graph_boson
    (pair : DiffeomorphismL2 period hPeriod (metric .plus) × DiffeomorphismL2 period hPeriod (metric .plus))
    (hPair : pair ∈ (hessianL2Maximal period hPeriod reference metric couplings).graph) :
    (diffeomorphismBosonProjection period hPeriod (metric .plus) pair.1,
      diffeomorphismBosonProjection period hPeriod (metric .plus) pair.2) ∈
        (hessianL2Maximal period hPeriod reference metric couplings).graph :=
by
  change (pair - (diffeomorphismGhostProjection period hPeriod (metric .plus) pair.1,
    diffeomorphismGhostProjection period hPeriod (metric .plus) pair.2)) ∈
      (hessianL2Maximal period hPeriod reference metric couplings).graph
  exact (hessianL2Maximal period hPeriod reference metric couplings).graph.sub_mem hPair
    (hessianL2Maximal_graph_ghost period hPeriod reference metric couplings pair hPair)

theorem hessianL2Minimal_ghost_boson_pairing_zero
    (field : (hessianL2Minimal period hPeriod reference metric couplings).domain)
    (test : DiffeomorphismL2 period hPeriod (metric .plus)) :
    inner Real (hessianL2Minimal period hPeriod reference metric couplings
      (hessianMinimalGhostDomain period hPeriod reference metric couplings field))
      (diffeomorphismBosonProjection period hPeriod (metric .plus) test) = 0 := by
  rw [hessianL2Minimal_ghost_commutes]
  exact diffeomorphismGhostBoson_orthogonal period hPeriod (metric .plus) _ test

end
end JanusFormal.P0EFTJanusProgramPT12HessianGhostMaximal4D