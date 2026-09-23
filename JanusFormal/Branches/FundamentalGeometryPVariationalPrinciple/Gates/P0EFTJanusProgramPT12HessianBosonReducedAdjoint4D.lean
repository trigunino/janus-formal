import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonReducedCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMaximal4D

/-! The actual metric–B Hessian adjoint is the restriction of the full maximal Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianBosonReducedAdjoint4D
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
open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D

local instance bosonPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)).range
open P0EFTJanusProgramPT12HessianBosonReduced4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D

open P0EFTJanusProgramPT12HessianBosonReducedCore4D
open P0EFTJanusProgramPT12ClosedFeatureAdjoint4D
open P0EFTJanusProgramPT12HessianL2Adjoint4D
open P0EFTJanusProgramPT12HessianGhostMaximal4D

attribute [local irreducible] hessianBosonReduced

def hessianBosonReducedAdjoint :
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  LinearPMap.adjoint (𝕜 := Real)
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (hessianBosonReduced period hPeriod reference metric couplings)

private theorem featureClosure_pairing_of_smooth
    {D H : Type*} [AddCommGroup D] [Module Real D]
    [NormedAddCommGroup H] [InnerProductSpace Real H]
    (inclusion operator : D →ₗ[Real] H) (input output : H)
    (h : ∀ test, inner Real (operator test) input = inner Real (inclusion test) output)
    (first second : H) (hGraph : (first, second) ∈ linearFeatureGraphClosure inclusion operator) :
    inner Real second input = inner Real first output := by
  have hClosed : IsClosed {pair : H × H | inner Real pair.2 input = inner Real pair.1 output} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal (by rintro pair ⟨test, rfl⟩; exact h test) hClosed hGraph
attribute [local irreducible] linearFeatureGraphClosure

theorem hessianBosonReducedAdjoint_graph_iff_smooth
    (input output : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianBosonReducedAdjoint period hPeriod reference metric couplings).graph ↔
      ∀ test, inner Real (hessianBosonReducedSmoothOutput period hPeriod reference metric couplings test) input =
        inner Real (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) test) output := by
  unfold hessianBosonReducedAdjoint
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (T := hessianBosonReduced period hPeriod reference metric couplings) (𝕜 := Real)
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (hessianBosonReduced_denseDomain period hPeriod reference metric couplings),
    hessianBosonReduced_graph_closure, Submodule.mem_adjoint_iff]
  constructor
  · intro h test
    have hMem := hessianBosonReduced_smooth_graph period hPeriod reference metric couplings test
    rw [hessianBosonReduced_graph_closure] at hMem
    exact sub_eq_zero.mp (h
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) test)
      (hessianBosonReducedSmoothOutput period hPeriod reference metric couplings test) hMem)
  · intro h first second hGraph
    exact sub_eq_zero.mpr (featureClosure_pairing_of_smooth
      (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
      (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus))
      (hessianBosonReducedSmoothLinearMap period hPeriod reference metric couplings)
      input output h first second hGraph)
theorem hessianBosonReducedAdjoint_graph_iff
    (input output : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianBosonReducedAdjoint period hPeriod reference metric couplings).graph ↔
      (input.val, output.val) ∈ (hessianL2Maximal period hPeriod reference metric couplings).graph := by
  rw [hessianBosonReducedAdjoint_graph_iff_smooth, hessianL2Maximal_graph_iff]
  have hFixed (field : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
      diffeomorphismBosonProjection period hPeriod (metric .plus) field.val = field.val := by
    exact (Set.ext_iff.mp (diffeomorphismBosonProjection_range_eq_fixed period hPeriod (metric .plus)) field.val).mp field.property
  apply forall_congr'
  intro test
  change (inner Real
      (diffeomorphismBosonProjection period hPeriod (metric .plus)
        (hessianSmoothRiesz period hPeriod reference metric couplings test)) input.val =
    inner Real
      (diffeomorphismBosonProjection period hPeriod (metric .plus)
        (diffeomorphismL2Smooth period hPeriod (metric .plus) test)) output.val) ↔ _
  rw [diffeomorphismBosonProjection_pairing, diffeomorphismBosonProjection_pairing,
    hFixed input, hFixed output]
  constructor <;> intro h
  · exact (real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _))
  · exact (real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _))

theorem hessianBosonReducedAdjoint_domain_iff
    (input : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    input ∈ (hessianBosonReducedAdjoint period hPeriod reference metric couplings).domain ↔
      input.val ∈ (hessianL2Maximal period hPeriod reference metric couplings).domain := by
  constructor
  · intro hInput
    obtain ⟨field, hField, _⟩ := (LinearPMap.mem_graph_iff _).mp
      ((hessianBosonReducedAdjoint_graph_iff period hPeriod reference metric couplings _ _).mp
        ((hessianBosonReducedAdjoint period hPeriod reference metric couplings).mem_graph ⟨input, hInput⟩))
    change field.val = input.val at hField
    rw [← hField]
    exact field.property
  · intro hInput
    let field : (hessianL2Maximal period hPeriod reference metric couplings).domain := ⟨input.val, hInput⟩
    let output : DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
      (diffeomorphismBosonProjection period hPeriod (metric .plus)).rangeRestrict
        (hessianL2Maximal period hPeriod reference metric couplings field)
    have hGraph := hessianL2Maximal_graph_boson period hPeriod reference metric couplings _
      ((hessianL2Maximal period hPeriod reference metric couplings).mem_graph field)
    have hFixed : diffeomorphismBosonProjection period hPeriod (metric .plus) input.val = input.val := by
      exact (Set.ext_iff.mp (diffeomorphismBosonProjection_range_eq_fixed period hPeriod (metric .plus)) input.val).mp input.property
    change (diffeomorphismBosonProjection period hPeriod (metric .plus) input.val, output.val) ∈ _ at hGraph
    rw [hFixed] at hGraph
    obtain ⟨vector, hVector, _⟩ := (LinearPMap.mem_graph_iff _).mp
      ((hessianBosonReducedAdjoint_graph_iff period hPeriod reference metric couplings input output).mpr hGraph)
    change vector.val = input at hVector
    rw [← hVector]
    exact vector.property

end
end JanusFormal.P0EFTJanusProgramPT12HessianBosonReducedAdjoint4D
