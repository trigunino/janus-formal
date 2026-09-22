import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedVolumeEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureVolumeTransport4D

/-! Exact volume conjugacy of the actual minimal FP and formal-adjoint graphs. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAFPVolumeGraph4D
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D


local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
set_option backward.isDefEq.respectTransparency false

open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D

open P0EFTJanusProgramPT12PairedFPClosable4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D

open P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings
  NonNullFace NullFace)

open P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

open P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
open P0EFTJanusProgramPT12ClosedFeatureAdjoint4D

open P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D

open P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
open P0EFTJanusProgramPT12PairedVolumeEquiv4D
open P0EFTJanusProgramPT12ClosedFeatureVolumeTransport4D

/-- The actual smooth adjoint intertwines with FP under multiplication by r. -/
theorem pairedFPCanonicalAdjointL2_volume
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    pairedFPCanonicalAdjointL2 period hPeriod metric
      (pairedSmoothVolumeWeight period hPeriod metric field) =
      pairedVolumeL2Equiv period hPeriod metric
        (globalPairedAbelianFPL2LinearMap period hPeriod metric field) := by
  have hInverse : pairedSmoothInverseVolumeWeight period hPeriod metric
      (pairedSmoothVolumeWeight period hPeriod metric field) = field := by
    apply globalPairedGaugeLieL2LinearMap_injective period hPeriod
    rw [← pairedVolumeL2Equiv_symm_smooth, ← pairedVolumeL2Equiv_smooth,
      ContinuousLinearEquiv.symm_apply_apply]
  change globalPairedGaugeLieL2LinearMap period hPeriod
    (pairedSmoothVolumeWeight period hPeriod metric (fun sector =>
      globalGeneralMetricAbelianFaddeevPopov period hPeriod (metric sector)
        (pairedSmoothInverseVolumeWeight period hPeriod metric
          (pairedSmoothVolumeWeight period hPeriod metric field) sector))) =
    pairedVolumeL2Equiv period hPeriod metric (globalPairedGaugeLieL2LinearMap period hPeriod
      (fun sector => globalGeneralMetricAbelianFaddeevPopov period hPeriod (metric sector) (field sector)))
  rw [hInverse, pairedVolumeL2Equiv_smooth]

/-- Exact equality of the two minimal closed graphs, with no maximal-domain assumption. -/
theorem candidateAFPFormalAdjointMinimal_volume_graph :
    (candidateAFPFormalAdjointMinimal period hPeriod data).graph =
      (candidateAFPCanonicalMinimal period hPeriod data).graph.map
        ((pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)).prodCongr
          (pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data))).toLinearMap := by
  rw [candidateAFPCanonicalMinimal_graph]
  change (closedFeatureOperator _ _).graph = _
  rw [closedFeatureOperator_graph _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data)]
  exact linearFeatureGraphClosure_volume_transport _ _ _
    (pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (pairedSmoothVolumeWeight period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (fun field => ⟨pairedSmoothInverseVolumeWeight period hPeriod _ field,
      pairedSmoothVolumeWeight_inverse period hPeriod _ field⟩)
    (fun field => (pairedVolumeL2Equiv_smooth period hPeriod _ field).symm)
    (pairedFPCanonicalAdjointL2_volume period hPeriod _)

theorem candidateAFPFormalAdjointMinimal_volume_mem_graph_iff
    (input output : GlobalPairedGaugeLieL2 period hPeriod) :
    (input, output) ∈ (candidateAFPFormalAdjointMinimal period hPeriod data).graph ↔
      ((pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)).symm input,
        (pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)).symm output) ∈
      (candidateAFPCanonicalMinimal period hPeriod data).graph := by
  rw [candidateAFPFormalAdjointMinimal_volume_graph]
  let weight := pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)
  constructor
  · rintro ⟨pair, hPair, hEqual⟩
    change (weight pair.1, weight pair.2) = (input, output) at hEqual
    have hFirst := congrArg weight.symm (congrArg Prod.fst hEqual)
    have hSecond := congrArg weight.symm (congrArg Prod.snd hEqual)
    change weight.symm (weight pair.1) = weight.symm input at hFirst
    change weight.symm (weight pair.2) = weight.symm output at hSecond
    rw [weight.symm_apply_apply] at hFirst hSecond
    change (weight.symm input, weight.symm output) ∈ _
    rw [← hFirst, ← hSecond]
    exact hPair
  · intro hPair
    refine ⟨_, hPair, ?_⟩
    change (weight (weight.symm input), weight (weight.symm output)) = (input, output)
    rw [weight.apply_symm_apply, weight.apply_symm_apply]

theorem candidateAFPFormalAdjointMinimal_volume_domain_iff
    (input : GlobalPairedGaugeLieL2 period hPeriod) :
    input ∈ (candidateAFPFormalAdjointMinimal period hPeriod data).domain ↔
      (pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)).symm input ∈
        (candidateAFPCanonicalMinimal period hPeriod data).domain := by
  let weight := pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)
  constructor
  · intro hInput
    have hGraph := (candidateAFPFormalAdjointMinimal_volume_mem_graph_iff period hPeriod data _ _).mp
      ((candidateAFPFormalAdjointMinimal period hPeriod data).mem_graph ⟨input, hInput⟩)
    obtain ⟨vector, hVector, _⟩ := (candidateAFPCanonicalMinimal period hPeriod data).mem_graph_iff.mp hGraph
    change (vector : GlobalPairedGaugeLieL2 period hPeriod) = weight.symm input at hVector
    rw [← hVector]
    exact vector.property
  · intro hInput
    have hGraph := (candidateAFPFormalAdjointMinimal_volume_mem_graph_iff period hPeriod data input
      (weight (candidateAFPCanonicalMinimal period hPeriod data ⟨weight.symm input, hInput⟩))).mpr
      (by
        change (weight.symm input, weight.symm (weight _)) ∈ _
        rw [weight.symm_apply_apply]
        exact (candidateAFPCanonicalMinimal period hPeriod data).mem_graph ⟨weight.symm input, hInput⟩)
    obtain ⟨vector, hVector, _⟩ := (candidateAFPFormalAdjointMinimal period hPeriod data).mem_graph_iff.mp hGraph
    change (vector : GlobalPairedGaugeLieL2 period hPeriod) = input at hVector
    rw [← hVector]
    exact vector.property

/-- On its full minimal domain, the formal adjoint is r FP_min r⁻¹. -/
theorem candidateAFPFormalAdjointMinimal_volume_apply
    (input : (candidateAFPFormalAdjointMinimal period hPeriod data).domain) :
    candidateAFPFormalAdjointMinimal period hPeriod data input =
      pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (candidateAFPCanonicalMinimal period hPeriod data
          ⟨(pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)).symm input.val,
            (candidateAFPFormalAdjointMinimal_volume_domain_iff period hPeriod data _).mp input.property⟩) := by
  let weight := pairedVolumeL2Equiv period hPeriod (globalCandidateAMetricBySector period hPeriod data)
  have hGraph := (candidateAFPFormalAdjointMinimal_volume_mem_graph_iff period hPeriod data _ _).mp
    ((candidateAFPFormalAdjointMinimal period hPeriod data).mem_graph input)
  obtain ⟨vector, hVector, hValue⟩ := (candidateAFPCanonicalMinimal period hPeriod data).mem_graph_iff.mp hGraph
  apply weight.symm.injective
  rw [weight.symm_apply_apply]
  exact hValue.symm.trans (congrArg (candidateAFPCanonicalMinimal period hPeriod data) (Subtype.ext hVector))

end
end P0EFTJanusProgramPT12CandidateAFPVolumeGraph4D
end JanusFormal
