import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedGraphSeries4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTemporalFourierMatrix4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

/-! Infinite temporal Fourier packets in the minimal actual abelian BRST graph. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTemporalFourierSeries4D
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
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

open P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

variable [hPeriodPos : Fact (0 < period)]

open P0EFTJanusProgramPT12AbelianTemporalFourierCore4D
open P0EFTJanusProgramPT12AbelianTemporalFourierMatrix4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
open P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
open P0EFTJanusProgramPT12ClosedGraphSeries4D

def temporalGhostOutput (antighost ghost : PairedTemporalCoefficients) : CandidateAAbelianGhostL2 period hPeriod :=
  WithLp.toLp 2
    (temporalFP period hPeriod data ghost,
      pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pairedTemporalGhost period hPeriod antighost))

/-- Each packet belongs to the minimal smooth graph closure, not just its self-adjoint extension. -/
theorem temporalGhostInput_minimal_graph (antighost ghost : PairedTemporalCoefficients) :
    (temporalGhostInput period hPeriod antighost ghost, temporalGhostOutput period hPeriod data antighost ghost) ∈
      (candidateAAbelianGhostMinimal period hPeriod data).graph := by
  apply (offDiagonalOperator_mem_graph_iff _ _ _ _).mpr
  constructor
  · exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨_, candidateAFPCanonicalMinimal_smooth_mem period hPeriod data (pairedTemporalGhost period hPeriod ghost)⟩,
        rfl, candidateAFPCanonicalMinimal_smooth_apply period hPeriod data _⟩
  · exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨_, candidateAFPFormalAdjointMinimal_smooth_mem period hPeriod data (pairedTemporalGhost period hPeriod antighost)⟩,
        rfl, candidateAFPFormalAdjointMinimal_smooth_apply period hPeriod data _⟩

variable {ι : Type*}
variable (antighost ghost : ι → PairedTemporalCoefficients) (coefficients : ι → Real)

/-- Simultaneous synthesis of the field and its actual FP/FP† image. -/
def temporalGhostGraphSeries : CandidateAAbelianGhostL2 period hPeriod × CandidateAAbelianGhostL2 period hPeriod :=
  graphSeries (fun i => temporalGhostInput period hPeriod (antighost i) (ghost i))
    (fun i => temporalGhostOutput period hPeriod data (antighost i) (ghost i)) coefficients

theorem temporalGhostGraphSeries_hasSum
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    HasSum (fun i => coefficients i • normalizedGraphMode
      (fun j => temporalGhostInput period hPeriod (antighost j) (ghost j))
      (fun j => temporalGhostOutput period hPeriod data (antighost j) (ghost j)) i)
      (temporalGhostGraphSeries period hPeriod data antighost ghost coefficients) :=
  graphSeries_hasSum _ _ coefficients hCoefficients

theorem temporalGhostGraphSeries_minimal_graph
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    temporalGhostGraphSeries period hPeriod data antighost ghost coefficients ∈
      (candidateAAbelianGhostMinimal period hPeriod data).graph :=
  graphSeries_mem_graph _ (candidateAAbelianGhostMinimal_isClosed period hPeriod data) _ _
    (fun i => temporalGhostInput_minimal_graph period hPeriod data (antighost i) (ghost i))
    coefficients hCoefficients

theorem temporalGhostGraphSeries_actual_graph
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    temporalGhostGraphSeries period hPeriod data antighost ghost coefficients ∈
      (candidateAAbelianGhostOperator period hPeriod data).graph :=
  LinearPMap.le_graph_of_le (candidateAAbelianGhostMinimal_le_selfAdjoint period hPeriod data)
    (temporalGhostGraphSeries_minimal_graph period hPeriod data antighost ghost coefficients hCoefficients)

theorem temporalGhostGraphSeries_mem_domain
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    (temporalGhostGraphSeries period hPeriod data antighost ghost coefficients).1 ∈
      (candidateAAbelianGhostMinimal period hPeriod data).domain :=
  graphSeries_mem_domain _ (candidateAAbelianGhostMinimal_isClosed period hPeriod data) _ _
    (fun i => temporalGhostInput_minimal_graph period hPeriod data (antighost i) (ghost i))
    coefficients hCoefficients

theorem temporalGhostGraphSeries_apply
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    candidateAAbelianGhostMinimal period hPeriod data
      ⟨(temporalGhostGraphSeries period hPeriod data antighost ghost coefficients).1,
        temporalGhostGraphSeries_mem_domain period hPeriod data antighost ghost coefficients hCoefficients⟩ =
      (temporalGhostGraphSeries period hPeriod data antighost ghost coefficients).2 :=
  graphSeries_apply _ (candidateAAbelianGhostMinimal_isClosed period hPeriod data) _ _
    (fun i => temporalGhostInput_minimal_graph period hPeriod data (antighost i) (ghost i))
    coefficients hCoefficients

theorem temporalGhostGraphSeries_norm_le
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    ‖temporalGhostGraphSeries period hPeriod data antighost ghost coefficients‖ ≤ ∑' i, ‖coefficients i‖ :=
  graphSeries_norm_le _ _ coefficients hCoefficients

/-- Each coefficient uses the same actual FP pairing as the finite reconstruction. -/
theorem temporalGhostOutput_pairing (anti gh testAnti testGhost : PairedTemporalCoefficients) :
    inner Real (temporalGhostOutput period hPeriod data anti gh)
      (temporalGhostInput period hPeriod testAnti testGhost) =
    inner Real (temporalFP period hPeriod data gh) (pairedTemporalGhostL2 period hPeriod testAnti) +
      inner Real (temporalFP period hPeriod data testGhost) (pairedTemporalGhostL2 period hPeriod anti) := by
  have hApply : candidateAAbelianGhostOperator period hPeriod data
      ⟨temporalGhostInput period hPeriod anti gh, temporalGhostInput_mem_domain period hPeriod data anti gh⟩ =
      temporalGhostOutput period hPeriod data anti gh :=
    candidateAAbelianGhostOperator_smooth_apply period hPeriod data _ _
  rw [← hApply]
  exact temporalGhostInput_pairing period hPeriod data anti gh testAnti testGhost

/-- Pairings of the infinite actual image converge to the series of finite FP pairings. -/
theorem temporalGhostGraphSeries_pairing_hasSum
    (hCoefficients : Summable (fun i => ‖coefficients i‖))
    (testAnti testGhost : PairedTemporalCoefficients) :
    HasSum (fun i => coefficients i /
      graphModeWeight (fun j => temporalGhostInput period hPeriod (antighost j) (ghost j))
        (fun j => temporalGhostOutput period hPeriod data (antighost j) (ghost j)) i *
      (inner Real (temporalFP period hPeriod data (ghost i)) (pairedTemporalGhostL2 period hPeriod testAnti) +
        inner Real (temporalFP period hPeriod data testGhost) (pairedTemporalGhostL2 period hPeriod (antighost i))))
      (inner Real (temporalGhostGraphSeries period hPeriod data antighost ghost coefficients).2
        (temporalGhostInput period hPeriod testAnti testGhost)) := by
  have h := (temporalGhostGraphSeries_hasSum period hPeriod data antighost ghost coefficients hCoefficients).mapL
    ((innerSL Real (temporalGhostInput period hPeriod testAnti testGhost)).comp
      (ContinuousLinearMap.snd Real (CandidateAAbelianGhostL2 period hPeriod) (CandidateAAbelianGhostL2 period hPeriod)))
  convert h using 1 <;> try rfl
  · funext i
    change _ = inner Real (temporalGhostInput period hPeriod testAnti testGhost)
      (coefficients i • (graphModeWeight
        (fun j => temporalGhostInput period hPeriod (antighost j) (ghost j))
        (fun j => temporalGhostOutput period hPeriod data (antighost j) (ghost j)) i)⁻¹ •
        temporalGhostOutput period hPeriod data (antighost i) (ghost i))
    rw [real_inner_smul_right, real_inner_smul_right,
      real_inner_comm (temporalGhostOutput period hPeriod data (antighost i) (ghost i))
        (temporalGhostInput period hPeriod testAnti testGhost),
      temporalGhostOutput_pairing, div_eq_mul_inv, mul_assoc]
  · exact real_inner_comm _ _
end
end P0EFTJanusProgramPT12AbelianTemporalFourierSeries4D
end JanusFormal
