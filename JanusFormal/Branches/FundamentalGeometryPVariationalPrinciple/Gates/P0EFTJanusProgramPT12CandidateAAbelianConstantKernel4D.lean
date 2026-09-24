import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeGlobalH04D

/-! Constant gauge ghosts inside the actual closed FP and BRST kernels. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianConstantKernel4D
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

open P0EFTJanusMappingTorusAbelianGaugeGlobalH04D
open P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D

def pairedConstantGhost : (Sector → GaugeLieAlgebra) →ₗ[Real]
    GlobalPairedGaugeLieSmooth period hPeriod where
  toFun value sector := constantGhost period hPeriod (value sector)
  map_add' _ _ := by
    funext sector
    apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    rfl
  map_smul' _ _ := by
    funext sector
    apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    rfl

theorem pairedConstantGhost_injective : Function.Injective (pairedConstantGhost period hPeriod) := by
  intro first second h
  funext sector
  exact congrArg (fun field : GlobalPairedGaugeLieSmooth period hPeriod =>
    field sector (Classical.choice (effectiveQuotient_nonempty period hPeriod))) h

def pairedConstantGhostL2 : (Sector → GaugeLieAlgebra) →ₗ[Real]
    GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedGaugeLieL2LinearMap period hPeriod).comp (pairedConstantGhost period hPeriod)

theorem pairedConstantGhostL2_injective : Function.Injective (pairedConstantGhostL2 period hPeriod) :=
  (globalPairedGaugeLieL2LinearMap_injective period hPeriod).comp
    (pairedConstantGhost_injective period hPeriod)

/-- Constants are killed by delta_g d for every supplied metric, without an ellipticity assumption. -/
theorem pairedConstantGhost_FP_zero
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) (value : Sector → GaugeLieAlgebra) :
    globalPairedAbelianFPL2LinearMap period hPeriod metric (pairedConstantGhost period hPeriod value) = 0 := by
  change globalPairedGaugeLieL2LinearMap period hPeriod
    (fun sector => globalGeneralMetricAbelianFaddeevPopov period hPeriod
      (metric sector) (constantGhost period hPeriod (value sector))) = 0
  have h : (fun sector => globalGeneralMetricAbelianFaddeevPopov period hPeriod
      (metric sector) (constantGhost period hPeriod (value sector))) = 0 := by
    funext sector
    unfold globalGeneralMetricAbelianFaddeevPopov
    rw [exactGaugePotential_constantGhost]
    exact (globalGeneralMetricAbelianLorenzCodifferentialLinearMap period hPeriod (metric sector)).map_zero
  rw [h, map_zero]

theorem pairedConstantGhost_minimal_graph (value : Sector → GaugeLieAlgebra) :
    (pairedConstantGhostL2 period hPeriod value, 0) ∈ (candidateAFPCanonicalMinimal period hPeriod data).graph := by
  have h := (candidateAFPCanonicalMinimal period hPeriod data).mem_graph
    ⟨_, candidateAFPCanonicalMinimal_smooth_mem period hPeriod data (pairedConstantGhost period hPeriod value)⟩
  rw [candidateAFPCanonicalMinimal_smooth_apply, pairedConstantGhost_FP_zero] at h
  exact h

def constantGhostBRST : (Sector → GaugeLieAlgebra) →ₗ[Real] CandidateAAbelianGhostL2 period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.toLinearMap.comp
    ((0 : (Sector → GaugeLieAlgebra) →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod).prod
      (pairedConstantGhostL2 period hPeriod))

theorem constantGhostBRST_injective : Function.Injective (constantGhostBRST period hPeriod) := by
  intro first second h
  exact pairedConstantGhostL2_injective period hPeriod (congrArg WithLp.snd h)

theorem constantGhostBRST_graph (value : Sector → GaugeLieAlgebra) :
    (constantGhostBRST period hPeriod value, 0) ∈ (candidateAAbelianGhostOperator period hPeriod data).graph :=
  (offDiagonalOperator_mem_graph_iff _ _ _ _).mpr
    ⟨pairedConstantGhost_minimal_graph period hPeriod data value,
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.graph.zero_mem⟩

def constantGhostBRSTKernel : (Sector → GaugeLieAlgebra) →ₗ[Real]
    LinearMap.ker (candidateAAbelianGhostOperator period hPeriod data).toFun where
  toFun value := ⟨⟨constantGhostBRST period hPeriod value,
    LinearPMap.mem_domain_of_mem_graph (constantGhostBRST_graph period hPeriod data value)⟩, by
      exact (candidateAAbelianGhostOperator period hPeriod data).mem_graph_snd_inj
        ((candidateAAbelianGhostOperator period hPeriod data).mem_graph _) (constantGhostBRST_graph period hPeriod data value) rfl⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

theorem constantGhostBRSTKernel_injective : Function.Injective (constantGhostBRSTKernel period hPeriod data) := by
  intro first second h
  apply constantGhostBRST_injective period hPeriod
  exact congrArg (fun state : LinearMap.ker (candidateAAbelianGhostOperator period hPeriod data).toFun => state.val.val) h

/-- This identifies a four-dimensional subspace, not the entire FP or BRST kernel. -/
theorem constantGhostBRSTKernel_range_finrank :
    Module.finrank Real (constantGhostBRSTKernel period hPeriod data).range = 4 := by
  rw [LinearMap.finrank_range_of_inj (constantGhostBRSTKernel_injective period hPeriod data)]
  have hCard : Fintype.card Sector = 2 := by decide
  simp [Module.finrank_pi_fintype, GaugeLieAlgebra,
    P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.GhostFiber, hCard]

open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-- The canonical antighost zero modes carry the actual metric volume density. -/
def pairedWeightedConstantAntighost
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    (Sector → GaugeLieAlgebra) →ₗ[Real] GlobalPairedGaugeLieSmooth period hPeriod where
  toFun value sector := smoothGaugeWeight period hPeriod
    (globalSmoothMetricVolumeRatio period hPeriod (metric sector))
    (pairedConstantGhost period hPeriod value sector)
  map_add' _ _ := by funext sector; simp only [map_add, Pi.add_apply]
  map_smul' _ _ := by funext sector; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem pairedWeightedConstantAntighost_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective (pairedWeightedConstantAntighost period hPeriod metric) := by
  intro first second h
  apply pairedConstantGhost_injective period hPeriod
  funext sector
  exact smoothGaugeWeight_metric_injective period hPeriod (metric sector)
    (congrArg (fun field => field sector) h)

theorem pairedWeightedConstantAntighost_adjoint_zero
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) (value : Sector → GaugeLieAlgebra) :
    pairedFPCanonicalAdjointL2 period hPeriod metric
      (pairedWeightedConstantAntighost period hPeriod metric value) = 0 := by
  have hSmooth : pairedFPCanonicalAdjointSmooth period hPeriod metric
      (pairedWeightedConstantAntighost period hPeriod metric value) = 0 := by
    funext sector
    apply (canonicalFPFormalAdjoint_weight_eq_zero_iff period hPeriod (metric sector) _).mpr
    change globalGeneralMetricAbelianLorenzCodifferentialLinearMap period hPeriod (metric sector)
      (exactGaugePotential period hPeriod (constantGhost period hPeriod (value sector))) = 0
    rw [exactGaugePotential_constantGhost, map_zero]
  change globalPairedGaugeLieL2LinearMap period hPeriod
    (pairedFPCanonicalAdjointSmooth period hPeriod metric _) = 0
  rw [hSmooth, map_zero]

def pairedWeightedConstantAntighostL2
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    (Sector → GaugeLieAlgebra) →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedGaugeLieL2LinearMap period hPeriod).comp
    (pairedWeightedConstantAntighost period hPeriod metric)

theorem pairedWeightedConstantAntighostL2_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective (pairedWeightedConstantAntighostL2 period hPeriod metric) :=
  (globalPairedGaugeLieL2LinearMap_injective period hPeriod).comp
    (pairedWeightedConstantAntighost_injective period hPeriod metric)

theorem pairedWeightedConstantAntighost_adjoint_graph (value : Sector → GaugeLieAlgebra) :
    (pairedWeightedConstantAntighostL2 period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) value, 0) ∈
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.graph := by
  have h := (candidateAFPCanonicalMinimal period hPeriod data).adjoint.mem_graph
    ⟨_, candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data
      (pairedWeightedConstantAntighost period hPeriod (globalCandidateAMetricBySector period hPeriod data) value)⟩
  rw [candidateAFPCanonicalAdjoint_smooth_apply, pairedWeightedConstantAntighost_adjoint_zero] at h
  exact h

def constantPairBRST : ((Sector → GaugeLieAlgebra) × (Sector → GaugeLieAlgebra)) →ₗ[Real]
    CandidateAAbelianGhostL2 period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.toLinearMap.comp
    ((pairedWeightedConstantAntighostL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)).prodMap
      (pairedConstantGhostL2 period hPeriod))

theorem constantPairBRST_injective : Function.Injective (constantPairBRST period hPeriod data) := by
  intro first second h
  exact Prod.ext
    (pairedWeightedConstantAntighostL2_injective period hPeriod _ (congrArg WithLp.fst h))
    (pairedConstantGhostL2_injective period hPeriod (congrArg WithLp.snd h))

theorem constantPairBRST_graph (value : (Sector → GaugeLieAlgebra) × (Sector → GaugeLieAlgebra)) :
    (constantPairBRST period hPeriod data value, 0) ∈
      (candidateAAbelianGhostOperator period hPeriod data).graph :=
  (offDiagonalOperator_mem_graph_iff _ _ _ _).mpr
    ⟨pairedConstantGhost_minimal_graph period hPeriod data value.2,
      pairedWeightedConstantAntighost_adjoint_graph period hPeriod data value.1⟩

def constantPairBRSTKernel : ((Sector → GaugeLieAlgebra) × (Sector → GaugeLieAlgebra)) →ₗ[Real]
    LinearMap.ker (candidateAAbelianGhostOperator period hPeriod data).toFun where
  toFun value := ⟨⟨constantPairBRST period hPeriod data value,
    LinearPMap.mem_domain_of_mem_graph (constantPairBRST_graph period hPeriod data value)⟩,
      (candidateAAbelianGhostOperator period hPeriod data).mem_graph_snd_inj
        ((candidateAAbelianGhostOperator period hPeriod data).mem_graph _)
        (constantPairBRST_graph period hPeriod data value) rfl⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

theorem constantPairBRSTKernel_injective : Function.Injective (constantPairBRSTKernel period hPeriod data) := by
  intro first second h
  exact constantPairBRST_injective period hPeriod data (congrArg (fun state => state.val.val) h)

/-- Eight independent actual zero modes; no claim that these exhaust the kernel. -/
theorem constantPairBRSTKernel_range_finrank :
    Module.finrank Real (constantPairBRSTKernel period hPeriod data).range = 8 := by
  rw [LinearMap.finrank_range_of_inj (constantPairBRSTKernel_injective period hPeriod data)]
  have hCard : Fintype.card Sector = 2 := by decide
  simp [Module.finrank_prod, Module.finrank_pi_fintype, GaugeLieAlgebra,
    P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.GhostFiber, hCard]

end
end P0EFTJanusProgramPT12CandidateAAbelianConstantKernel4D
end JanusFormal
