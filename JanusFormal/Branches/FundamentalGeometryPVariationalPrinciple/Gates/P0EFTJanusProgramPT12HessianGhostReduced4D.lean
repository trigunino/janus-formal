import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMinimal4D

/-! A closed densely defined actual Hessian on the genuine ghost-pair Hilbert subspace. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianGhostReduced4D
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
open P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D

local instance ghostPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismGhostProjection period hPeriod (metric .plus)).range
def hessianGhostReducedGraph : Submodule Real
    (DiffeomorphismGhostPairL2 period hPeriod (metric .plus) × DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  (hessianL2Minimal period hPeriod reference metric couplings).graph.comap
    ((diffeomorphismGhostProjection period hPeriod (metric .plus)).range.subtype.prodMap
      (diffeomorphismGhostProjection period hPeriod (metric .plus)).range.subtype)

def hessianGhostReduced : DiffeomorphismGhostPairL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismGhostPairL2 period hPeriod (metric .plus) :=
  (hessianGhostReducedGraph period hPeriod reference metric couplings).toLinearPMap

theorem hessianGhostReduced_graph : (hessianGhostReduced period hPeriod reference metric couplings).graph =
    hessianGhostReducedGraph period hPeriod reference metric couplings := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  change (pair.1.val, pair.2.val) ∈ (hessianL2Minimal period hPeriod reference metric couplings).graph at hPair
  apply Subtype.ext
  exact (hessianL2Minimal period hPeriod reference metric couplings).graph_fst_eq_zero_snd hPair
    (congrArg Subtype.val hZero)

theorem hessianGhostReduced_graph_iff
    (input output : DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianGhostReduced period hPeriod reference metric couplings).graph ↔
      (input.val, output.val) ∈ (hessianL2Minimal period hPeriod reference metric couplings).graph := by
  rw [hessianGhostReduced_graph]
  rfl

theorem hessianGhostReduced_isClosed : (hessianGhostReduced period hPeriod reference metric couplings).IsClosed := by
  change IsClosed ((hessianGhostReduced period hPeriod reference metric couplings).graph :
    Set (DiffeomorphismGhostPairL2 period hPeriod (metric .plus) × DiffeomorphismGhostPairL2 period hPeriod (metric .plus)))
  rw [hessianGhostReduced_graph]
  exact (hessianL2Minimal_isClosed period hPeriod reference metric couplings).preimage
    (show Continuous (fun pair : DiffeomorphismGhostPairL2 period hPeriod (metric .plus) ×
      DiffeomorphismGhostPairL2 period hPeriod (metric .plus) => (pair.1.val, pair.2.val)) by fun_prop)

def hessianGhostReducedSmoothOutput (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    DiffeomorphismGhostPairL2 period hPeriod (metric .plus) :=
  ⟨diffeomorphismGhostProjection period hPeriod (metric .plus) (hessianSmoothRiesz period hPeriod reference metric couplings field),
    ⟨hessianSmoothRiesz period hPeriod reference metric couplings field, rfl⟩⟩

theorem hessianGhostReduced_smooth_graph (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismGhostPairSmooth period hPeriod (metric .plus) field,
      hessianGhostReducedSmoothOutput period hPeriod reference metric couplings field) ∈
        (hessianGhostReduced period hPeriod reference metric couplings).graph := by
  rw [hessianGhostReduced_graph_iff]
  have h := hessianL2Minimal_graph_ghost period hPeriod reference metric couplings _
    ((hessianL2Minimal period hPeriod reference metric couplings).mem_graph
      (hessianL2SmoothDomain period hPeriod reference metric couplings field))
  rw [hessianL2Minimal_smooth] at h
  exact h

theorem hessianGhostReduced_denseDomain : Dense
    ((hessianGhostReduced period hPeriod reference metric couplings).domain :
      Set (DiffeomorphismGhostPairL2 period hPeriod (metric .plus))) := by
  apply (diffeomorphismGhostPairSmooth_denseRange period hPeriod (metric .plus)).mono
  rintro _ ⟨field, rfl⟩
  obtain ⟨input, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (hessianGhostReduced_smooth_graph period hPeriod reference metric couplings field)
  change input.val = diffeomorphismGhostPairSmooth period hPeriod (metric .plus) field at hInput
  rw [← hInput]
  exact input.property

theorem hessianGhostReduced_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real)
      (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
      (F := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
      (hessianGhostReduced period hPeriod reference metric couplings)
      (hessianGhostReduced period hPeriod reference metric couplings) := by
  intro first second
  obtain ⟨x, hX, hTX⟩ := (LinearPMap.mem_graph_iff _).mp
    ((hessianGhostReduced_graph_iff period hPeriod reference metric couplings _ _).mp
      ((hessianGhostReduced period hPeriod reference metric couplings).mem_graph first))
  obtain ⟨y, hY, hTY⟩ := (LinearPMap.mem_graph_iff _).mp
    ((hessianGhostReduced_graph_iff period hPeriod reference metric couplings _ _).mp
      ((hessianGhostReduced period hPeriod reference metric couplings).mem_graph second))
  dsimp only at hX hTX hY hTY
  change inner Real (hessianGhostReduced period hPeriod reference metric couplings first).val second.val.val =
    inner Real first.val.val (hessianGhostReduced period hPeriod reference metric couplings second).val
  rw [← hX, ← hTX, ← hY, ← hTY]
  exact hessianL2Minimal_isFormalAdjoint period hPeriod reference metric couplings x y

theorem hessianGhostReduced_smooth_actual_pairing
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (hessianGhostReducedSmoothOutput period hPeriod reference metric couplings first)
      (diffeomorphismGhostPairSmooth period hPeriod (metric .plus) second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings metric
        (hessianGhostSmooth period hPeriod first) (hessianGhostSmooth period hPeriod second) := by
  change inner Real
    (diffeomorphismGhostProjection period hPeriod (metric .plus) (hessianSmoothRiesz period hPeriod reference metric couplings first))
    (diffeomorphismGhostProjection period hPeriod (metric .plus) (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) = _
  rw [← hessianSmoothRiesz_ghost_commutes, hessianGhostSmooth_L2]
  exact hessianSmoothRiesz_actual_pairing period hPeriod reference metric couplings
    (hessianGhostSmooth period hPeriod first) (hessianGhostSmooth period hPeriod second)
end
end JanusFormal.P0EFTJanusProgramPT12HessianGhostReduced4D