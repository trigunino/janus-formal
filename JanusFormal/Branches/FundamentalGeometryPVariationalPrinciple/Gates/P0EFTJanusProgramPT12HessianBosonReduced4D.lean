import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostMinimal4D

/-! A closed densely defined actual Hessian on the genuine metric–B Hilbert subspace. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianBosonReduced4D
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

open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D

def hessianBosonSmooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod :=
  field - hessianGhostSmooth period hPeriod field

theorem hessianBosonSmooth_L2 (normalization : SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismBosonProjection period hPeriod normalization
      (diffeomorphismL2Smooth period hPeriod normalization field) =
      diffeomorphismL2Smooth period hPeriod normalization (hessianBosonSmooth period hPeriod field) := by
  change diffeomorphismL2Smooth period hPeriod normalization field -
    diffeomorphismGhostProjection period hPeriod normalization
      (diffeomorphismL2Smooth period hPeriod normalization field) =
    diffeomorphismL2Smooth period hPeriod normalization (field - hessianGhostSmooth period hPeriod field)
  rw [map_sub, hessianGhostSmooth_L2]

theorem hessianSmoothRiesz_boson_commutes
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianSmoothRiesz period hPeriod reference metric couplings (hessianBosonSmooth period hPeriod field) =
      diffeomorphismBosonProjection period hPeriod (metric .plus)
        (hessianSmoothRiesz period hPeriod reference metric couplings field) := by
  change (hessianSmoothRieszLinearMap period hPeriod reference metric couplings)
    (field - hessianGhostSmooth period hPeriod field) = _
  rw [map_sub]
  change hessianSmoothRiesz period hPeriod reference metric couplings field -
    hessianSmoothRiesz period hPeriod reference metric couplings (hessianGhostSmooth period hPeriod field) =
    hessianSmoothRiesz period hPeriod reference metric couplings field -
      diffeomorphismGhostProjection period hPeriod (metric .plus)
        (hessianSmoothRiesz period hPeriod reference metric couplings field)
  rw [hessianSmoothRiesz_ghost_commutes]
local instance bosonPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)).range
def hessianBosonReducedGraph : Submodule Real
    (DiffeomorphismBosonPairL2 period hPeriod (metric .plus) × DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  (hessianL2Minimal period hPeriod reference metric couplings).graph.comap
    ((diffeomorphismBosonProjection period hPeriod (metric .plus)).range.subtype.prodMap
      (diffeomorphismBosonProjection period hPeriod (metric .plus)).range.subtype)

def hessianBosonReduced : DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  (hessianBosonReducedGraph period hPeriod reference metric couplings).toLinearPMap

theorem hessianBosonReduced_graph : (hessianBosonReduced period hPeriod reference metric couplings).graph =
    hessianBosonReducedGraph period hPeriod reference metric couplings := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  change (pair.1.val, pair.2.val) ∈ (hessianL2Minimal period hPeriod reference metric couplings).graph at hPair
  apply Subtype.ext
  exact (hessianL2Minimal period hPeriod reference metric couplings).graph_fst_eq_zero_snd hPair
    (congrArg Subtype.val hZero)

theorem hessianBosonReduced_graph_iff
    (input output : DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :
    (input, output) ∈ (hessianBosonReduced period hPeriod reference metric couplings).graph ↔
      (input.val, output.val) ∈ (hessianL2Minimal period hPeriod reference metric couplings).graph := by
  rw [hessianBosonReduced_graph]
  rfl

theorem hessianBosonReduced_isClosed : (hessianBosonReduced period hPeriod reference metric couplings).IsClosed := by
  change IsClosed ((hessianBosonReduced period hPeriod reference metric couplings).graph :
    Set (DiffeomorphismBosonPairL2 period hPeriod (metric .plus) × DiffeomorphismBosonPairL2 period hPeriod (metric .plus)))
  rw [hessianBosonReduced_graph]
  exact (hessianL2Minimal_isClosed period hPeriod reference metric couplings).preimage
    (show Continuous (fun pair : DiffeomorphismBosonPairL2 period hPeriod (metric .plus) ×
      DiffeomorphismBosonPairL2 period hPeriod (metric .plus) => (pair.1.val, pair.2.val)) by fun_prop)

def hessianBosonReducedSmoothOutput (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  ⟨diffeomorphismBosonProjection period hPeriod (metric .plus) (hessianSmoothRiesz period hPeriod reference metric couplings field),
    ⟨hessianSmoothRiesz period hPeriod reference metric couplings field, rfl⟩⟩

theorem hessianBosonReduced_smooth_graph (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field,
      hessianBosonReducedSmoothOutput period hPeriod reference metric couplings field) ∈
        (hessianBosonReduced period hPeriod reference metric couplings).graph := by
  rw [hessianBosonReduced_graph_iff]
  have h := hessianL2Minimal_graph_boson period hPeriod reference metric couplings _
    ((hessianL2Minimal period hPeriod reference metric couplings).mem_graph
      (hessianL2SmoothDomain period hPeriod reference metric couplings field))
  rw [hessianL2Minimal_smooth] at h
  exact h

theorem hessianBosonReduced_denseDomain : Dense
    ((hessianBosonReduced period hPeriod reference metric couplings).domain :
      Set (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))) := by
  apply (diffeomorphismBosonPairSmooth_denseRange period hPeriod (metric .plus)).mono
  rintro _ ⟨field, rfl⟩
  obtain ⟨input, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (hessianBosonReduced_smooth_graph period hPeriod reference metric couplings field)
  change input.val = diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field at hInput
  rw [← hInput]
  exact input.property

theorem hessianBosonReduced_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real)
      (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
      (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
      (hessianBosonReduced period hPeriod reference metric couplings)
      (hessianBosonReduced period hPeriod reference metric couplings) := by
  intro first second
  obtain ⟨x, hX, hTX⟩ := (LinearPMap.mem_graph_iff _).mp
    ((hessianBosonReduced_graph_iff period hPeriod reference metric couplings _ _).mp
      ((hessianBosonReduced period hPeriod reference metric couplings).mem_graph first))
  obtain ⟨y, hY, hTY⟩ := (LinearPMap.mem_graph_iff _).mp
    ((hessianBosonReduced_graph_iff period hPeriod reference metric couplings _ _).mp
      ((hessianBosonReduced period hPeriod reference metric couplings).mem_graph second))
  dsimp only at hX hTX hY hTY
  change inner Real (hessianBosonReduced period hPeriod reference metric couplings first).val second.val.val =
    inner Real first.val.val (hessianBosonReduced period hPeriod reference metric couplings second).val
  rw [← hX, ← hTX, ← hY, ← hTY]
  exact hessianL2Minimal_isFormalAdjoint period hPeriod reference metric couplings x y

theorem hessianBosonReduced_smooth_actual_pairing
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real (hessianBosonReducedSmoothOutput period hPeriod reference metric couplings first)
      (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) second) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTPolarizationAction period hPeriod couplings metric
        (hessianBosonSmooth period hPeriod first) (hessianBosonSmooth period hPeriod second) := by
  change inner Real
    (diffeomorphismBosonProjection period hPeriod (metric .plus) (hessianSmoothRiesz period hPeriod reference metric couplings first))
    (diffeomorphismBosonProjection period hPeriod (metric .plus) (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) = _
  rw [← hessianSmoothRiesz_boson_commutes, hessianBosonSmooth_L2]
  exact hessianSmoothRiesz_actual_pairing period hPeriod reference metric couplings
    (hessianBosonSmooth period hPeriod first) (hessianBosonSmooth period hPeriod second)
end
end JanusFormal.P0EFTJanusProgramPT12HessianBosonReduced4D