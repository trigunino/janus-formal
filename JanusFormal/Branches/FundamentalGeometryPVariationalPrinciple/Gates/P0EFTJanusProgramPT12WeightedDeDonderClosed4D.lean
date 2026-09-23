import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularFeatureAdjoint4D
/-! The closed actual metric-to-B column and its densely defined Hilbert adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderClosed4D
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

open P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

local instance metricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismMetricProjection period hPeriod (metric .plus)).range
local instance auxiliaryInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2).range

open P0EFTJanusProgramPT12WeightedDeDonderSmooth4D
open P0EFTJanusProgramPT12RectangularFeatureClosed4D
open P0EFTJanusProgramPT12RectangularFeatureAdjoint4D

attribute [local irreducible] diffeomorphismMetricSmooth diffeomorphismTripletComponentSmooth
  weightedDeDonderSmooth weightedDeDonderTransposeSmooth rectangularFeatureGraphClosure

theorem weightedDeDonderGraph_pairing
    (graph : rectangularFeatureGraphClosure (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) (diffeomorphismMetricSmooth period hPeriod (metric .plus)) (weightedDeDonderSmooth period hPeriod reference metric couplings))
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real graph.val.2 ((diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) test) = inner Real graph.val.1 ((weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) test) := by
  have hClosed : IsClosed {pair : DiffeomorphismMetricL2 period hPeriod (metric .plus) × DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2 |
      inner Real pair.2 ((diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) test) = inner Real pair.1 ((weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) test)} := by
    apply isClosed_eq <;> fun_prop
  have hSubset : (((diffeomorphismMetricSmooth period hPeriod (metric .plus)).prod (weightedDeDonderSmooth period hPeriod reference metric couplings)).range : Set (DiffeomorphismMetricL2 period hPeriod (metric .plus) × DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2)) ⊆
      {pair | inner Real pair.2 ((diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) test) = inner Real pair.1 ((weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) test)} := by
    rintro pair ⟨field, rfl⟩
    exact weightedDeDonderSmooth_pairing period hPeriod reference metric couplings field test
  have hGraph := graph.property
  unfold rectangularFeatureGraphClosure at hGraph
  exact (closure_minimal hSubset hClosed) hGraph

theorem weightedDeDonderGraph_single :
    Function.Injective (fun graph : rectangularFeatureGraphClosure
      (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) (diffeomorphismMetricSmooth period hPeriod (metric .plus)) (weightedDeDonderSmooth period hPeriod reference metric couplings) => graph.val.1) := by
  intro first second hInput
  apply Subtype.ext
  apply Prod.ext hInput
  refine @DenseRange.eq_of_inner_left (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) (GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) Real _ _
    (auxiliaryInnerProductSpace period hPeriod metric) first.val.2 second.val.2
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 2) ?_
  intro test
  exact (weightedDeDonderGraph_pairing period hPeriod reference metric couplings first test).trans
    ((congrArg (fun field => inner Real field ((weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) test)) hInput).trans
      (weightedDeDonderGraph_pairing period hPeriod reference metric couplings second test).symm)

def weightedDeDonderMinimal : DiffeomorphismMetricL2 period hPeriod (metric .plus) →ₗ.[Real] DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2 :=
  rectangularFeatureOperator (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) (diffeomorphismMetricSmooth period hPeriod (metric .plus)) (weightedDeDonderSmooth period hPeriod reference metric couplings)

theorem weightedDeDonderMinimal_isClosed : (weightedDeDonderMinimal period hPeriod reference metric couplings).IsClosed :=
  rectangularFeatureOperator_isClosed (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ (weightedDeDonderGraph_single period hPeriod reference metric couplings)

theorem weightedDeDonderMinimal_denseDomain :
    Dense ((weightedDeDonderMinimal period hPeriod reference metric couplings).domain : Set (DiffeomorphismMetricL2 period hPeriod (metric .plus))) :=
  rectangularFeatureOperator_dense_domain (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _
    (diffeomorphismMetricSmooth_denseRange period hPeriod (metric .plus))

theorem weightedDeDonderMinimal_hasCore :
    (weightedDeDonderMinimal period hPeriod reference metric couplings).HasCore (diffeomorphismMetricSmooth period hPeriod (metric .plus)).range :=
  rectangularFeatureOperator_hasCore (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ (weightedDeDonderGraph_single period hPeriod reference metric couplings)

theorem weightedDeDonderMinimal_smooth_mem (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismMetricSmooth period hPeriod (metric .plus)) field ∈ (weightedDeDonderMinimal period hPeriod reference metric couplings).domain :=
  rectangularFeatureOperator_smooth_mem (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ field

theorem weightedDeDonderMinimal_smooth_apply (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    weightedDeDonderMinimal period hPeriod reference metric couplings
      ⟨(diffeomorphismMetricSmooth period hPeriod (metric .plus)) field, weightedDeDonderMinimal_smooth_mem period hPeriod reference metric couplings field⟩ = (weightedDeDonderSmooth period hPeriod reference metric couplings) field :=
  rectangularFeatureOperator_smooth_apply (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ (weightedDeDonderGraph_single period hPeriod reference metric couplings) field

def weightedDeDonderAdjoint : DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2 →ₗ.[Real] DiffeomorphismMetricL2 period hPeriod (metric .plus) :=
  LinearPMap.adjoint (𝕜 := Real) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) (weightedDeDonderMinimal period hPeriod reference metric couplings)

theorem weightedDeDonderAdjoint_smooth_mem (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) field ∈ (weightedDeDonderAdjoint period hPeriod reference metric couplings).domain :=
  rectangularFeatureAdjoint_smooth_mem (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ (weightedDeDonderGraph_single period hPeriod reference metric couplings)
    (diffeomorphismMetricSmooth_denseRange period hPeriod (metric .plus))
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) (weightedDeDonderSmooth_pairing period hPeriod reference metric couplings) field

theorem weightedDeDonderAdjoint_smooth_apply (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    weightedDeDonderAdjoint period hPeriod reference metric couplings
      ⟨(diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) field, weightedDeDonderAdjoint_smooth_mem period hPeriod reference metric couplings field⟩ = (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) field :=
  rectangularFeatureAdjoint_smooth_apply (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ (weightedDeDonderGraph_single period hPeriod reference metric couplings)
    (diffeomorphismMetricSmooth_denseRange period hPeriod (metric .plus))
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) (weightedDeDonderSmooth_pairing period hPeriod reference metric couplings) field

theorem weightedDeDonderAdjoint_denseDomain :
    Dense ((weightedDeDonderAdjoint period hPeriod reference metric couplings).domain : Set (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2)) :=
  rectangularFeatureAdjoint_dense_domain (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismMetricL2 period hPeriod (metric .plus)) (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) _ _ (weightedDeDonderGraph_single period hPeriod reference metric couplings)
    (diffeomorphismMetricSmooth_denseRange period hPeriod (metric .plus))
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 2) (weightedDeDonderTransposeSmooth period hPeriod reference metric couplings) (weightedDeDonderSmooth_pairing period hPeriod reference metric couplings)
    (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 2)

end
end JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderClosed4D

