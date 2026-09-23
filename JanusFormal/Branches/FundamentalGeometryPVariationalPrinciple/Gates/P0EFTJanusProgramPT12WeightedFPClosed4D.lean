import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureAdjoint4D

/-! The closed actual weighted FP column, its genuine smooth core, and dense Hilbert adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedFPClosed4D
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
open P0EFTJanusProgramPT12HessianGhostReduced4D




open P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D

local instance componentInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0).range

open P0EFTJanusProgramPT12WeightedFPSmooth4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
open P0EFTJanusProgramPT12ClosedFeatureAdjoint4D

attribute [local irreducible] diffeomorphismTripletComponentSmooth weightedFPSmooth weightedFPTransposeSmooth linearFeatureGraphClosure

theorem weightedFPGraph_pairing
    (graph : linearFeatureGraphClosure
      (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
      (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0)
      (weightedFPSmooth period hPeriod reference metric couplings))
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    inner Real graph.val.2 (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 test) =
      inner Real graph.val.1 (weightedFPTransposeSmooth period hPeriod reference metric couplings test) :=
by
  have hClosed : IsClosed {pair : DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 ×
      DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 |
      inner Real pair.2 (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 test) =
        inner Real pair.1 (weightedFPTransposeSmooth period hPeriod reference metric couplings test)} := by
    apply isClosed_eq <;> fun_prop
  have hSubset :
      (((diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0).prod
        (weightedFPSmooth period hPeriod reference metric couplings)).range :
        Set (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 ×
          DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)) ⊆
      {pair | inner Real pair.2 (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 test) =
        inner Real pair.1 (weightedFPTransposeSmooth period hPeriod reference metric couplings test)} := by
    rintro pair ⟨field, rfl⟩
    exact weightedFPSmooth_pairing period hPeriod reference metric couplings field test
  have hGraph := graph.property
  unfold linearFeatureGraphClosure at hGraph
  exact (closure_minimal hSubset hClosed) hGraph
theorem weightedFPGraph_single :
    Function.Injective (fun graph : linearFeatureGraphClosure
      (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
      (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0)
      (weightedFPSmooth period hPeriod reference metric couplings) => graph.val.1) := by
  intro first second hInput
  apply Subtype.ext
  apply Prod.ext hInput
  refine @DenseRange.eq_of_inner_left
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) Real _ _
    (componentInnerProductSpace period hPeriod metric) first.val.2 second.val.2
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0)
    (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 0) ?_
  intro test
  exact (weightedFPGraph_pairing period hPeriod reference metric couplings first test).trans
    ((congrArg (fun field => inner Real field
      (weightedFPTransposeSmooth period hPeriod reference metric couplings test)) hInput).trans
      (weightedFPGraph_pairing period hPeriod reference metric couplings second test).symm)
def weightedFPMinimal :
    DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 →ₗ.[Real]
      DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 :=
  closedFeatureOperator (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0)
    (weightedFPSmooth period hPeriod reference metric couplings)

theorem weightedFPMinimal_isClosed : (weightedFPMinimal period hPeriod reference metric couplings).IsClosed :=
  closedFeatureOperator_isClosed (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (weightedFPGraph_single period hPeriod reference metric couplings)

theorem weightedFPMinimal_denseDomain : Dense
    ((weightedFPMinimal period hPeriod reference metric couplings).domain :
      Set (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)) :=
  closedFeatureOperator_dense_domain (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 0)

theorem weightedFPMinimal_hasCore : (weightedFPMinimal period hPeriod reference metric couplings).HasCore
    (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0).range :=
  closedFeatureOperator_hasCore (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (weightedFPGraph_single period hPeriod reference metric couplings)

theorem weightedFPMinimal_smooth_mem
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 field ∈
      (weightedFPMinimal period hPeriod reference metric couplings).domain :=
  closedFeatureOperator_smooth_mem (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ field

theorem weightedFPMinimal_smooth_apply
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    weightedFPMinimal period hPeriod reference metric couplings
      ⟨diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 field,
        weightedFPMinimal_smooth_mem period hPeriod reference metric couplings field⟩ =
      weightedFPSmooth period hPeriod reference metric couplings field :=
  closedFeatureOperator_smooth_apply (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (weightedFPGraph_single period hPeriod reference metric couplings) field

def weightedFPAdjoint :
    DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 →ₗ.[Real]
      DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0 :=
  LinearPMap.adjoint (𝕜 := Real)
    (E := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (F := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (weightedFPMinimal period hPeriod reference metric couplings)

theorem weightedFPAdjoint_smooth_mem
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 field ∈
      (weightedFPAdjoint period hPeriod reference metric couplings).domain :=
  closedFeatureAdjoint_smooth_mem (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (weightedFPGraph_single period hPeriod reference metric couplings)
    (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 0)
    (weightedFPTransposeSmooth period hPeriod reference metric couplings)
    (weightedFPSmooth_pairing period hPeriod reference metric couplings) field

theorem weightedFPAdjoint_smooth_apply
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    weightedFPAdjoint period hPeriod reference metric couplings
      ⟨diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 field,
        weightedFPAdjoint_smooth_mem period hPeriod reference metric couplings field⟩ =
      weightedFPTransposeSmooth period hPeriod reference metric couplings field :=
  closedFeatureAdjoint_smooth_apply (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (weightedFPGraph_single period hPeriod reference metric couplings)
    (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 0)
    (weightedFPTransposeSmooth period hPeriod reference metric couplings)
    (weightedFPSmooth_pairing period hPeriod reference metric couplings) field

theorem weightedFPAdjoint_denseDomain : Dense
    ((weightedFPAdjoint period hPeriod reference metric couplings).domain :
      Set (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)) :=
  closedFeatureAdjoint_dense_domain (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (weightedFPGraph_single period hPeriod reference metric couplings)
    (diffeomorphismTripletComponentSmooth_denseRange period hPeriod (metric .plus) 0)
    (weightedFPTransposeSmooth period hPeriod reference metric couplings)
    (weightedFPSmooth_pairing period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12WeightedFPClosed4D
