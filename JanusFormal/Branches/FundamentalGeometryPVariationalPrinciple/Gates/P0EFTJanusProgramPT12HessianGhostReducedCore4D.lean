import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostReduced4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

/-! The projected smooth fields form an operator core of the actual ghost Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianGhostReducedCore4D
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
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D

def hessianGhostReducedSmoothLinearMap :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      DiffeomorphismGhostPairL2 period hPeriod (metric .plus) :=
  (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict.toLinearMap.comp
    (hessianSmoothRieszLinearMap period hPeriod reference metric couplings)

theorem hessianGhostReduced_graph_closure :
    (hessianGhostReduced period hPeriod reference metric couplings).graph =
      linearFeatureGraphClosure (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
        (diffeomorphismGhostPairSmooth period hPeriod (metric .plus))
        (hessianGhostReducedSmoothLinearMap period hPeriod reference metric couplings) := by
  apply le_antisymm
  · intro pair hPair
    have hFull := (hessianGhostReduced_graph_iff period hPeriod reference metric couplings _ _).mp hPair
    rw [hessianL2Minimal_graph] at hFull
    let project := fun pair : DiffeomorphismL2 period hPeriod (metric .plus) ×
        DiffeomorphismL2 period hPeriod (metric .plus) =>
      ((diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict pair.1,
       (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict pair.2)
    have hMap : Set.MapsTo project
        ((hessianL2OperatorCore period hPeriod reference metric couplings).graph : Set _)
        (((diffeomorphismGhostPairSmooth period hPeriod (metric .plus)).prod
          (hessianGhostReducedSmoothLinearMap period hPeriod reference metric couplings)).range : Set _) := by
      intro value hValue
      obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
      obtain ⟨smooth, hSmooth⟩ := field.property
      have hField : field =
          ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) smooth, ⟨smooth, rfl⟩⟩ :=
        Subtype.ext hSmooth.symm
      rw [hField, hessianL2OperatorCore_smooth] at hOutput
      refine ⟨smooth, ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · exact congrArg (diffeomorphismGhostProjection period hPeriod (metric .plus))
          (hSmooth.trans hInput)
      · exact congrArg (diffeomorphismGhostProjection period hPeriod (metric .plus)) hOutput
    have hProjected := hMap.closure (by fun_prop) hFull
    have hFixed (field : DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :
        (diffeomorphismGhostProjection period hPeriod (metric .plus)).rangeRestrict field.val = field := by
      apply Subtype.ext
      exact (Set.ext_iff.mp (diffeomorphismGhostProjection_range_eq_fixed period hPeriod (metric .plus)) field.val).mp field.property
    have hEqual : project (pair.1.val, pair.2.val) = pair := Prod.ext (hFixed pair.1) (hFixed pair.2)
    rw [hEqual] at hProjected
    exact hProjected
  · exact closure_minimal
      (by rintro pair ⟨field, rfl⟩; exact hessianGhostReduced_smooth_graph period hPeriod reference metric couplings field)
      (hessianGhostReduced_isClosed period hPeriod reference metric couplings)

theorem hessianGhostReduced_feature_single :
    Function.Injective (fun graph : linearFeatureGraphClosure (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
      (diffeomorphismGhostPairSmooth period hPeriod (metric .plus))
      (hessianGhostReducedSmoothLinearMap period hPeriod reference metric couplings) => graph.val.1) :=
  featureClosure_injective_of_closed_extension (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) _ _
    (hessianGhostReduced period hPeriod reference metric couplings)
    (hessianGhostReduced_isClosed period hPeriod reference metric couplings)
    (hessianGhostReduced_smooth_graph period hPeriod reference metric couplings)

theorem hessianGhostReduced_eq_closedFeature :
    hessianGhostReduced period hPeriod reference metric couplings =
      closedFeatureOperator (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) (diffeomorphismGhostPairSmooth period hPeriod (metric .plus))
        (hessianGhostReducedSmoothLinearMap period hPeriod reference metric couplings) := by
  apply LinearPMap.eq_of_eq_graph
  rw [hessianGhostReduced_graph_closure,
    closedFeatureOperator_graph (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) _ _ (hessianGhostReduced_feature_single period hPeriod reference metric couplings)]

theorem hessianGhostReduced_hasCore :
    (hessianGhostReduced period hPeriod reference metric couplings).HasCore
      (diffeomorphismGhostPairSmooth period hPeriod (metric .plus)).range := by
  rw [hessianGhostReduced_eq_closedFeature]
  exact closedFeatureOperator_hasCore (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) _ _
    (hessianGhostReduced_feature_single period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12HessianGhostReducedCore4D
