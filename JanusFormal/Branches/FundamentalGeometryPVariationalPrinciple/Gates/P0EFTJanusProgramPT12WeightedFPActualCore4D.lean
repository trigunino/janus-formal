import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostDiagonal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D

/-! The weighted FP block reproduces the actual ghost Hessian on its smooth core. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedFPActualCore4D
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

open P0EFTJanusProgramPT12HessianGhostDiagonal4D
open P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
open P0EFTJanusProgramPT12WeightedFPSmooth4D
open P0EFTJanusProgramPT12WeightedFPBlock4D

theorem hessianSmoothRiesz_ghost_offDiagonal (j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 1
      (hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 0 j field)) =
      hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 0 j field) := by
  have h := hessianSmoothRiesz_ghost_commutes period hPeriod reference metric couplings
    (diffeomorphismTripletTransfer period hPeriod 0 j field)
  change hessianSmoothRiesz period hPeriod reference metric couplings
    (diffeomorphismTripletTransfer period hPeriod 0 j field) = _ at h
  change _ = diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0 _ +
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 1 _ at h
  rw [hessianSmoothRiesz_ghost_diagonal_zero, zero_add] at h
  exact h.symm

theorem hessianSmoothRiesz_antighost_offDiagonal (j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0
      (hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 1 j field)) =
      hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 1 j field) := by
  have h := hessianSmoothRiesz_ghost_commutes period hPeriod reference metric couplings
    (diffeomorphismTripletTransfer period hPeriod 1 j field)
  change hessianSmoothRiesz period hPeriod reference metric couplings
    (diffeomorphismTripletTransfer period hPeriod 1 j field) = _ at h
  change _ = diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0 _ +
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 1 _ at h
  rw [hessianSmoothRiesz_antighost_diagonal_zero, add_zero] at h
  exact h.symm

include metric in
theorem diffeomorphismTripletTransfer_comp (i j k : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletTransfer period hPeriod i j
      (diffeomorphismTripletTransfer period hPeriod j k field) =
      diffeomorphismTripletTransfer period hPeriod i k field := by
  apply diffeomorphismL2Smooth_injective period hPeriod (metric .plus)
  rw [← diffeomorphismTripletL2_smooth, ← diffeomorphismTripletL2_smooth,
    diffeomorphismTripletL2_comp_apply, diffeomorphismTripletL2_smooth]

theorem weightedFPAssemble_smooth_input
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ((diffeomorphismGhostPairIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2
        (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 first,
         diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 second))).val =
      diffeomorphismL2Smooth period hPeriod (metric .plus)
        (diffeomorphismTripletTransfer period hPeriod 0 0 first +
         diffeomorphismTripletTransfer period hPeriod 1 0 second) := by
  change diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0
    (diffeomorphismL2Smooth period hPeriod (metric .plus) first) +
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 0
      (diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0
        (diffeomorphismL2Smooth period hPeriod (metric .plus) second)) = _
  rw [diffeomorphismTripletL2_comp_apply, diffeomorphismTripletL2_smooth,
    diffeomorphismTripletL2_smooth, map_add]

theorem weightedFPAssemble_smooth_output
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ((diffeomorphismGhostPairIsometry period hPeriod (metric .plus))
      (WithLp.toLp 2
        (weightedFPTransposeSmooth period hPeriod reference metric couplings second,
         weightedFPSmooth period hPeriod reference metric couplings first))).val =
      hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 0 0 first +
         diffeomorphismTripletTransfer period hPeriod 1 0 second) := by
  change diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0
    (hessianSmoothRiesz period hPeriod reference metric couplings
      (diffeomorphismTripletTransfer period hPeriod 1 0 second)) +
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 0
      (diffeomorphismTripletL2 period hPeriod (metric .plus) 0 1
        (hessianSmoothRiesz period hPeriod reference metric couplings
          (diffeomorphismTripletTransfer period hPeriod 0 0 first))) = _
  rw [diffeomorphismTripletL2_comp_apply, hessianSmoothRiesz_antighost_offDiagonal,
    hessianSmoothRiesz_ghost_offDiagonal]
  change (hessianSmoothRieszLinearMap period hPeriod reference metric couplings) _ +
    (hessianSmoothRieszLinearMap period hPeriod reference metric couplings) _ =
    (hessianSmoothRieszLinearMap period hPeriod reference metric couplings) (_ + _)
  rw [map_add, add_comm]

theorem weightedFPActualGhostBlock_reduced_smooth_graph
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismGhostPairSmooth period hPeriod (metric .plus) field,
     hessianGhostReducedSmoothOutput period hPeriod reference metric couplings field) ∈
      (weightedFPActualGhostBlock period hPeriod reference metric couplings).graph := by
  have h := weightedFPActualGhostBlock_smooth_graph period hPeriod reference metric couplings
    field (diffeomorphismTripletTransfer period hPeriod 0 1 field)
  have hInput :
      (diffeomorphismGhostPairIsometry period hPeriod (metric .plus))
        (WithLp.toLp 2
          (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 field,
           diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0
             (diffeomorphismTripletTransfer period hPeriod 0 1 field))) =
        diffeomorphismGhostPairSmooth period hPeriod (metric .plus) field := by
    apply Subtype.ext
    rw [weightedFPAssemble_smooth_input, diffeomorphismTripletTransfer_comp period hPeriod metric,
      hessianGhostSmooth_eq_transfer]
    exact (hessianGhostSmooth_L2 period hPeriod (metric .plus) field).symm
  have hOutput :
      (diffeomorphismGhostPairIsometry period hPeriod (metric .plus))
        (WithLp.toLp 2
          (weightedFPTransposeSmooth period hPeriod reference metric couplings
             (diffeomorphismTripletTransfer period hPeriod 0 1 field),
           weightedFPSmooth period hPeriod reference metric couplings field)) =
        hessianGhostReducedSmoothOutput period hPeriod reference metric couplings field := by
    apply Subtype.ext
    rw [weightedFPAssemble_smooth_output, diffeomorphismTripletTransfer_comp period hPeriod metric,
      hessianGhostSmooth_eq_transfer]
    exact hessianSmoothRiesz_ghost_commutes period hPeriod reference metric couplings field
  rw [hInput, hOutput] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12WeightedFPActualCore4D