import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostReduced4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D

/-! The ghost and antighost diagonal columns of the actual Hessian vanish. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianGhostDiagonal4D
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

theorem hessianTripletSmooth_readout_zero (sector : Sector) (i j k : Fin 3) (hki : k ≠ i)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) k
      (diffeomorphismL2Smooth period hPeriod (metric .plus)
        (diffeomorphismTripletTransfer period hPeriod i j field)) = 0 := by
  rw [sectorTripletL2_smooth]
  fin_cases k <;>
    change globalNormalizedVectorFrameL2LinearMap period hPeriod (metric sector)
      (if _ = i then _ else 0) = 0 <;>
    (split_ifs with heq <;> first | exact (hki heq).elim | exact map_zero _)

theorem hessianTripletSmooth_antighost_fp_zero (sector : Sector) (j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianFeaturesSmooth period hPeriod metric
      (diffeomorphismTripletTransfer period hPeriod 1 j field) (1, sector)).val = 0 := by
  rw [hessianFeaturesSmooth_fp]
  change (actualFPSmoothOutput period hPeriod metric (0 : GlobalDiffeomorphismGhostField period hPeriod) sector).val = 0
  rw [map_zero]
  rfl

theorem hessianSectorForm_ghost_diagonal_zero (sector : Sector) (j k : Fin 3)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianSectorForm period hPeriod reference metric sector
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 0 j first))
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 0 k second)) = 0 := by
  simp only [hessianSectorForm, hessianFeatureMinimal_smooth]
  simp only [hessianFeatureSmoothDomain,
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 0 j 2 (by decide),
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 0 k 2 (by decide),
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 0 j 1 (by decide),
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 0 k 1 (by decide),
    inner_zero_left, inner_zero_right, mul_zero, add_zero, sub_zero]

theorem hessianSectorForm_antighost_diagonal_zero (sector : Sector) (j k : Fin 3)
    (first second : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianSectorForm period hPeriod reference metric sector
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 1 j first))
      (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 1 k second)) = 0 := by
  simp only [hessianSectorForm, hessianFeatureMinimal_smooth]
  simp only [hessianFeatureSmoothDomain,
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 1 j 2 (by decide),
    hessianTripletSmooth_readout_zero period hPeriod reference metric sector 1 k 2 (by decide),
    hessianTripletSmooth_antighost_fp_zero,
    inner_zero_left, inner_zero_right, mul_zero, add_zero, sub_zero]

theorem hessianSmoothRiesz_ghost_diagonal_zero (j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0
      (hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 0 j field)) = 0 := by
  apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).eq_of_inner_left (𝕜 := Real)
  intro test
  rw [diffeomorphismTripletL2_pairing, diffeomorphismTripletL2_smooth, inner_zero_left]
  have h := hessianSmoothRiesz_pairing period hPeriod reference metric couplings
    (diffeomorphismTripletTransfer period hPeriod 0 j field)
    (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 0 0 test))
  simp only [hessianL2Form, hessianSectorForm_ghost_diagonal_zero, mul_zero, add_zero] at h
  simpa only [hessianFeatureSmoothDomain] using h

theorem hessianSmoothRiesz_antighost_diagonal_zero (j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 1
      (hessianSmoothRiesz period hPeriod reference metric couplings
        (diffeomorphismTripletTransfer period hPeriod 1 j field)) = 0 := by
  apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).eq_of_inner_left (𝕜 := Real)
  intro test
  rw [diffeomorphismTripletL2_pairing, diffeomorphismTripletL2_smooth, inner_zero_left]
  have h := hessianSmoothRiesz_pairing period hPeriod reference metric couplings
    (diffeomorphismTripletTransfer period hPeriod 1 j field)
    (hessianFeatureSmoothDomain period hPeriod metric (diffeomorphismTripletTransfer period hPeriod 1 1 test))
  simp only [hessianL2Form, hessianSectorForm_antighost_diagonal_zero, mul_zero, add_zero] at h
  simpa only [hessianFeatureSmoothDomain] using h

end
end JanusFormal.P0EFTJanusProgramPT12HessianGhostDiagonal4D
