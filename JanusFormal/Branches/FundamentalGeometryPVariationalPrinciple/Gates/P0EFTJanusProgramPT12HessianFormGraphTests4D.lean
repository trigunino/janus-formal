import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianL2OperatorClosed4D

/-! Smooth tests determine the full BRST form on the common differential graph domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianFormGraphTests4D
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

open P0EFTJanusProgramPT12HessianSmoothRiesz4D
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12HessianL2OperatorCore4D
open P0EFTJanusProgramPT12SymmetricL2Closure4D

open P0EFTJanusProgramPT12HessianL2OperatorClosed4D


def hessianSectorTestPairing (sector : Sector) (first : (hessianFeatureMinimal period hPeriod metric).domain) (second : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod) : Real :=
  inner Real ((hessianFeatureMinimal period hPeriod metric first (0, sector)).val)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 second.1) +
  inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val)
    ((second.2 (0, sector)).val) -
  (1 / 2 : Real) * inner Real (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 second.1) -
  (1 / 2 : Real) * inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 2 first.val)
    (sectorTripletFlatL2 period hPeriod reference (metric sector) (metric .plus) 2 second.1) -
  inner Real ((hessianFeatureMinimal period hPeriod metric first (1, sector)).val)
    (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 second.1) -
  inner Real (sectorTripletL2 period hPeriod reference (metric sector) (metric .plus) 1 first.val)
    ((second.2 (1, sector)).val)

theorem hessianSectorTestPairing_continuous (sector : Sector)
    (first : (hessianFeatureMinimal period hPeriod metric).domain) :
    Continuous (hessianSectorTestPairing period hPeriod reference metric sector first) := by
  unfold hessianSectorTestPairing
  fun_prop

def hessianTestPairing (first : (hessianFeatureMinimal period hPeriod metric).domain)
    (second : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod) : Real :=
  candidateAPlusEinsteinKineticWeight couplings * hessianSectorTestPairing period hPeriod reference metric .plus first second +
    candidateAMinusEinsteinKineticWeight couplings * hessianSectorTestPairing period hPeriod reference metric .minus first second

theorem hessianTestPairing_continuous (first : (hessianFeatureMinimal period hPeriod metric).domain) :
    Continuous (hessianTestPairing period hPeriod reference metric couplings first) :=
  ((hessianSectorTestPairing_continuous period hPeriod reference metric .plus first).const_mul _).add
    ((hessianSectorTestPairing_continuous period hPeriod reference metric .minus first).const_mul _)

theorem hessianTestPairing_onGraph (first second : (hessianFeatureMinimal period hPeriod metric).domain) :
    hessianTestPairing period hPeriod reference metric couplings first
      (second.val, hessianFeatureMinimal period hPeriod metric second) =
        hessianL2Form period hPeriod reference metric couplings first second := rfl

theorem hessianL2Form_smooth_tests_iff (input : (hessianFeatureMinimal period hPeriod metric).domain)
    (output : DiffeomorphismL2 period hPeriod (metric .plus)) :
    (∀ test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod,
      inner Real output (diffeomorphismL2Smooth period hPeriod (metric .plus) test) =
        hessianL2Form period hPeriod reference metric couplings input (hessianFeatureSmoothDomain period hPeriod metric test)) ↔
    (∀ test : (hessianFeatureMinimal period hPeriod metric).domain,
      inner Real output test.val = hessianL2Form period hPeriod reference metric couplings input test) := by
  constructor
  · intro h test
    have hPair : (test.val, hessianFeatureMinimal period hPeriod metric test) ∈
        (hessianFeatureCore period hPeriod metric).graph.topologicalClosure := by
      rw [← hessianFeatureMinimal_graph period hPeriod metric reference]
      exact (hessianFeatureMinimal period hPeriod metric).mem_graph test
    have hClosed : IsClosed {value : DiffeomorphismL2 period hPeriod (metric .plus) × HessianFeatureL2 period hPeriod |
        inner Real output value.1 = hessianTestPairing period hPeriod reference metric couplings input value} :=
      isClosed_eq (by fun_prop) (hessianTestPairing_continuous period hPeriod reference metric couplings input)
    change inner Real output (test.val, hessianFeatureMinimal period hPeriod metric test).1 =
      hessianTestPairing period hPeriod reference metric couplings input (test.val, hessianFeatureMinimal period hPeriod metric test)
    apply (closure_minimal _ hClosed) hPair
    intro value hValue
    obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hValue
    rcases field with ⟨field, hField⟩
    obtain ⟨smooth, rfl⟩ := hField
    have hValueEq : value = (diffeomorphismL2Smooth period hPeriod (metric .plus) smooth,
        hessianFeaturesSmooth period hPeriod metric smooth) := by
      apply Prod.ext
      · exact hInput.symm
      · exact hOutput.symm.trans (hessianFeatureCore_smooth period hPeriod metric smooth)
    change inner Real output value.1 = hessianTestPairing period hPeriod reference metric couplings input value
    rw [hValueEq, ← hessianFeatureMinimal_smooth]
    exact h smooth
  · intro h test
    exact h (hessianFeatureSmoothDomain period hPeriod metric test)

end
end JanusFormal.P0EFTJanusProgramPT12HessianFormGraphTests4D