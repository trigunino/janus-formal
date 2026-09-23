import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianFormClosed4D

/-! Exact differential and smooth restrictions of the closed BRST form realization. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianFormClosedDomain4D
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


open P0EFTJanusProgramPT12HessianL2Adjoint4D
open P0EFTJanusProgramPT12HessianFormGraphTests4D

open P0EFTJanusProgramPT12HessianFormAdjoint4D

open P0EFTJanusProgramPT12HessianFormOperator4D

open P0EFTJanusProgramPT12HessianFormSmoothCore4D
open P0EFTJanusProgramPT12SymmetricL2GraphClosure4D

open P0EFTJanusProgramPT12HessianFormClosed4D

theorem hessianFormClosed_differentialRestriction :
    (hessianFormClosed period hPeriod reference metric couplings).domRestrict
      (hessianFeatureMinimal period hPeriod metric).domain =
        hessianL2FormOperator period hPeriod reference metric couplings := by
  have hLow := hessianL2FormOperator_le_closed period hPeriod reference metric couplings
  have hHigh := hessianFormClosed_le_maximal period hPeriod reference metric couplings
  apply LinearPMap.ext
  · ext input
    change (input ∈ (hessianFeatureMinimal period hPeriod metric).domain ∧
      input ∈ (hessianFormClosed period hPeriod reference metric couplings).domain) ↔
      (input ∈ (hessianFeatureMinimal period hPeriod metric).domain ∧
        input ∈ (hessianL2Maximal period hPeriod reference metric couplings).domain)
    exact ⟨fun h => ⟨h.1, hHigh.1 h.2⟩, fun h => ⟨h.1, hLow.1 h⟩⟩
  · intro input hFirst hSecond
    exact hHigh.2 (x := ⟨input, hFirst.2⟩) (y := ⟨input, hSecond.2⟩) rfl

theorem hessianFormClosed_domain_iff_form
    (input : (hessianFeatureMinimal period hPeriod metric).domain) :
    input.val ∈ (hessianFormClosed period hPeriod reference metric couplings).domain ↔
      ∃ output : DiffeomorphismL2 period hPeriod (metric .plus),
        ∀ test : (hessianFeatureMinimal period hPeriod metric).domain,
          inner Real output test.val = hessianL2Form period hPeriod reference metric couplings input test := by
  rw [← hessianL2FormOperator_domain_iff, ← hessianFormClosed_differentialRestriction]
  change input.val ∈ (hessianFormClosed period hPeriod reference metric couplings).domain ↔
    (input.val ∈ (hessianFeatureMinimal period hPeriod metric).domain ∧
      input.val ∈ (hessianFormClosed period hPeriod reference metric couplings).domain)
  exact (and_iff_right input.property).symm

theorem hessianFormClosed_smoothRestriction :
    (hessianFormClosed period hPeriod reference metric couplings).domRestrict
      (diffeomorphismL2Smooth period hPeriod (metric .plus)).range =
        hessianL2OperatorCore period hPeriod reference metric couplings := by
  apply LinearPMap.ext
  · ext input
    change (input ∈ (diffeomorphismL2Smooth period hPeriod (metric .plus)).range ∧
      input ∈ (hessianFormClosed period hPeriod reference metric couplings).domain) ↔
      input ∈ (diffeomorphismL2Smooth period hPeriod (metric .plus)).range
    constructor
    · exact And.left
    · rintro ⟨field, rfl⟩
      exact ⟨⟨field, rfl⟩, (hessianFormClosedSmoothDomain period hPeriod reference metric couplings field).property⟩
  · intro input hFirst hSecond
    obtain ⟨field, rfl⟩ := hSecond
    exact (hessianFormClosed_smooth period hPeriod reference metric couplings field).trans
      (hessianL2OperatorCore_smooth period hPeriod reference metric couplings field).symm

theorem hessianFormClosed_smoothCore_iff :
    (hessianFormClosed period hPeriod reference metric couplings).HasCore
      (diffeomorphismL2Smooth period hPeriod (metric .plus)).range ↔
        hessianFormClosed period hPeriod reference metric couplings =
          hessianL2Minimal period hPeriod reference metric couplings := by
  constructor
  · intro hCore
    have h := hCore.closure_eq
    rw [hessianFormClosed_smoothRestriction] at h
    exact h.symm
  · intro hEqual
    rw [hEqual]
    exact hessianL2Minimal_hasCore period hPeriod reference metric couplings

end
end JanusFormal.P0EFTJanusProgramPT12HessianFormClosedDomain4D