import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianFormAdjoint4D

/-! The densely defined symmetric operator represented by the actual BRST form. -/
namespace JanusFormal.P0EFTJanusProgramPT12HessianFormOperator4D
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

def hessianL2FormOperator : DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real]
    DiffeomorphismL2 period hPeriod (metric .plus) :=
  (hessianL2Maximal period hPeriod reference metric couplings).domRestrict
    (hessianFeatureMinimal period hPeriod metric).domain

def hessianFormDifferentialState (input : (hessianL2FormOperator period hPeriod reference metric couplings).domain) :
    (hessianFeatureMinimal period hPeriod metric).domain := ⟨input.val, input.property.1⟩

theorem hessianL2FormOperator_pairing
    (input : (hessianL2FormOperator period hPeriod reference metric couplings).domain)
    (test : (hessianFeatureMinimal period hPeriod metric).domain) :
    inner Real (hessianL2FormOperator period hPeriod reference metric couplings input) test.val =
      hessianL2Form period hPeriod reference metric couplings
        (hessianFormDifferentialState period hPeriod reference metric couplings input) test :=
  hessianL2Maximal_form_pairing period hPeriod reference metric couplings
    (hessianFormDifferentialState period hPeriod reference metric couplings input) input.property.2 test

theorem hessianL2FormOperator_domain_iff
    (input : (hessianFeatureMinimal period hPeriod metric).domain) :
    input.val ∈ (hessianL2FormOperator period hPeriod reference metric couplings).domain ↔
      ∃ output : DiffeomorphismL2 period hPeriod (metric .plus),
        ∀ test : (hessianFeatureMinimal period hPeriod metric).domain,
          inner Real output test.val = hessianL2Form period hPeriod reference metric couplings input test := by
  change (input.val ∈ (hessianFeatureMinimal period hPeriod metric).domain ∧
    input.val ∈ (hessianL2Maximal period hPeriod reference metric couplings).domain) ↔ _
  rw [and_iff_right input.property]
  exact hessianL2Maximal_domain_iff_form period hPeriod reference metric couplings input

def hessianFormSmoothDomain (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (hessianL2FormOperator period hPeriod reference metric couplings).domain :=
  ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field,
    (hessianFeatureSmoothDomain period hPeriod metric field).property,
    (hessianL2Minimal_le_maximal period hPeriod reference metric couplings).1
      (hessianL2SmoothDomain period hPeriod reference metric couplings field).property⟩

theorem hessianL2FormOperator_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    hessianL2FormOperator period hPeriod reference metric couplings
      (hessianFormSmoothDomain period hPeriod reference metric couplings field) =
        hessianSmoothRiesz period hPeriod reference metric couplings field := by
  let smooth := hessianFormSmoothDomain period hPeriod reference metric couplings field
  have h := (hessianL2Minimal_le_maximal period hPeriod reference metric couplings).2
    (x := hessianL2SmoothDomain period hPeriod reference metric couplings field)
    (y := ⟨smooth.val, smooth.property.2⟩) rfl
  exact h.symm.trans (hessianL2Minimal_smooth period hPeriod reference metric couplings field)

theorem hessianL2FormOperator_denseDomain : Dense
    ((hessianL2FormOperator period hPeriod reference metric couplings).domain :
      Set (DiffeomorphismL2 period hPeriod (metric .plus))) := by
  apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).mono
  rintro _ ⟨field, rfl⟩
  exact (hessianFormSmoothDomain period hPeriod reference metric couplings field).property

theorem hessianL2FormOperator_isFormalAdjoint :
    LinearPMap.IsFormalAdjoint (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
      (F := DiffeomorphismL2 period hPeriod (metric .plus))
      (hessianL2FormOperator period hPeriod reference metric couplings)
      (hessianL2FormOperator period hPeriod reference metric couplings) := by
  intro first second
  let x := hessianFormDifferentialState period hPeriod reference metric couplings first
  let y := hessianFormDifferentialState period hPeriod reference metric couplings second
  exact (hessianL2FormOperator_pairing period hPeriod reference metric couplings first y).trans
    ((hessianL2Form_comm period hPeriod reference metric couplings x y).trans
      ((hessianL2FormOperator_pairing period hPeriod reference metric couplings second x).symm.trans
        (real_inner_comm first.val (hessianL2FormOperator period hPeriod reference metric couplings second))))

theorem hessianL2FormOperator_le_maximal : hessianL2FormOperator period hPeriod reference metric couplings ≤
    hessianL2Maximal period hPeriod reference metric couplings := LinearPMap.domRestrict_le

theorem hessianL2FormOperator_isClosable : (hessianL2FormOperator period hPeriod reference metric couplings).IsClosable :=
  (hessianL2Maximal_isClosed period hPeriod reference metric couplings).isClosable.leIsClosable
    (hessianL2FormOperator_le_maximal period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12HessianFormOperator4D