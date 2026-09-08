import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerExpanded4D

/-! # Euler decomposition of the paired full-BRST action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2FullBRSTEulerDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FiniteFramePairedC2FullBRSTGaugeCore period hPeriod
  source plusFrame minusFrame plusMetric minusMetric
local notation "AbelianInput" => FiniteFramePairedC2AbelianBRSTCore period hPeriod
  plusFrame minusFrame plusMetric minusMetric
local notation "DiffeomorphismInput" => FiniteFramePairedDiffeomorphismBRSTCore period hPeriod
  source plusFrame minusFrame plusMetric minusMetric
local notation "Domain" => finiteFramePairedC2FullBRSTGaugeDomain period hPeriod
  source plusFrame minusFrame plusMetric minusMetric

/-- Actual Euler map of the paired Abelian BRST block. -/
def finiteFramePairedC2AbelianBRSTEuler (input : AbelianInput) :
    AbelianInput →L[Real] Real :=
  fderiv Real (finiteFramePairedC2AbelianBRSTAction period hPeriod plusFrame minusFrame
    plusMetric minusMetric) input

/-- The full-BRST Euler map is the sum of its projected Abelian and diffeomorphism Eulers. -/
theorem finiteFramePairedC2FullBRSTGaugeEuler_eq_component_eulers
    (couplings : GlobalCandidateAActionCouplings) (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedC2FullBRSTGaugeEuler period hPeriod source plusFrame minusFrame plusMetric
        minusMetric couplings input =
      (finiteFramePairedC2AbelianBRSTEuler period hPeriod plusFrame minusFrame plusMetric
        minusMetric
        (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
          plusMetric minusMetric input)).comp
            (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
              plusMetric minusMetric) +
      (finiteFramePairedDiffeomorphismBRSTEuler period hPeriod source plusFrame minusFrame plusMetric
        minusMetric couplings
        (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame
          minusFrame plusMetric minusMetric input)).comp
            (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame
              minusFrame plusMetric minusMetric) := by
  have hAbelianMem :
      finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
          plusMetric minusMetric input ∈
        finiteFramePairedC2AbelianBRSTDomain period hPeriod plusFrame minusFrame plusMetric
          minusMetric :=
    ⟨⟨hInput.1.1.1, Set.mem_univ _⟩, ⟨hInput.1.2.1, Set.mem_univ _⟩⟩
  have hDiffeomorphismMem :
      finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame
          minusFrame plusMetric minusMetric input ∈
        finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame minusFrame plusMetric
          minusMetric :=
    ⟨hInput.1, Set.mem_univ _⟩
  have hAbelianBase : HasFDerivAt
      (finiteFramePairedC2AbelianBRSTAction period hPeriod plusFrame minusFrame plusMetric minusMetric)
      (finiteFramePairedC2AbelianBRSTEuler period hPeriod plusFrame minusFrame plusMetric minusMetric
        (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
          plusMetric minusMetric input))
      (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
        plusMetric minusMetric input) := by
    unfold finiteFramePairedC2AbelianBRSTEuler
    exact (((finiteFramePairedC2AbelianBRSTAction_contDiffOn period hPeriod plusFrame minusFrame
      plusMetric minusMetric _ hAbelianMem).contDiffAt
        ((finiteFramePairedC2AbelianBRSTDomain_isOpen period hPeriod plusFrame minusFrame plusMetric
          minusMetric).mem_nhds hAbelianMem)).differentiableAt (by norm_num)).hasFDerivAt
  have hAbelian := hAbelianBase.comp input
    (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
      plusMetric minusMetric).hasFDerivAt
  have hDiffeomorphismBase :=
    finiteFramePairedDiffeomorphismBRSTAction_hasFDerivAt period hPeriod source plusFrame minusFrame
      plusMetric minusMetric couplings
      (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame
        minusFrame plusMetric minusMetric input) hDiffeomorphismMem
  have hDiffeomorphism := hDiffeomorphismBase.comp input
    (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame
      minusFrame plusMetric minusMetric).hasFDerivAt
  unfold finiteFramePairedC2FullBRSTGaugeEuler finiteFramePairedC2FullBRSTGaugeAction
  exact (hAbelian.add hDiffeomorphism).fderiv

end
end P0EFTJanusFiniteFramePairedC2FullBRSTEulerDecomposition4D
end JanusFormal
