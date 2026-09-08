import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2AbelianBRSTEulerSectors4D

/-! # Sector decomposition of the paired diffeomorphism BRST Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedDiffeomorphismBRSTEulerSectors4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
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
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D

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
local notation "Input" => FiniteFramePairedDiffeomorphismBRSTCore period hPeriod source plusFrame
  minusFrame plusMetric minusMetric
local notation "PlusInput" => FiniteFrameC2DiffeomorphismBRSTCore period hPeriod plusFrame plusMetric
local notation "MinusInput" => FiniteFrameC2DiffeomorphismBRSTCore period hPeriod minusFrame minusMetric
local notation "Domain" => finiteFramePairedDiffeomorphismBRSTDomain period hPeriod source plusFrame
  minusFrame plusMetric minusMetric

/-- The paired diffeomorphism Euler is the weighted sum of the two pulled-back sector Eulers. -/
theorem finiteFramePairedDiffeomorphismBRSTEuler_eq_sector_eulers
    (couplings : GlobalCandidateAActionCouplings) (input : Input) (hInput : input ∈ Domain) :
    finiteFramePairedDiffeomorphismBRSTEuler period hPeriod source plusFrame minusFrame plusMetric
        minusMetric couplings input =
      candidateAPlusEinsteinKineticWeight couplings •
        (finiteFrameC2DiffeomorphismBRSTEuler period hPeriod plusFrame plusMetric
          (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
            plusMetric minusMetric input)).comp
          (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
            plusMetric minusMetric) +
      candidateAMinusEinsteinKineticWeight couplings •
        (finiteFrameC2DiffeomorphismBRSTEuler period hPeriod minusFrame minusMetric
          (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
            plusMetric minusMetric input)).comp
          (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
            plusMetric minusMetric) := by
  have hPlusBase := finiteFrameC2DiffeomorphismBRSTAction_hasFDerivAt period hPeriod plusFrame
    plusMetric (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
      plusMetric minusMetric input) ⟨hInput.1.1, Set.mem_univ _⟩
  have hMinusBase := finiteFrameC2DiffeomorphismBRSTAction_hasFDerivAt period hPeriod minusFrame
    minusMetric (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
      plusMetric minusMetric input) ⟨hInput.1.2, Set.mem_univ _⟩
  have hPlus := (hPlusBase.comp input
    (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod source plusFrame minusFrame
      plusMetric minusMetric).hasFDerivAt).const_mul
        (candidateAPlusEinsteinKineticWeight couplings)
  have hMinus := (hMinusBase.comp input
    (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod source plusFrame minusFrame
      plusMetric minusMetric).hasFDerivAt).const_mul
        (candidateAMinusEinsteinKineticWeight couplings)
  unfold finiteFramePairedDiffeomorphismBRSTEuler finiteFramePairedDiffeomorphismBRSTAction
  exact (hPlus.add hMinus).fderiv

end
end P0EFTJanusFiniteFramePairedDiffeomorphismBRSTEulerSectors4D
end JanusFormal
