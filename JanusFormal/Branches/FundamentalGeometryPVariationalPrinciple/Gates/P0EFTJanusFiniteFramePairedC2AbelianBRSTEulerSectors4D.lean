import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerGaugeSlots4D

/-! # Sector decomposition of the paired Abelian BRST Euler map -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2AbelianBRSTEulerSectors4D

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
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTEulerDecomposition4D

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

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "PlusInput" => FiniteFrameC2AbelianBRSTCore period hPeriod plusFrame plusMetric
local notation "MinusInput" => FiniteFrameC2AbelianBRSTCore period hPeriod minusFrame minusMetric
local notation "PairInput" => FiniteFramePairedC2AbelianBRSTCore period hPeriod plusFrame minusFrame
  plusMetric minusMetric
local notation "Domain" => finiteFramePairedC2AbelianBRSTDomain period hPeriod plusFrame minusFrame
  plusMetric minusMetric

/-- Actual Euler map of one finite-frame Abelian BRST sector. -/
def finiteFrameC2AbelianBRSTEuler
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (input : FiniteFrameC2AbelianBRSTCore period hPeriod frame metric) :
    FiniteFrameC2AbelianBRSTCore period hPeriod frame metric →L[Real] Real :=
  fderiv Real (finiteFrameC2AbelianBRSTAction period hPeriod frame metric) input

/-- The paired Abelian Euler map is the sum of the two sector Eulers. -/
theorem finiteFramePairedC2AbelianBRSTEuler_eq_sector_eulers
    (input : PairInput) (hInput : input ∈ Domain) :
    finiteFramePairedC2AbelianBRSTEuler period hPeriod plusFrame minusFrame plusMetric minusMetric
        input =
      (finiteFrameC2AbelianBRSTEuler period hPeriod plusFrame plusMetric input.1).comp
          (ContinuousLinearMap.fst Real PlusInput MinusInput) +
        (finiteFrameC2AbelianBRSTEuler period hPeriod minusFrame minusMetric input.2).comp
          (ContinuousLinearMap.snd Real PlusInput MinusInput) := by
  have hFst : HasFDerivAt (fun current : PairInput => current.1)
      (ContinuousLinearMap.fst Real PlusInput MinusInput) input := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : PairInput => current.2)
      (ContinuousLinearMap.snd Real PlusInput MinusInput) input := by
    fun_prop
  have hPlus :=
    (finiteFrameC2AbelianBRSTAction_hasFDerivAt period hPeriod plusFrame plusMetric input.1
      hInput.1).comp input hFst
  have hMinus :=
    (finiteFrameC2AbelianBRSTAction_hasFDerivAt period hPeriod minusFrame minusMetric input.2
      hInput.2).comp input hSnd
  unfold finiteFramePairedC2AbelianBRSTEuler finiteFramePairedC2AbelianBRSTAction
    finiteFrameC2AbelianBRSTEuler
  change fderiv Real
      ((fun current : PairInput =>
        finiteFrameC2AbelianBRSTAction period hPeriod plusFrame plusMetric current.1) +
       (fun current : PairInput =>
        finiteFrameC2AbelianBRSTAction period hPeriod minusFrame minusMetric current.2)) input = _
  exact (hPlus.add hMinus).fderiv

end
end P0EFTJanusFiniteFramePairedC2AbelianBRSTEulerSectors4D
end JanusFormal
