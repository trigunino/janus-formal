import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricAbelianBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D

/-! # The complete Abelian BRST action along the mobile physical family

The mobile total potential is re-expressed in the fixed reference frames
before evaluation. Both metric variations and all independent nonminimal
fields enter the action on one fixed open domain.
-/

namespace JanusFormal
namespace P0EFTJanusPairedMobileAbelianBRSTAction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D
open P0EFTJanusVariableMetricC2LorenzFPFeatures4D
open P0EFTJanusVariableMetricAbelianBRSTAction4D

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

/-- Independent B, antighost and ghost coordinates. -/
abbrev AbelianBRSTNonminimalCore :=
  (Fin 2 → CanonicalPhysicalBulkL2 period hPeriod) ×
    ((Fin 2 → CanonicalPhysicalBulkL2 period hPeriod) × AbelianGhostC2Core period hPeriod)

abbrev PairedMobileAbelianBRSTCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase ×
    (AbelianBRSTNonminimalCore period hPeriod × AbelianBRSTNonminimalCore period hPeriod)

variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

def pairedMobileAbelianBRSTDomain :
    Set (PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase) :=
  regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod plusBase minusBase ×ˢ univ

theorem pairedMobileAbelianBRSTDomain_isOpen :
    IsOpen (pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase) :=
  ((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
    plusBase minusBase).prod isOpen_univ).prod isOpen_univ

def pairedMobileAbelianBRSTInput
    (input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase) :
    PairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase :=
  (((regularGeneralMetricC2PairedPlusGaugeCoefficientInput period hPeriod configuration
        plusBase minusBase input.1).1,
      ((pairedMobileGaugeC2Input period hPeriod configuration plusBase minusBase input.1).1,
        input.2.1)),
   ((regularGeneralMetricC2PairedMinusGaugeCoefficientInput period hPeriod configuration
        plusBase minusBase input.1).1,
      ((pairedMobileGaugeC2Input period hPeriod configuration plusBase minusBase input.1).2,
        input.2.2)))

theorem pairedMobileAbelianBRSTInput_contDiffOn_two :
    ContDiffOn Real 2
      (pairedMobileAbelianBRSTInput period hPeriod configuration plusBase minusBase)
      (pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase) := by
  have hProjection : ContDiff Real 2
      (fun input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase => input.1) :=
    contDiff_fst
  have hSource : MapsTo
      (fun input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase => input.1)
      (pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod plusBase minusBase) :=
    fun _ hInput => hInput.1
  have hPlusFields : ContDiff Real 2
      (fun input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase => input.2.1) :=
    contDiff_snd.fst
  have hMinusFields : ContDiff Real 2
      (fun input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase => input.2.2) :=
    contDiff_snd.snd
  have hPlus := (regularGeneralMetricC2PairedPlusGaugeCoefficientInput_contDiffOn_two
    period hPeriod configuration plusBase minusBase).comp hProjection.contDiffOn hSource
  have hMinus := (regularGeneralMetricC2PairedMinusGaugeCoefficientInput_contDiffOn_two
    period hPeriod configuration plusBase minusBase).comp hProjection.contDiffOn hSource
  have hGauge := (pairedMobileGaugeC2Input_contDiffOn_two
    period hPeriod configuration plusBase minusBase).comp hProjection.contDiffOn hSource
  exact (hPlus.fst.prodMk (hGauge.fst.prodMk hPlusFields.contDiffOn)).prodMk
    (hMinus.fst.prodMk (hGauge.snd.prodMk hMinusFields.contDiffOn))

theorem pairedMobileAbelianBRSTInput_mem
    {input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase}
    (hInput : input ∈ pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase) :
    pairedMobileAbelianBRSTInput period hPeriod configuration plusBase minusBase input ∈
      pairedVariableMetricAbelianBRSTDomain period hPeriod plusBase minusBase := by
  have hPlus := (regularGeneralMetricC2PairedPlusGaugeCoefficientInput_mem
    period hPeriod configuration plusBase minusBase hInput.1).1
  have hMinus := (regularGeneralMetricC2PairedMinusGaugeCoefficientInput_mem
    period hPeriod configuration plusBase minusBase hInput.1).1
  exact ⟨⟨hPlus.1, Set.mem_univ _⟩, ⟨hMinus.1, Set.mem_univ _⟩⟩

def pairedMobileAbelianBRSTAction
    (input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase) : Real :=
  pairedVariableMetricAbelianBRSTAction period hPeriod plusBase minusBase
    (pairedMobileAbelianBRSTInput period hPeriod configuration plusBase minusBase input)

theorem pairedMobileAbelianBRSTAction_contDiffOn_two :
    ContDiffOn Real 2
      (pairedMobileAbelianBRSTAction period hPeriod configuration plusBase minusBase)
      (pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase) :=
  ((pairedVariableMetricAbelianBRSTAction_contDiffOn period hPeriod plusBase minusBase).of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
      (pairedMobileAbelianBRSTInput_contDiffOn_two period hPeriod configuration plusBase minusBase)
      (fun _ hInput => pairedMobileAbelianBRSTInput_mem period hPeriod configuration
        plusBase minusBase hInput)

/-- The derivative includes both the metric change and the mobile frame transport. -/
theorem pairedMobileAbelianBRSTAction_hasFDerivAt
    (input : PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase)
    (hInput : input ∈ pairedMobileAbelianBRSTDomain period hPeriod plusBase minusBase) :
    HasFDerivAt
      (pairedMobileAbelianBRSTAction period hPeriod configuration plusBase minusBase)
      ((fderiv Real (pairedVariableMetricAbelianBRSTAction period hPeriod plusBase minusBase)
        (pairedMobileAbelianBRSTInput period hPeriod configuration plusBase minusBase input)).comp
          (fderiv Real
            (pairedMobileAbelianBRSTInput period hPeriod configuration plusBase minusBase) input))
      input := by
  have hInner := ((pairedMobileAbelianBRSTInput_contDiffOn_two period hPeriod configuration
    plusBase minusBase input hInput).contDiffAt
      ((pairedMobileAbelianBRSTDomain_isOpen period hPeriod plusBase minusBase).mem_nhds hInput)
        ).differentiableAt (by norm_num)
  have hMapped := pairedMobileAbelianBRSTInput_mem period hPeriod configuration
    plusBase minusBase hInput
  have hOuter := ((pairedVariableMetricAbelianBRSTAction_contDiffOn period hPeriod
    plusBase minusBase _ hMapped).contDiffAt
      ((pairedVariableMetricAbelianBRSTDomain_isOpen period hPeriod plusBase minusBase).mem_nhds
        hMapped)).differentiableAt (by simp)
  exact hOuter.hasFDerivAt.comp input hInner.hasFDerivAt

end
end P0EFTJanusPairedMobileAbelianBRSTAction4D
end JanusFormal
