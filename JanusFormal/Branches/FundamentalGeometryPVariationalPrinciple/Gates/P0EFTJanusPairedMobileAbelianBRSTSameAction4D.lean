import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileAbelianBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricAbelianBRSTSameAction4D

/-! # Same-action agreement along the actual paired mobile physical family

The physical direction supplies both moving metrics and total potentials.
The independent nonminimal fields are retained in every sector.
-/

namespace JanusFormal
namespace P0EFTJanusPairedMobileAbelianBRSTSameAction4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D
open P0EFTJanusVariableMetricC2FPSmoothAgreement4D
open P0EFTJanusVariableMetricAbelianBRSTAction4D
open P0EFTJanusVariableMetricAbelianBRSTSameAction4D
open P0EFTJanusPairedMobileAbelianBRSTAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- No nonminimal coordinate is constrained to vanish. -/
def smoothAbelianBRSTNonminimalCore
    (fields : GlobalAbelianNonminimalFields period hPeriod) :
    AbelianBRSTNonminimalCore period hPeriod :=
  (globalGaugeLieFieldL2Coordinates period hPeriod fields.nakanishiLautrup.field,
    (globalGaugeLieFieldL2Coordinates period hPeriod fields.antighost.field,
      smoothAbelianGhostC2Core period hPeriod fields.ghost.field))

variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

def smoothPairedMobileAbelianBRSTCore
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (nonminimal : Sector → GlobalAbelianNonminimalFields period hPeriod) :
    PairedMobileAbelianBRSTCore period hPeriod plusBase minusBase :=
  (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
      configuration plusBase minusBase direction,
    (smoothAbelianBRSTNonminimalCore period hPeriod (nonminimal .plus),
      smoothAbelianBRSTNonminimalCore period hPeriod (nonminimal .minus)))

def pairedMobileAbelianMetricAt
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    Sector → SmoothGeneralLorentzMetric period hPeriod
  | .plus => (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus) hDirection.plus_mem).metric
  | .minus => (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus) hDirection.minus_mem).metric

/-- The completed input is the smooth lift of the same total physical fields. -/
theorem pairedMobileAbelianBRSTInput_projected
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (nonminimal : Sector → GlobalAbelianNonminimalFields period hPeriod) :
    pairedMobileAbelianBRSTInput period hPeriod configuration plusBase minusBase
        (smoothPairedMobileAbelianBRSTCore period hPeriod configuration
          plusBase minusBase direction nonminimal) =
      smoothPairedVariableMetricAbelianBRSTCore period hPeriod plusBase minusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus)
        (direction.1.completeVariation.fullMetricPerturbation .minus)
        { potential := pairedMobileGaugePotentialAt period hPeriod configuration
            plusBase minusBase direction hDirection
          nonminimal := nonminimal } := by
  simp only [pairedMobileAbelianBRSTInput, smoothPairedMobileAbelianBRSTCore,
    pairedMobileGaugeC2Input_projected period hPeriod configuration
      plusBase minusBase direction hDirection,
    regularGeneralMetricC2PairedPlusGaugeCoefficientInput_projected,
    regularGeneralMetricC2PairedMinusGaugeCoefficientInput_projected,
    smoothPairedVariableMetricAbelianBRSTCore, smoothVariableMetricAbelianBRSTCore,
    smoothAbelianBRSTNonminimalCore]

/-- The complete mobile action uses the actual varied metric in Lorenz and FP. -/
theorem pairedMobileAbelianBRSTAction_projected_eq_BRST
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (nonminimal : Sector → GlobalAbelianNonminimalFields period hPeriod) :
    pairedMobileAbelianBRSTAction period hPeriod configuration plusBase minusBase
        (smoothPairedMobileAbelianBRSTCore period hPeriod configuration
          plusBase minusBase direction nonminimal) =
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod
        (pairedMobileAbelianMetricAt period hPeriod configuration
          plusBase minusBase direction hDirection)
        { potential := pairedMobileGaugePotentialAt period hPeriod configuration
            plusBase minusBase direction hDirection
          nonminimal := nonminimal }
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold pairedMobileAbelianBRSTAction
  rw [pairedMobileAbelianBRSTInput_projected period hPeriod configuration
    plusBase minusBase direction hDirection nonminimal]
  exact pairedVariableMetricAbelianBRSTAction_smooth_eq_BRST period hPeriod
    plusBase minusBase
    (direction.1.completeVariation.fullMetricPerturbation .plus)
    (direction.1.completeVariation.fullMetricPerturbation .minus)
    (pairedMobileAbelianMetricAt period hPeriod configuration
      plusBase minusBase direction hDirection)
    (regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus) hDirection.plus_mem)
    (regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod minusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus) hDirection.minus_mem)
    hDirection.plus_mem.1 hDirection.minus_mem.1 _

/-- SAME-ACTION at the metrics and Maxwell potentials carried by `datumAt`. -/
theorem pairedMobileAbelianBRSTAction_eq_datumAt
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (nonminimal : Sector → GlobalAbelianNonminimalFields period hPeriod) :
    pairedMobileAbelianBRSTAction period hPeriod configuration plusBase minusBase
        (smoothPairedMobileAbelianBRSTCore period hPeriod configuration
          plusBase minusBase direction nonminimal) =
      let datum := (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
        period hPeriod configuration couplings data plusBase minusBase).datumAt
          direction hDirection
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod
        (globalCandidateAMetricBySector period hPeriod datum.2)
        { potential := globalCandidateAPotentialBySector period hPeriod datum.2
          nonminimal := nonminimal }
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact pairedMobileAbelianBRSTAction_projected_eq_BRST period hPeriod configuration
    plusBase minusBase direction hDirection nonminimal

end
end P0EFTJanusPairedMobileAbelianBRSTSameAction4D
end JanusFormal
