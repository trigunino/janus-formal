import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongFullBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileDiffeomorphismBRSTSmoothAgreement4D

/-! # Full BRST SAME-ACTION on the original physical family

Both BRST summands use the metrics of the original family's actual datum. The
diffeomorphism perturbation is its existing physical metric direction; the
family's two base metrics remain the fixed gauge background. All nonminimal
fields are independent and shared geometric diffeomorphism fields are retained.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongFullBRSTSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusPairedMobileAbelianBRSTSameAction4D
open P0EFTJanusPairedStrongAbelianGaugeFixedAction4D
open P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D
open P0EFTJanusPairedMobileDiffeomorphismBRSTSmoothAgreement4D
open P0EFTJanusPairedStrongFullBRSTAction4D

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
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
    period hPeriod plusBase minusBase)
  (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
  (source : RegularGeneralLorentzMetric period hPeriod)

local notation "Core" => PairedStrongFullBRSTCore period hPeriod configuration
  data analysis realization plusBase minusBase hBase measure

/-- Only independent nonminimal coordinates are added to the original physical direction. -/
def smoothPairedStrongFullBRSTCore
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (abelian : Sector → GlobalAbelianNonminimalFields period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) : Core :=
  ((direction, (smoothAbelianBRSTNonminimalCore period hPeriod (abelian .plus),
      smoothAbelianBRSTNonminimalCore period hPeriod (abelian .minus))),
    smoothDiffeomorphismNonminimalC2Core period hPeriod source diffeomorphism)

theorem pairedStrongFullDiffeomorphismProjection_smooth
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (abelian : Sector → GlobalAbelianNonminimalFields period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    pairedStrongFullDiffeomorphismProjection period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure
        (smoothPairedStrongFullBRSTCore period hPeriod configuration data analysis realization
          plusBase minusBase hBase measure source direction abelian diffeomorphism) =
      smoothPairedMobileDiffeomorphismBRSTCore period hPeriod source plusBase minusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus)
        (direction.1.completeVariation.fullMetricPerturbation .minus) diffeomorphism := by
  rw [pairedStrongFullDiffeomorphismProjection_apply,
    pairedStrongAbelianBRSTProjection_apply]
  rfl

theorem smoothPairedStrongFullBRSTCore_mem_domain
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (abelian : Sector → GlobalAbelianNonminimalFields period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    smoothPairedStrongFullBRSTCore period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure source direction abelian diffeomorphism ∈
      pairedStrongFullBRSTDomain period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure :=
  ⟨⟨hDirection, mem_univ _⟩, mem_univ _⟩

/-- The diffeomorphism action uses the actual datum metric and its physical perturbation. -/
theorem pairedStrongFullDiffeomorphismAction_smooth_eq_datumAt
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (abelian : Sector → GlobalAbelianNonminimalFields period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    let datum := (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
        direction hDirection
    pairedMobileDiffeomorphismBRSTAction period hPeriod source plusBase minusBase couplings
        (pairedStrongFullDiffeomorphismProjection period hPeriod configuration data analysis realization
          plusBase minusBase hBase measure
          (smoothPairedStrongFullBRSTCore period hPeriod configuration data analysis realization
            plusBase minusBase hBase measure source direction abelian diffeomorphism)) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings
        (globalCandidateAMetricBySector period hPeriod datum.2)
        { metricPerturbation := direction.1.completeVariation.fullMetricPerturbation
          nonminimal := diffeomorphism } := by
  dsimp only
  rw [pairedStrongFullDiffeomorphismProjection_smooth]
  have h := pairedMobileDiffeomorphismBRSTAction_smooth_eq_BRST period hPeriod
    source plusBase minusBase couplings
    (direction.1.completeVariation.fullMetricPerturbation .plus)
    (direction.1.completeVariation.fullMetricPerturbation .minus)
    (pairedMobileAbelianMetricAt period hPeriod configuration.physical
      plusBase minusBase direction hDirection)
    (regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus) hDirection.plus_mem)
    (regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod minusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus) hDirection.minus_mem)
    hDirection.plus_mem.1 hDirection.minus_mem.1 diffeomorphism
  have hPerturbation :
      (fun | .plus => direction.1.completeVariation.fullMetricPerturbation .plus
           | .minus => direction.1.completeVariation.fullMetricPerturbation .minus) =
        direction.1.completeVariation.fullMetricPerturbation := by
    funext sector
    cases sector <;> rfl
  have hState := congrArg (fun perturbation =>
    ({ metricPerturbation := perturbation, nonminimal := diffeomorphism } :
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)) hPerturbation
  have hAction := congrArg
    (globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings
      (pairedMobileAbelianMetricAt period hPeriod configuration.physical
        plusBase minusBase direction hDirection)) hState
  exact h.trans hAction

/-- SAME-ACTION at the original family's actual datum, with both complete BRST sectors. -/
theorem pairedStrongFullBRSTAction_smooth_eq_CandidateA
    (hMeasure : measure = intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (abelian : Sector → GlobalAbelianNonminimalFields period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    let datum := (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration.physical couplings data plusBase minusBase).datumAt
        direction hDirection
    pairedStrongFullBRSTAction period hPeriod configuration data analysis realization
        plusBase minusBase hBase measure source
        (smoothPairedStrongFullBRSTCore period hPeriod configuration data analysis realization
          plusBase minusBase hBase measure source direction abelian diffeomorphism) =
      globalCandidateAAbelianGaugeFixedAction period hPeriod
          { physical := datum.1
            nonminimal := { configuration.nonminimal with abelian := abelian } }
          datum.2 measure +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings
          (globalCandidateAMetricBySector period hPeriod datum.2)
          { metricPerturbation := direction.1.completeVariation.fullMetricPerturbation
            nonminimal := diffeomorphism } := by
  have hAbelian := pairedStrongAbelianGaugeFixedAction_smooth_eq_CandidateA period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure
    hMeasure direction hDirection abelian
  have hDiffeomorphism := pairedStrongFullDiffeomorphismAction_smooth_eq_datumAt period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure source
    direction hDirection abelian diffeomorphism
  exact congrArg₂ (fun first second : Real => first + second) hAbelian hDiffeomorphism

end
end P0EFTJanusPairedStrongFullBRSTSmoothAgreement4D
end JanusFormal
