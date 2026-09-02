import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D

/-!
# Paired local datum along the minimal physical tangent

The paired metric chart is evaluated on the genuine metric slot of a minimal
physical direction.  All target fields are installed by
`globalMinimalPhysicalConfigurationAt`; both the state gauge potentials and
their Maxwell variations are reconstructed intrinsically from the matching
regular-frame coefficient fields.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The exact target configuration obtained by translating every minimal
physical field and installing the paired geometry from its metric slot. -/
def regularGeneralMetricC2PairedMinimalPhysicalTarget
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    GlobalFieldConfiguration period hPeriod :=
  globalMinimalPhysicalConfigurationAt period hPeriod configuration
    (globalMetricPerturbationPairLorentzChartGeometry period hPeriod plusBase
      minusBase direction.1.completeVariation.fullMetricPerturbation
        hAdmissible) direction

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalTarget_geometry
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    (regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
      configuration plusBase minusBase direction hAdmissible).geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod plusBase
        minusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus)
        (direction.1.completeVariation.fullMetricPerturbation .minus)
        hAdmissible :=
  rfl

/-- Intrinsic Maxwell direction reconstructed from the gauge slot of the same
minimal physical tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalGaugeVariation
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    Sector → SmoothAbelianGaugePotential period hPeriod
  | .plus =>
      regularFrameGaugePotentialFromCoefficients period hPeriod
        (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
          minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)
          hAdmissible).metric
        direction.1.completeVariation.independent.gauge.1
  | .minus =>
      regularFrameGaugePotentialFromCoefficients period hPeriod
        (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
          minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)
          hAdmissible).metric
        direction.1.completeVariation.independent.gauge.2

/-- Exact local Candidate-A datum at one admissible minimal physical
direction.  Unlike Gate 355, its first projection retains every translated
gauge, LL and SpinC field of that direction. -/
def regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace :=
  regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod
    configuration
    (regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
      configuration plusBase minusBase direction hAdmissible)
    couplings data plusBase minusBase
    (direction.1.completeVariation.fullMetricPerturbation .plus)
    (direction.1.completeVariation.fullMetricPerturbation .minus)
    hAdmissible rfl
    (regularGeneralMetricC2PairedMinimalPhysicalGaugeVariation period hPeriod
      configuration plusBase minusBase direction hAdmissible)

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum_configuration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    (regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum period hPeriod
      configuration couplings data plusBase minusBase direction
        hAdmissible).1 =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration plusBase minusBase direction hAdmissible :=
  rfl

/-- Gate marker: every admissible minimal physical direction now supplies an
exact local datum on its fully translated target configuration. -/
theorem regular_general_metric_c2_paired_minimal_physical_local_action_datum_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation) :
    Nonempty (GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace) :=
  ⟨regularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum period hPeriod
    configuration couplings data plusBase minusBase direction hAdmissible⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
end JanusFormal
