import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

/-!
# Target configuration datum on the paired regular metric chart

An arbitrary configuration carrying the paired geometry is no longer required
to have preselected intrinsic gauge potentials.  The inverse regular-frame
map reconstructs them from its two gauge coefficient fields, after which the
complete Candidate-A action datum is assembled directly on that target.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartActionData4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Intrinsic potentials reconstructed from the two gauge coefficient fields
of an arbitrary target configuration. -/
def regularGeneralMetricC2PairedTargetGaugePotential
    (target : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation) :
    Sector → SmoothAbelianGaugePotential period hPeriod
  | .plus =>
      regularFrameGaugePotentialFromCoefficients period hPeriod
        (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
          minusBase plusMetricVariation minusMetricVariation
          hAdmissible).metric target.coefficientFields.gauge.1
  | .minus =>
      regularFrameGaugePotentialFromCoefficients period hPeriod
        (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
          minusBase plusMetricVariation minusMetricVariation
          hAdmissible).metric target.coefficientFields.gauge.2

@[simp]
theorem regularGeneralMetricC2PairedTargetGaugePotential_plus_coefficients
    (target : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation) :
    gaugePotentialFrameCoefficients period hPeriod
        (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
          minusBase plusMetricVariation minusMetricVariation
          hAdmissible).metric
        (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod target
          plusBase minusBase plusMetricVariation minusMetricVariation
          hAdmissible .plus) =
      target.coefficientFields.gauge.1 := by
  exact gaugePotentialFrameCoefficients_reconstructed period hPeriod _ _

@[simp]
theorem regularGeneralMetricC2PairedTargetGaugePotential_minus_coefficients
    (target : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation) :
    gaugePotentialFrameCoefficients period hPeriod
        (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
          minusBase plusMetricVariation minusMetricVariation
          hAdmissible).metric
        (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod target
          plusBase minusBase plusMetricVariation minusMetricVariation
          hAdmissible .minus) =
      target.coefficientFields.gauge.2 := by
  exact gaugePotentialFrameCoefficients_reconstructed period hPeriod _ _

/-- Complete Candidate-A action data directly indexed by an arbitrary target
whose geometry is the paired chart geometry. -/
def regularGeneralMetricC2PairedTargetActionData
    (configuration target : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (hTargetGeometry : target.geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
        plusBase minusBase plusMetricVariation minusMetricVariation
        hAdmissible)
    (variation : Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalCandidateAActionData period hPeriod target couplings
      NonNullFace NullFace where
  plusGravity := regularGeneralMetricC2PairedPlusGravity period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  minusGravity := regularGeneralMetricC2PairedMinusGravity period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  plusMetric_eq := by
    rw [hTargetGeometry]
    exact regularGeneralMetricC2PairedPlusGravity_metric_eq_geometry
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible
  minusMetric_eq := by
    rw [hTargetGeometry]
    exact regularGeneralMetricC2PairedMinusGravity_metric_eq_geometry
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible
  plusMaxwell := regularGeneralMetricC2PairedPlusMaxwell period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
      (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod target
        plusBase minusBase plusMetricVariation minusMetricVariation
        hAdmissible .plus) (variation .plus)
  minusMaxwell := regularGeneralMetricC2PairedMinusMaxwell period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
      (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod target
        plusBase minusBase plusMetricVariation minusMetricVariation
        hAdmissible .minus) (variation .minus)
  plusGauge_eq := by
    intro point index component
    calc
      _ = gaugePotentialFrameCoefficients period hPeriod
          (regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric
          (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod
            target plusBase minusBase plusMetricVariation
              minusMetricVariation hAdmissible .plus) point
          (index, component) :=
        regularGeneralMetricC2PairedPlusMaxwell_gaugeCoefficient period hPeriod
          plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible _ _ point index component
      _ = target.coefficientFields.gauge.1 point (index, component) := by
        rw [regularGeneralMetricC2PairedTargetGaugePotential_plus_coefficients]
  minusGauge_eq := by
    intro point index component
    calc
      _ = gaugePotentialFrameCoefficients period hPeriod
          (regularGeneralMetricC2PairedMinusGravity period hPeriod plusBase
            minusBase plusMetricVariation minusMetricVariation
            hAdmissible).metric
          (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod
            target plusBase minusBase plusMetricVariation
              minusMetricVariation hAdmissible .minus) point
          (index, component) :=
        regularGeneralMetricC2PairedMinusMaxwell_gaugeCoefficient period hPeriod
          plusBase minusBase plusMetricVariation minusMetricVariation
            hAdmissible _ _ point index component
      _ = target.coefficientFields.gauge.2 point (index, component) := by
        rw [regularGeneralMetricC2PairedTargetGaugePotential_minus_coefficients]
  interactionDensity := regularGeneralMetricC2PairedInteractionDensity
    period hPeriod plusBase minusBase plusMetricVariation minusMetricVariation
      hAdmissible couplings.interactionScale couplings.interactionCoefficients
  interactionDensity_eq := by
    intro point
    rw [hTargetGeometry]
    simpa only [regularGeneralMetricC2PairedLorentzChartConfiguration_geometry]
      using regularGeneralMetricC2PairedInteractionDensity_eq period hPeriod
        configuration plusBase minusBase plusMetricVariation
          minusMetricVariation hAdmissible
          (regularGeneralMetricC2PairedTargetGaugePotential period hPeriod
            target plusBase minusBase plusMetricVariation
              minusMetricVariation hAdmissible)
          couplings.interactionScale couplings.interactionCoefficients point
  boundary := rebaseGlobalBoundaryVariationData period hPeriod
    (target := target) data.boundary
  nonNullBoundary := data.nonNullBoundary
  nullActionFaces := data.nullActionFaces
  nullActionGenerator_eq := data.nullActionGenerator_eq
  nullActionInterval_eq := data.nullActionInterval_eq

/-- The arbitrary target and its reconstructed action package as the exact
dependent local datum. -/
def regularGeneralMetricC2PairedTargetLocalActionDatum
    (configuration target : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (hTargetGeometry : target.geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
        plusBase minusBase plusMetricVariation minusMetricVariation
        hAdmissible)
    (variation : Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace :=
  ⟨target, regularGeneralMetricC2PairedTargetActionData period hPeriod
    configuration target couplings data plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible hTargetGeometry
        variation⟩

@[simp]
theorem regularGeneralMetricC2PairedTargetLocalActionDatum_configuration
    (configuration target : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (hTargetGeometry : target.geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
        plusBase minusBase plusMetricVariation minusMetricVariation
        hAdmissible)
    (variation : Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod
      configuration target couplings data plusBase minusBase
        plusMetricVariation minusMetricVariation hAdmissible hTargetGeometry
          variation).1 = target :=
  rfl

/-- Gate marker: every target with the paired geometry has an exact local
datum, with no representability hypothesis on its gauge coefficients. -/
theorem regular_general_metric_c2_paired_target_local_action_datum_gate
    (configuration target : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusMetricVariation minusMetricVariation :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible
      period hPeriod plusBase minusBase plusMetricVariation
        minusMetricVariation)
    (hTargetGeometry : target.geometry =
      regularGeneralMetricC2PairedLorentzChartGeometry period hPeriod
        plusBase minusBase plusMetricVariation minusMetricVariation
        hAdmissible)
    (variation : Sector → SmoothAbelianGaugePotential period hPeriod) :
    Nonempty (GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace) :=
  ⟨regularGeneralMetricC2PairedTargetLocalActionDatum period hPeriod
    configuration target couplings data plusBase minusBase
      plusMetricVariation minusMetricVariation hAdmissible hTargetGeometry
        variation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D
end JanusFormal
