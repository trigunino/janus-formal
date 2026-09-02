import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D

/-!
# Candidate-A action data on the paired regular metric chart

The explicit face and scalar boundary controls are transported to the paired
configuration.  The gravity, Maxwell, gauge and interaction fields from the
preceding paired gates then assemble one complete `GlobalCandidateAActionData`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartActionData4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartConfiguration4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Reindex explicit boundary controls along a configuration replacement.
The later LL realization reads the target configuration, while the supplied
face strata and scalar boundary condition remain unchanged. -/
def rebaseGlobalBoundaryVariationData
    {source target : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod source
      NonNullFace NullFace) :
    GlobalBoundaryVariationData period hPeriod target
      NonNullFace NullFace where
  nonNullWeight := data.nonNullWeight
  nonNullEinsteinScale := data.nonNullEinsteinScale
  nonNullOrientation := data.nonNullOrientation
  nonNullDirichletJet := data.nonNullDirichletJet
  nullFaces := data.nullFaces
  scalarMassSquared := data.scalarMassSquared
  scalarField := data.scalarField
  scalarTest := data.scalarTest
  scalarControl := data.scalarControl

@[simp]
theorem rebaseGlobalBoundaryVariationData_nullFaces
    {source target : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod source
      NonNullFace NullFace) :
    (rebaseGlobalBoundaryVariationData period hPeriod
      (target := target) data).nullFaces = data.nullFaces :=
  rfl

@[simp]
theorem rebaseGlobalBoundaryVariationData_nonNullFaces
    {source target : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod source
      NonNullFace NullFace) :
    (rebaseGlobalBoundaryVariationData period hPeriod
      (target := target) data).nonNullFaces period hPeriod =
        data.nonNullFaces period hPeriod :=
  rfl

/-- Complete action package at one admissible paired metric/gauge point.
Boundary strata are inherited from the supplied base package and rebound to
the new configuration; all varied bulk fields are reconstructed exactly. -/
def regularGeneralMetricC2PairedLorentzChartActionData
    (configuration : GlobalFieldConfiguration period hPeriod)
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
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalCandidateAActionData period hPeriod
      (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
        configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential)
      couplings NonNullFace NullFace where
  plusGravity := regularGeneralMetricC2PairedPlusGravity period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  minusGravity := regularGeneralMetricC2PairedMinusGravity period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  plusMetric_eq :=
    regularGeneralMetricC2PairedPlusGravity_metric_eq_geometry period hPeriod
      plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  minusMetric_eq :=
    regularGeneralMetricC2PairedMinusGravity_metric_eq_geometry period hPeriod
      plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
  plusMaxwell := regularGeneralMetricC2PairedPlusMaxwell period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
      (potential .plus) (variation .plus)
  minusMaxwell := regularGeneralMetricC2PairedMinusMaxwell period hPeriod
    plusBase minusBase plusMetricVariation minusMetricVariation hAdmissible
      (potential .minus) (variation .minus)
  plusGauge_eq :=
    regularGeneralMetricC2PairedLorentzChartConfiguration_plusGauge_eq
      period hPeriod configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential variation
  minusGauge_eq :=
    regularGeneralMetricC2PairedLorentzChartConfiguration_minusGauge_eq
      period hPeriod configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential variation
  interactionDensity := regularGeneralMetricC2PairedInteractionDensity
    period hPeriod plusBase minusBase plusMetricVariation minusMetricVariation
      hAdmissible couplings.interactionScale couplings.interactionCoefficients
  interactionDensity_eq :=
    regularGeneralMetricC2PairedInteractionDensity_eq period hPeriod
      configuration plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential couplings.interactionScale
          couplings.interactionCoefficients
  boundary := rebaseGlobalBoundaryVariationData period hPeriod data.boundary
  nonNullBoundary := data.nonNullBoundary
  nullActionFaces := data.nullActionFaces
  nullActionGenerator_eq := data.nullActionGenerator_eq
  nullActionInterval_eq := data.nullActionInterval_eq

@[simp]
theorem regularGeneralMetricC2PairedLorentzChartActionData_plusGravity
    (configuration : GlobalFieldConfiguration period hPeriod)
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
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    (regularGeneralMetricC2PairedLorentzChartActionData period hPeriod
      configuration couplings data plusBase minusBase plusMetricVariation
        minusMetricVariation hAdmissible potential variation).plusGravity =
      regularGeneralMetricC2PairedPlusGravity period hPeriod plusBase
        minusBase plusMetricVariation minusMetricVariation hAdmissible :=
  rfl

/-- Gate marker: every supplied base boundary package extends to a complete
paired Candidate-A action datum. -/
theorem regular_general_metric_c2_paired_lorentz_chart_action_data_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
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
    (potential variation :
      Sector → SmoothAbelianGaugePotential period hPeriod) :
    Nonempty
      (GlobalCandidateAActionData period hPeriod
        (regularGeneralMetricC2PairedLorentzChartConfiguration period hPeriod
          configuration plusBase minusBase plusMetricVariation
          minusMetricVariation hAdmissible potential)
        couplings NonNullFace NullFace) :=
  ⟨regularGeneralMetricC2PairedLorentzChartActionData period hPeriod
    configuration couplings data plusBase minusBase plusMetricVariation
      minusMetricVariation hAdmissible potential variation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartActionData4D
end JanusFormal
