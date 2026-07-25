import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLFiniteBVExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothHolonomicDiagonalRealization4D

/-!
# Einstein--Maxwell completion of the coupled Candidate-A/BV action

The two regular Lorentz metrics are tied to the two diagonal metrics already
present in `IndependentFields`.  The intrinsic one-form coefficients and
their variations are likewise tied to the existing gauge slots.  The full
curve is the previous coupled/BV action plus two Einstein--Hilbert and two
Maxwell bulk actions.

The proved derivative concerns directions with fixed metric magnitudes.  In
that sector the Einstein--Hilbert terms are constant and the Maxwell
variation is the genuine derivative of the derived `F = dA` action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusSmoothHolonomicDiagonalRealization4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLFiniteBVExtension4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance localRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance localRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup Real :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module Real Real :=
  localRealNormedSpace.toModule

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Geometric completion of the two metric and gauge sectors. -/
structure CandidateAEinsteinMaxwellCompletion
    (fields : IndependentFields period hPeriod) where
  plusGravity : RegularEinsteinHilbertMetric period hPeriod
  minusGravity : RegularEinsteinHilbertMetric period hPeriod
  plusRealization : SmoothHolonomicDiagonalRealization period hPeriod
    fields.metrics.plusMagnitude fields.metrics.plus_pos
  minusRealization : SmoothHolonomicDiagonalRealization period hPeriod
    fields.metrics.minusMagnitude fields.metrics.minus_pos
  plusMetric_eq :
    plusGravity.metric.metric =
      plusRealization.toSmoothGeneralLorentzMetric period hPeriod
        fields.metrics.plusMagnitude fields.metrics.plus_pos
  minusMetric_eq :
    minusGravity.metric.metric =
      minusRealization.toSmoothGeneralLorentzMetric period hPeriod
        fields.metrics.minusMagnitude fields.metrics.minus_pos
  plusMaxwell :
    RegularIntrinsicMaxwellLine period hPeriod plusGravity.metric
  minusMaxwell :
    RegularIntrinsicMaxwellLine period hPeriod minusGravity.metric
  plusGauge_eq : ∀ point index component,
    plusMaxwell.potential.toFun component point
        (plusGravity.metric.frame index point) =
      fields.gauge.1 point (index, component)
  minusGauge_eq : ∀ point index component,
    minusMaxwell.potential.toFun component point
        (minusGravity.metric.frame index point) =
      fields.gauge.2 point (index, component)

/-- Tangent completion.  Metric magnitudes are fixed on the derivative
theorem below; gauge velocities are exactly those of the intrinsic
one-forms. -/
structure CandidateAEinsteinMaxwellFiniteBVVariation
    (fields : IndependentFields period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    where
  base : CandidateACoupledFiniteBVVariation period hPeriod
  plusMetricDirection_eq_zero :
    base.physical.complete.independent.metrics.plusLogDirection = 0
  minusMetricDirection_eq_zero :
    base.physical.complete.independent.metrics.minusLogDirection = 0
  plusGaugeVariation_eq : ∀ point index component,
    completion.plusMaxwell.variation.toFun component point
        (completion.plusGravity.metric.frame index point) =
      base.physical.complete.independent.gauge.1 point (index, component)
  minusGaugeVariation_eq : ∀ point index component,
    completion.minusMaxwell.variation.toFun component point
        (completion.minusGravity.metric.frame index point) =
      base.physical.complete.independent.gauge.2 point (index, component)

private def maxwellPairingLine
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (parameter : Real) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    data.basePairing point + parameter * data.mixedPairing point +
      parameter ^ 2 * data.variationPairing point
  contMDiff_toFun :=
    data.basePairing.contMDiff_toFun.add
      (contMDiff_const.mul data.mixedPairing.contMDiff_toFun) |>.add
      (contMDiff_const.mul data.variationPairing.contMDiff_toFun)

private theorem maxwellPairingLine_action_hasDerivAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
      (fun parameter =>
        intrinsicMaxwellAction period hPeriod metric
          (maxwellPairingLine period hPeriod metric data parameter) measure)
      (intrinsicMaxwellFirstVariation period hPeriod metric data measure)
      0 := by
  rw [show (fun parameter =>
      intrinsicMaxwellAction period hPeriod metric
        (maxwellPairingLine period hPeriod metric data parameter) measure) =
      fun parameter =>
        intrinsicMaxwellAction period hPeriod metric data.basePairing measure +
          parameter *
            intrinsicMaxwellFirstVariation period hPeriod metric data measure +
          parameter ^ 2 *
            intrinsicMaxwellQuadraticRemainder period hPeriod metric data
              measure by
    funext parameter
    exact intrinsicMaxwellAction_line_expansion period hPeriod metric data
      measure parameter]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (intrinsicMaxwellFirstVariation period hPeriod metric data measure))
      |>.const_add
        (intrinsicMaxwellAction period hPeriod metric data.basePairing measure)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (intrinsicMaxwellQuadraticRemainder period hPeriod metric data measure)
  change HasDerivAt
    ((fun parameter : Real =>
        intrinsicMaxwellAction period hPeriod metric data.basePairing measure +
          parameter *
            intrinsicMaxwellFirstVariation period hPeriod metric data measure) +
      (fun parameter : Real =>
        parameter ^ 2 *
          intrinsicMaxwellQuadraticRemainder period hPeriod metric data
            measure)) _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-- Previous coupled/BV curve plus both genuine gravitational and Maxwell
bulk actions. -/
def candidateACoupledEinsteinMaxwellFiniteBVActionCurve
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction : CandidateAEinsteinMaxwellFiniteBVVariation period hPeriod
      fields completion)
    (parameter : Real) : Real :=
  (((candidateACoupledFiniteBVActionCurve period hPeriod candidateMeasure
          interactionScale coefficients fields matterContract kPlus kMinus
          bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
          direction.base parameter +
        intrinsicEinsteinHilbertAction period hPeriod couplings
          completion.plusGravity candidateMeasure) +
      intrinsicEinsteinHilbertAction period hPeriod couplings
        completion.minusGravity candidateMeasure) +
    intrinsicMaxwellAction period hPeriod completion.plusGravity.metric
      (maxwellPairingLine period hPeriod completion.plusGravity.metric
        completion.plusMaxwell parameter)
      candidateMeasure) +
  intrinsicMaxwellAction period hPeriod completion.minusGravity.metric
    (maxwellPairingLine period hPeriod completion.minusGravity.metric
      completion.minusMaxwell parameter)
    candidateMeasure

/-- First variation in the fixed-metric Einstein--Maxwell/BV sector. -/
def candidateACoupledEinsteinMaxwellFiniteBVEuler
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction : CandidateAEinsteinMaxwellFiniteBVVariation period hPeriod
      fields completion) : Real :=
  candidateACoupledFiniteBVEuler period hPeriod candidateMeasure
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
      direction.base +
    intrinsicMaxwellFirstVariation period hPeriod
      completion.plusGravity.metric completion.plusMaxwell candidateMeasure +
    intrinsicMaxwellFirstVariation period hPeriod
      completion.minusGravity.metric completion.minusMaxwell candidateMeasure

/-- The displayed Euler coefficient is the derivative of the completed
action along every certified fixed-metric direction. -/
theorem candidateACoupledEinsteinMaxwellFiniteBVActionCurve_hasDerivAt
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure candidateMeasure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction : CandidateAEinsteinMaxwellFiniteBVVariation period hPeriod
      fields completion)
    (candidateContract : DominatedCandidateAVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      direction.base.physical.complete.independent.metrics)
    (metricMatterContract : DominatedIndependentMetricMatterVariationContract
      period hPeriod candidateMeasure matterContract.massSquared fields
      direction.base.physical) :
    HasDerivAt
      (candidateACoupledEinsteinMaxwellFiniteBVActionCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        bvField couplings completion direction)
      (candidateACoupledEinsteinMaxwellFiniteBVEuler period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        bvField completion direction)
      0 := by
  have hBase :=
    candidateACoupledFiniteBVActionCurve_hasDerivAt period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      bvField direction.base candidateContract metricMatterContract
  have hPlus :=
    maxwellPairingLine_action_hasDerivAt period hPeriod
      completion.plusGravity.metric completion.plusMaxwell candidateMeasure
  have hMinus :=
    maxwellPairingLine_action_hasDerivAt period hPeriod
      completion.minusGravity.metric completion.minusMaxwell candidateMeasure
  have hTotal :=
    ((((hBase.add_const
        (intrinsicEinsteinHilbertAction period hPeriod couplings
          completion.plusGravity candidateMeasure)).add_const
        (intrinsicEinsteinHilbertAction period hPeriod couplings
          completion.minusGravity candidateMeasure)).add hPlus).add hMinus)
  convert hTotal using 1 <;> rfl

end

end P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
end JanusFormal
