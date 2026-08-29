import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D

/-!
# Full-metric Einstein--Maxwell completion of the coupled Candidate-A/BV action

The two Einstein--Hilbert metric lines are tied at every parameter to the
existing positive diagonal metric curve.  The two gauge-potential lines are
tied at every parameter to the existing affine gauge curve.  Consequently
the metric directions are unrestricted; the earlier fixed-metric theorem is
only a special sector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusSmoothHolonomicDiagonalRealization4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D
open P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLFiniteBVExtension4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
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
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
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

/-- A full geometric lift of one coupled/BV direction.  Every metric and
gauge object is tied to the pre-existing Program-P field curve. -/
structure CandidateAEinsteinMaxwellFullMetricFiniteBVVariation
    (fields : IndependentFields period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    where
  base : CandidateACoupledFiniteBVVariation period hPeriod
  plusGravityLine :
    RegularEinsteinHilbertMetricLine period hPeriod
  minusGravityLine :
    RegularEinsteinHilbertMetricLine period hPeriod
  plusGravity_zero : plusGravityLine.data 0 = completion.plusGravity
  minusGravity_zero : minusGravityLine.data 0 = completion.minusGravity
  plusRealization : ∀ parameter,
    SmoothHolonomicDiagonalRealization period hPeriod
      (metricCurve period hPeriod fields.metrics
        base.physical.complete.independent.metrics parameter).plusMagnitude
      (metricCurve period hPeriod fields.metrics
        base.physical.complete.independent.metrics parameter).plus_pos
  minusRealization : ∀ parameter,
    SmoothHolonomicDiagonalRealization period hPeriod
      (metricCurve period hPeriod fields.metrics
        base.physical.complete.independent.metrics parameter).minusMagnitude
      (metricCurve period hPeriod fields.metrics
        base.physical.complete.independent.metrics parameter).minus_pos
  plusMetric_eq : ∀ parameter,
    (plusGravityLine.data parameter).metric.metric =
      (plusRealization parameter).toSmoothGeneralLorentzMetric period hPeriod
        (metricCurve period hPeriod fields.metrics
          base.physical.complete.independent.metrics parameter).plusMagnitude
        (metricCurve period hPeriod fields.metrics
          base.physical.complete.independent.metrics parameter).plus_pos
  minusMetric_eq : ∀ parameter,
    (minusGravityLine.data parameter).metric.metric =
      (minusRealization parameter).toSmoothGeneralLorentzMetric period hPeriod
        (metricCurve period hPeriod fields.metrics
          base.physical.complete.independent.metrics parameter).minusMagnitude
        (metricCurve period hPeriod fields.metrics
          base.physical.complete.independent.metrics parameter).minus_pos
  plusMaxwellLine :
    RegularIntrinsicMaxwellMetricGaugeLine period hPeriod plusGravityLine
  minusMaxwellLine :
    RegularIntrinsicMaxwellMetricGaugeLine period hPeriod minusGravityLine
  plusPotential_zero :
    plusMaxwellLine.potential 0 = completion.plusMaxwell.potential
  minusPotential_zero :
    minusMaxwellLine.potential 0 = completion.minusMaxwell.potential
  plusPairing_zero :
    plusMaxwellLine.pairing 0 = completion.plusMaxwell.basePairing
  minusPairing_zero :
    minusMaxwellLine.pairing 0 = completion.minusMaxwell.basePairing
  plusGauge_eq : ∀ parameter point index component,
    (plusMaxwellLine.potential parameter).toFun component point
        ((plusGravityLine.data parameter).metric.frame index point) =
      (independentFieldCurve period hPeriod fields
        base.physical.complete.independent parameter).gauge.1
          point (index, component)
  minusGauge_eq : ∀ parameter point index component,
    (minusMaxwellLine.potential parameter).toFun component point
        ((minusGravityLine.data parameter).metric.frame index point) =
      (independentFieldCurve period hPeriod fields
        base.physical.complete.independent parameter).gauge.2
          point (index, component)

/-- Coupled/BV action with both EH and Maxwell sectors evaluated on the same
unrestricted metric and gauge curves as the existing physical action. -/
def candidateACoupledEinsteinMaxwellFullMetricFiniteBVActionCurve
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
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion)
    (parameter : Real) : Real :=
  ((((candidateACoupledFiniteBVActionCurve period hPeriod candidateMeasure
          interactionScale coefficients fields matterContract kPlus kMinus
          bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
          direction.base parameter +
        intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
          direction.plusGravityLine candidateMeasure parameter) +
      intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
        direction.minusGravityLine candidateMeasure parameter) +
    intrinsicMaxwellMetricGaugeActionCurve period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine candidateMeasure
      parameter) +
  intrinsicMaxwellMetricGaugeActionCurve period hPeriod
    direction.minusGravityLine direction.minusMaxwellLine candidateMeasure
    parameter)

/-- Exact integrated first variation of the unrestricted coupled action. -/
def candidateACoupledEinsteinMaxwellFullMetricFiniteBVEuler
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
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion) : Real :=
  ((((candidateACoupledFiniteBVEuler period hPeriod candidateMeasure
          interactionScale coefficients fields matterContract kPlus kMinus
          bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
          direction.base +
        intrinsicEinsteinHilbertMetricFirstVariation period hPeriod couplings
          direction.plusGravityLine candidateMeasure) +
      intrinsicEinsteinHilbertMetricFirstVariation period hPeriod couplings
        direction.minusGravityLine candidateMeasure) +
    intrinsicMaxwellMetricGaugeFirstVariation period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine candidateMeasure) +
  intrinsicMaxwellMetricGaugeFirstVariation period hPeriod
    direction.minusGravityLine direction.minusMaxwellLine candidateMeasure)

/-- No metric direction is set to zero: the derivative theorem follows from
the actual EH and Maxwell density derivatives on the common Program-P line. -/
theorem candidateACoupledEinsteinMaxwellFullMetricFiniteBVActionCurve_hasDerivAt
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
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion)
    (candidateContract : DominatedCandidateAVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      direction.base.physical.complete.independent.metrics)
    (metricMatterContract : DominatedIndependentMetricMatterVariationContract
      period hPeriod candidateMeasure matterContract.massSquared fields
      direction.base.physical)
    (plusGravityContract : DominatedEinsteinHilbertMetricVariation
      period hPeriod couplings direction.plusGravityLine candidateMeasure)
    (minusGravityContract : DominatedEinsteinHilbertMetricVariation
      period hPeriod couplings direction.minusGravityLine candidateMeasure)
    (plusMaxwellContract : DominatedMaxwellMetricGaugeVariation
      period hPeriod direction.plusGravityLine direction.plusMaxwellLine
        candidateMeasure)
    (minusMaxwellContract : DominatedMaxwellMetricGaugeVariation
      period hPeriod direction.minusGravityLine direction.minusMaxwellLine
        candidateMeasure) :
    HasDerivAt
      (candidateACoupledEinsteinMaxwellFullMetricFiniteBVActionCurve
        period hPeriod candidateMeasure interactionScale coefficients fields
        matterContract kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure junction bvField couplings completion direction)
      (candidateACoupledEinsteinMaxwellFullMetricFiniteBVEuler
        period hPeriod candidateMeasure interactionScale coefficients fields
        matterContract kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure junction bvField couplings completion direction)
      0 := by
  have hBase :=
    candidateACoupledFiniteBVActionCurve_hasDerivAt period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      bvField direction.base candidateContract metricMatterContract
  have hPlusGravity :=
    intrinsicEinsteinHilbertMetricActionCurve_hasDerivAt period hPeriod
      couplings direction.plusGravityLine candidateMeasure plusGravityContract
  have hMinusGravity :=
    intrinsicEinsteinHilbertMetricActionCurve_hasDerivAt period hPeriod
      couplings direction.minusGravityLine candidateMeasure minusGravityContract
  have hPlusMaxwell :=
    intrinsicMaxwellMetricGaugeActionCurve_hasDerivAt period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine candidateMeasure
      plusMaxwellContract
  have hMinusMaxwell :=
    intrinsicMaxwellMetricGaugeActionCurve_hasDerivAt period hPeriod
      direction.minusGravityLine direction.minusMaxwellLine candidateMeasure
      minusMaxwellContract
  have hTotal :=
    ((((hBase.add hPlusGravity).add hMinusGravity).add hPlusMaxwell).add
      hMinusMaxwell)
  convert hTotal using 1 <;> rfl

end

end P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
end JanusFormal
