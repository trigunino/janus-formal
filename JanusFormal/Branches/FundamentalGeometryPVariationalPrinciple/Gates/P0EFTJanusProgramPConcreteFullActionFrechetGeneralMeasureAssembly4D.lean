import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteCandidateALineC2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteMatterLineC2Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Realization4D

/-!
# Full concrete Fréchet assembly for a general finite candidate measure

Candidate A is unconditionally `C²` for every finite measure.  Matter and the
four Einstein--Maxwell slots are supplied by their exact non-circular
criteria.  Together with the unconditional Robin, true-LL and finite-BV
blocks this constructs the complete nine-block linewise Fréchet bridge.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteFullActionFrechetGeneralMeasureAssembly4D

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
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
open P0EFTJanusProgramPConcreteCandidateALineC2Closure4D
open P0EFTJanusProgramPConcreteMatterLineC2Closure4D
open P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Closure4D
open P0EFTJanusMappingTorusConcreteEinsteinMaxwellGeneralMeasureC2Realization4D

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

/-- The mixed joint-regularity data are exactly enough to recover the
Einstein--Maxwell criterion used by the finite-measure assembly. -/
def einsteinMaxwellGeneralMeasureC2CriterionOfJointData
    (couplings : EinsteinHilbertCouplings)
    (fields : IndependentFields period hPeriod)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion)
    (data :
      EinsteinMaxwellGeneralMeasureJointC2Data period hPeriod couplings fields
        completion direction) :
    EinsteinMaxwellGeneralMeasureC2Criterion period hPeriod couplings fields
      completion direction :=
  Classical.choice
    ((einsteinMaxwellGeneralMeasureC2Criterion_nonempty_iff period hPeriod
      couplings fields completion direction).2 data)

/-- Exactly the six formerly missing `C²` slots for an arbitrary finite
candidate measure, under the displayed matter and Einstein--Maxwell data. -/
def fullMetricFiniteBVGeneralMeasureMissingC2Slots
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure candidateMeasure]
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
    (matterCriterion :
      ConcreteMatterLineC2Criterion period hPeriod candidateMeasure
        matterContract.massSquared fields direction.base.physical)
    (einsteinMaxwellCriterion :
      EinsteinMaxwellGeneralMeasureC2Criterion period hPeriod couplings fields
        completion direction) :
    FullMetricLineMissingC2Slots period hPeriod candidateMeasure
      interactionScale coefficients fields matterContract kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
      couplings completion direction := by
  let einsteinMaxwell :=
    fullMetricFiniteBVLineBlocks_einsteinMaxwell_contDiff_two period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      bvField couplings completion direction einsteinMaxwellCriterion
  exact
    { candidateA := by
        change ContDiff Real 2
          (candidateAActionCurve period hPeriod candidateMeasure
            interactionScale coefficients fields.metrics
              direction.base.physical.complete.independent.metrics)
        exact candidateAActionCurve_contDiff_two period hPeriod
          candidateMeasure interactionScale coefficients fields.metrics
          direction.base.physical.complete.independent.metrics
      matter :=
        fullMetricFiniteBVLineBlocks_matter_contDiff_two period hPeriod
          candidateMeasure interactionScale coefficients fields matterContract
          kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
          bvField couplings completion direction matterCriterion
      einsteinHilbertPlus := einsteinMaxwell.einsteinHilbertPlus
      einsteinHilbertMinus := einsteinMaxwell.einsteinHilbertMinus
      maxwellPlus := einsteinMaxwell.maxwellPlus
      maxwellMinus := einsteinMaxwell.maxwellMinus }

/-- Complete concrete nine-block Fréchet bridge for every finite candidate
measure satisfying exactly the matter and Einstein--Maxwell criteria above. -/
def fullMetricFiniteBVGeneralMeasureConcreteFrechetBridge
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
    (matterCriterion :
      ConcreteMatterLineC2Criterion period hPeriod candidateMeasure
        matterContract.massSquared fields direction.base.physical)
    (einsteinMaxwellCriterion :
      EinsteinMaxwellGeneralMeasureC2Criterion period hPeriod couplings fields
        completion direction) :
    ConcreteFullActionFrechetBridge Real Real
      (fullMetricFiniteBVAffineActionCurve period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction) :=
  fullMetricFiniteBVLineConcreteFrechetBridge period hPeriod candidateMeasure
    interactionScale coefficients fields matterContract kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure junction bvField couplings completion
    direction
    (fullMetricFiniteBVGeneralMeasureMissingC2Slots period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      bvField couplings completion direction matterCriterion
      einsteinMaxwellCriterion)

end
end P0EFTJanusProgramPConcreteFullActionFrechetGeneralMeasureAssembly4D
end JanusFormal
