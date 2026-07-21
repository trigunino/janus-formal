import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentMatterMetricActionData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D

/-!
# Sector-metric specialization of the Candidate-A and matter action

This gate specializes the combined Candidate-A + matter + Robin + true-LL
action to the existing `independentMatterMetricActionData`.  Every matter
component therefore uses the plus or minus magnitude selected by its actual
sector from the same base `IndependentFields.metrics`, and its measure is
literally the Candidate-A integration measure.

The matter masses and the required pairing integrability remain explicit
analytic inputs.  Moreover, the selected matter magnitudes are fixed at the
base configuration along the current matter affine curve; this does not yet
derive metric--matter cross-variation.  Candidate A is still diagonal, and no
Einstein--Hilbert, Maxwell, ghost or Candidate-A Hessian term is added.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateASectorMetricMatterRobinTrueLLAction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

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
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The combined action with matter data constructed from the same base
metrics and the same quotient measure as Candidate A. -/
def candidateASectorMetricMatterRobinTrueLLActionCurve
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (parameter : Real) : Real :=
  candidateARobinCompleteMatterTrueLLActionCurve period hPeriod
    candidateMeasure interactionScale coefficients
    (independentMatterMetricActionData period hPeriod fields candidateMeasure
      matterContract)
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    direction parameter

/-- The corresponding Euler coefficient with the same sector-selected matter
data. -/
def candidateASectorMetricMatterRobinTrueLLEuler
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure) : Real :=
  candidateARobinCompleteMatterTrueLLEuler period hPeriod candidateMeasure
    interactionScale coefficients
    (independentMatterMetricActionData period hPeriod fields candidateMeasure
      matterContract)
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    direction

/-- The specialization is definitionally the previously proved combined
action with the sector-metric matter constructor inserted. -/
@[simp] theorem candidateASectorMetricMatterRobinTrueLLActionCurve_eq
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure) :
    candidateASectorMetricMatterRobinTrueLLActionCurve period hPeriod
        candidateMeasure interactionScale coefficients kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction
        matterContract =
      candidateARobinCompleteMatterTrueLLActionCurve period hPeriod
        candidateMeasure interactionScale coefficients
        (independentMatterMetricActionData period hPeriod fields
          candidateMeasure matterContract)
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields
        junction direction :=
  rfl

/-- The specialized derivative is inherited without weakening either the
Candidate-A domination contract or the Robin/LL finite-measure assumptions. -/
theorem candidateASectorMetricMatterRobinTrueLLAction_hasDerivAt
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (candidateContract : DominatedCandidateAVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      direction.complete.independent.metrics) :
    HasDerivAt
      (candidateASectorMetricMatterRobinTrueLLActionCurve period hPeriod
        candidateMeasure interactionScale coefficients kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction
        matterContract)
      (candidateASectorMetricMatterRobinTrueLLEuler period hPeriod
        candidateMeasure interactionScale coefficients kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction
        matterContract)
      0 := by
  unfold candidateASectorMetricMatterRobinTrueLLActionCurve
    candidateASectorMetricMatterRobinTrueLLEuler
  exact candidateARobinCompleteMatterTrueLLAction_hasDerivAt period hPeriod
    candidateMeasure interactionScale coefficients
    (independentMatterMetricActionData period hPeriod fields candidateMeasure
      matterContract)
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    direction candidateContract

end

end P0EFTJanusMappingTorusCandidateASectorMetricMatterRobinTrueLLAction4D
end JanusFormal
