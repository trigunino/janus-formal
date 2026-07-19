import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D

/-!
# Candidate-A interaction on the Robin-complete variation

This gate adds the integrated Candidate-A interaction curve to the existing
matter + Robin + true-LL action curve on one and the same
`ProgramPRobinCompleteVariation4D`.  The Candidate-A metric curve is exactly
the metric component of the simultaneous independent-field curve.

The result remains restricted to the fixed-frame diagonal interaction sector.
`MatterMultipletActionData` is still supplied independently and is not yet
canonically reconstructed from `fields.metrics`.  No Einstein--Hilbert,
Maxwell or ghost action, and no Candidate-A Hessian, is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D

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
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D

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

/-- Candidate A uses exactly the metric component of the simultaneous field
curve selected by the same Robin-complete direction. -/
@[simp] theorem metricCurve_robinComplete_eq_independentFieldCurve_metrics
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) :
    metricCurve period hPeriod fields.metrics
        direction.complete.independent.metrics parameter =
      (independentFieldCurve period hPeriod fields
        direction.complete.independent parameter).metrics :=
  rfl

/-- Sum of the diagonal Candidate-A interaction and the existing matter +
Robin + true-LL action along one Robin-complete direction. -/
def candidateARobinCompleteMatterTrueLLActionCurve
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  candidateAActionCurve period hPeriod candidateMeasure interactionScale
      coefficients fields.metrics direction.complete.independent.metrics
      parameter +
    robinCompleteMatterTrueLLActionCurve period hPeriod matterData kPlus
      kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      direction parameter

/-- Sum of the two genuine first-variation coefficients of the action curve
above. -/
def candidateARobinCompleteMatterTrueLLEuler
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  integratedCandidateAFirstVariation period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      direction.complete.independent.metrics +
    robinCompleteMatterTrueLLEuler period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction

/-- Under the actual Candidate-A domination contract and the existing finite
measure assumptions for Robin and LL, the summed Euler coefficient is the
derivative of the summed action on the same Robin-complete direction. -/
theorem candidateARobinCompleteMatterTrueLLAction_hasDerivAt
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterData : MatterMultipletActionData period hPeriod)
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
    (contract : DominatedCandidateAVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      direction.complete.independent.metrics) :
    HasDerivAt
      (candidateARobinCompleteMatterTrueLLActionCurve period hPeriod
        candidateMeasure interactionScale coefficients matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction)
      (candidateARobinCompleteMatterTrueLLEuler period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction direction)
      0 := by
  unfold candidateARobinCompleteMatterTrueLLActionCurve
    candidateARobinCompleteMatterTrueLLEuler
  exact
    (candidateAActionCurve_hasDerivAt period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      direction.complete.independent.metrics contract).add
    (robinCompleteMatterTrueLLAction_hasDerivAt period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields
      junction direction)

end

end P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D
end JanusFormal
