import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAPartialSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D

/-!
# Candidate A with coupled metric--matter variation

This gate removes the frozen-metric limitation of the earlier sector action.
Candidate A and all eight scalar matter components now use the metric carried
by the same `IndependentFields` curve.  Robin and the true three-slot LL action
remain on the same Robin-complete direction.

The first derivative is the sum of the genuine Candidate-A, coupled
metric--matter, Robin and LL derivatives.  The already proved iterated
metric--matter derivative is then inserted in both symmetric cross slots of
the sectorial Hessian.

The pure metric--metric second derivative of the matter action is included in
the final completed sectorial Hessian.  The true LL term already varies its
auxiliary metric and measure.  Einstein--Hilbert, Maxwell, ghost and non-LL
auxiliary actions are not added here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D
open P0EFTJanusMappingTorusCandidateAPartialSameActionHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusTruePTFullLLFirstVariationBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

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

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Candidate A, the eight scalar matter fields, Robin and true LL evaluated
on one coupled Robin-complete curve. -/
def candidateACoupledMetricMatterRobinTrueLLActionCurve
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
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  candidateAActionCurve period hPeriod candidateMeasure interactionScale
      coefficients fields.metrics direction.complete.independent.metrics
      parameter +
    programPMetricMatterActionCurve period hPeriod candidateMeasure
      matterContract.massSquared fields direction parameter +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
      (junctionAffineCurve period hPeriod junction direction.robin parameter)
      robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame
      (differentialLLFullCurve period hPeriod fields
        (toFullMatterRobinLLDirections period hPeriod direction).llAuxMetric
        (toFullMatterRobinLLDirections period hPeriod direction).llMeasure
        (toFullMatterRobinLLDirections period hPeriod direction).common.ll
        parameter)
      llMeasure

/-- Genuine first-variation coefficient of the coupled sector action. -/
def candidateACoupledMetricMatterRobinTrueLLEuler
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
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  integratedCandidateAFirstVariation period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      direction.complete.independent.metrics +
    integratedIndependentMetricMatterFirstVariation period hPeriod
      candidateMeasure matterContract.massSquared fields direction +
    robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      direction.robin robinMeasure +
    globalPTFullLLFirstVariation period hPeriod frame fields
      (toFullMatterRobinLLDirections period hPeriod direction) llMeasure

/-- The coupled Euler coefficient is the derivative of one action curve. -/
theorem candidateACoupledMetricMatterRobinTrueLLAction_hasDerivAt
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
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
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (candidateContract : DominatedCandidateAVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      direction.complete.independent.metrics)
    (metricMatterContract : DominatedIndependentMetricMatterVariationContract
      period hPeriod candidateMeasure matterContract.massSquared fields
      direction) :
    HasDerivAt
      (candidateACoupledMetricMatterRobinTrueLLActionCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        direction)
      (candidateACoupledMetricMatterRobinTrueLLEuler period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        direction)
      0 := by
  have hCandidate :=
    candidateAActionCurve_hasDerivAt period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      direction.complete.independent.metrics candidateContract
  have hMatter :=
    programPMetricMatterActionCurve_hasDerivAt period hPeriod candidateMeasure
      matterContract.massSquared fields direction metricMatterContract
  have hRobin :=
    robinJunctionAction_affine_hasDerivAt period hPeriod kPlus kMinus bulkPlus
      bulkMinus junction direction.robin robinMeasure
  have hLL :=
    truePTAction_fullCurve_hasDerivAt_fullFirstVariation period hPeriod frame
      fields (toFullMatterRobinLLDirections period hPeriod direction) llMeasure
  unfold candidateACoupledMetricMatterRobinTrueLLActionCurve
    candidateACoupledMetricMatterRobinTrueLLEuler
  exact ((hCandidate.add hMatter).add hRobin).add hLL

/-- Two-parameter restriction of the same coupled action to one metric and
one matter direction.  Candidate A follows the outer metric curve; Robin and
LL are constant on this restriction. -/
def candidateACoupledMetricMatterNestedActionCurve
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
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (metricParameter matterParameter : Real) : Real :=
  candidateAActionCurve period hPeriod candidateMeasure interactionScale
      coefficients fields.metrics metricDirection metricParameter +
    programPMetricMatterNestedActionCurve period hPeriod candidateMeasure
      matterContract.massSquared fields metricDirection matterDirection
      metricParameter matterParameter +
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus junction
      robinMeasure +
    globalPTSymmetricDifferentialLLAction period hPeriod frame fields llMeasure

/-- The inner matter derivative of the coupled action is exactly the already
constructed matter Euler curve. -/
theorem candidateACoupledMetricMatterNestedActionCurve_matter_hasDerivAt
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
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (contract : DominatedIndependentMetricMatterMixedVariationContract
      period hPeriod candidateMeasure matterContract.massSquared fields
      metricDirection matterDirection)
    (metricParameter : Real) :
    HasDerivAt
      (candidateACoupledMetricMatterNestedActionCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        metricDirection matterDirection metricParameter)
      (integratedIndependentMatterEulerCurve period hPeriod candidateMeasure
        matterContract.massSquared fields metricDirection matterDirection
        metricParameter)
      0 := by
  have hMatter :=
    programPMetricMatterNestedActionCurve_matter_hasDerivAt period hPeriod
      candidateMeasure matterContract.massSquared fields metricDirection
      matterDirection contract metricParameter
  unfold candidateACoupledMetricMatterNestedActionCurve
  exact
    (((hMatter.const_add
        (candidateAActionCurve period hPeriod candidateMeasure interactionScale
          coefficients fields.metrics metricDirection metricParameter)).add_const
        (robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction robinMeasure)).add_const
      (globalPTSymmetricDifferentialLLAction period hPeriod frame fields
        llMeasure))

/-- Outer curve of actual inner derivatives of the same coupled action. -/
def candidateACoupledMetricMatterMixedDerivativeCurve
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
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (metricParameter : Real) : Real :=
  deriv
    (candidateACoupledMetricMatterNestedActionCurve period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
      metricDirection matterDirection metricParameter)
    0

/-- The existing integrated mixed density is the genuine metric derivative
of the matter derivative of the full coupled sector action. -/
theorem candidateACoupledMetricMatterMixedDerivativeCurve_hasDerivAt
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
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (contract : DominatedIndependentMetricMatterMixedVariationContract
      period hPeriod candidateMeasure matterContract.massSquared fields
      metricDirection matterDirection) :
    HasDerivAt
      (candidateACoupledMetricMatterMixedDerivativeCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        metricDirection matterDirection)
      (integratedIndependentMetricMatterMixedVariation period hPeriod
        candidateMeasure matterContract.massSquared fields metricDirection
        matterDirection)
      0 := by
  have hCurve :
      candidateACoupledMetricMatterMixedDerivativeCurve period hPeriod
          candidateMeasure interactionScale coefficients fields matterContract
          kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
          metricDirection matterDirection =
        integratedIndependentMatterEulerCurve period hPeriod candidateMeasure
          matterContract.massSquared fields metricDirection matterDirection := by
    funext metricParameter
    exact
      (candidateACoupledMetricMatterNestedActionCurve_matter_hasDerivAt
        period hPeriod candidateMeasure interactionScale coefficients
        fields matterContract kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure junction metricDirection matterDirection contract
        metricParameter).deriv
  rw [hCurve]
  exact integratedIndependentMatterEulerCurve_hasDerivAt period hPeriod
    candidateMeasure matterContract.massSquared fields metricDirection
    matterDirection contract

/-- Symmetric insertion of the two metric--matter cross slots. -/
def candidateACoupledMetricMatterCrossHessian
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  integratedIndependentMetricMatterMixedVariation period hPeriod
      candidateMeasure matterContract.massSquared fields
      first.complete.independent.metrics second.complete.independent.matter +
    integratedIndependentMetricMatterMixedVariation period hPeriod
      candidateMeasure matterContract.massSquared fields
      second.complete.independent.metrics first.complete.independent.matter

theorem candidateACoupledMetricMatterCrossHessian_symmetric
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) :
    candidateACoupledMetricMatterCrossHessian period hPeriod candidateMeasure
        fields matterContract first second =
      candidateACoupledMetricMatterCrossHessian period hPeriod candidateMeasure
        fields matterContract second first := by
  unfold candidateACoupledMetricMatterCrossHessian
  ring

/-- Candidate-A, fixed-metric matter, Robin and LL Hessians augmented by both
actual metric--matter cross slots.  Only the pure matter metric--metric term
is not yet included. -/
def candidateACoupledCrossCompletedSectorialHessian
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  candidateAPartialSectorialSameActionHessian period hPeriod candidateMeasure
      interactionScale coefficients
      (independentMatterMetricActionData period hPeriod fields candidateMeasure
        matterContract)
      kPlus kMinus robinMeasure frame llMeasure fields first second +
    candidateACoupledMetricMatterCrossHessian period hPeriod candidateMeasure
      fields matterContract first second

/-- The cross-completed sectorial Hessian is symmetric. -/
theorem candidateACoupledCrossCompletedSectorialHessian_symmetric
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (first second : ProgramPRobinCompleteVariation4D period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale
      coefficients) :
    candidateACoupledCrossCompletedSectorialHessian period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus robinMeasure frame llMeasure first second =
      candidateACoupledCrossCompletedSectorialHessian period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus robinMeasure frame llMeasure second first := by
  unfold candidateACoupledCrossCompletedSectorialHessian
  rw [candidateAPartialSectorialSameActionHessian_symmetric period hPeriod
      candidateMeasure interactionScale coefficients
      (independentMatterMetricActionData period hPeriod fields candidateMeasure
        matterContract)
      kPlus kMinus robinMeasure frame llMeasure fields first second contract,
    candidateACoupledMetricMatterCrossHessian_symmetric period hPeriod
      candidateMeasure fields matterContract first second]

/-- Candidate A, scalar matter, Robin and true LL with all scalar
metric--metric, metric--matter and matter--matter Hessian slots included. -/
def candidateACoupledMetricCompletedSectorialHessian
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  candidateACoupledCrossCompletedSectorialHessian period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus robinMeasure frame llMeasure first second +
    integratedIndependentMatterMetricHessian period hPeriod candidateMeasure
      matterContract.massSquared fields first.complete.independent.metrics
      second.complete.independent.metrics

/-- The scalar-metric-completed sectorial Hessian is symmetric. -/
theorem candidateACoupledMetricCompletedSectorialHessian_symmetric
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (first second : ProgramPRobinCompleteVariation4D period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale
      coefficients) :
    candidateACoupledMetricCompletedSectorialHessian period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus robinMeasure frame llMeasure first second =
      candidateACoupledMetricCompletedSectorialHessian period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus robinMeasure frame llMeasure second first := by
  unfold candidateACoupledMetricCompletedSectorialHessian
  rw [candidateACoupledCrossCompletedSectorialHessian_symmetric period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus robinMeasure frame llMeasure first second contract,
    integratedIndependentMatterMetricHessian_symmetric period hPeriod
      candidateMeasure matterContract.massSquared fields
      first.complete.independent.metrics second.complete.independent.metrics]

/-- Coordinate-decomposed Euler curve of the same coupled sector action.
Every correction vanishes at the base point and isolates one genuine second
partial derivative: sectorial, pure metric, and the two mixed slots. -/
def candidateACoupledMetricCompletedEulerCurve
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
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  let partialCurve := candidateAPartialSectorialEulerCurve period hPeriod
    candidateMeasure interactionScale coefficients
    (independentMatterMetricActionData period hPeriod fields candidateMeasure
      matterContract)
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    test varied
  let pureMetricCurve :=
    integratedIndependentMatterMetricFirstVariationAlongSecond period hPeriod
      candidateMeasure matterContract.massSquared fields
      test.complete.independent.metrics varied.complete.independent.metrics
  let variedMetricTestMatterCurve :=
    integratedIndependentMatterEulerCurve period hPeriod candidateMeasure
      matterContract.massSquared fields varied.complete.independent.metrics
      test.complete.independent.matter
  let testMetricVariedMatterCurve :=
    integratedIndependentMatterEulerCurve period hPeriod candidateMeasure
      matterContract.massSquared fields test.complete.independent.metrics
      varied.complete.independent.matter
  candidateACoupledMetricMatterRobinTrueLLEuler period hPeriod candidateMeasure
      interactionScale coefficients fields matterContract kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure junction test +
    (partialCurve parameter - partialCurve 0) +
    (pureMetricCurve parameter - pureMetricCurve 0) +
    (variedMetricTestMatterCurve parameter -
      variedMetricTestMatterCurve 0) +
    (testMetricVariedMatterCurve parameter -
      testMetricVariedMatterCurve 0)

/-- At the base point, the completed Euler curve is exactly the first
derivative coefficient of the coupled action. -/
@[simp]
theorem candidateACoupledMetricCompletedEulerCurve_zero
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
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod) :
    candidateACoupledMetricCompletedEulerCurve period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction test varied 0 =
      candidateACoupledMetricMatterRobinTrueLLEuler period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        test := by
  simp [candidateACoupledMetricCompletedEulerCurve]

/-- The completed Euler curve differentiates to the full scalar-coupled
sectorial Hessian.  All analytic assumptions are domination contracts for
passing the already proved pointwise derivatives under their integrals. -/
theorem candidateACoupledMetricCompletedEulerCurve_hasDerivAt
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
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
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod)
    (candidateContract : DominatedCandidateASecondVariationContract
      period hPeriod candidateMeasure interactionScale coefficients
      fields.metrics test.complete.independent.metrics
      varied.complete.independent.metrics)
    (pureMetricContract :
      DominatedIndependentMatterMetricSecondVariationContract period hPeriod
        candidateMeasure matterContract.massSquared fields
        test.complete.independent.metrics varied.complete.independent.metrics)
    (variedMetricTestMatterContract :
      DominatedIndependentMetricMatterMixedVariationContract period hPeriod
        candidateMeasure matterContract.massSquared fields
        varied.complete.independent.metrics test.complete.independent.matter)
    (testMetricVariedMatterContract :
      DominatedIndependentMetricMatterMixedVariationContract period hPeriod
        candidateMeasure matterContract.massSquared fields
        test.complete.independent.metrics varied.complete.independent.matter) :
    HasDerivAt
      (candidateACoupledMetricCompletedEulerCurve period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction
        test varied)
      (candidateACoupledMetricCompletedSectorialHessian period hPeriod
        candidateMeasure interactionScale coefficients fields matterContract
        kPlus kMinus robinMeasure frame llMeasure test varied)
      0 := by
  have hPartial :=
    candidateAPartialSectorialEulerCurve_hasDerivAt period hPeriod
      candidateMeasure interactionScale coefficients
      (independentMatterMetricActionData period hPeriod fields candidateMeasure
        matterContract)
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields
      junction test varied candidateContract
  have hPure :=
    integratedIndependentMatterMetricFirstVariationAlongSecond_hasDerivAt
      period hPeriod candidateMeasure matterContract.massSquared fields
      test.complete.independent.metrics varied.complete.independent.metrics
      pureMetricContract
  have hVariedMetricTestMatter :=
    integratedIndependentMatterEulerCurve_hasDerivAt period hPeriod
      candidateMeasure matterContract.massSquared fields
      varied.complete.independent.metrics test.complete.independent.matter
      variedMetricTestMatterContract
  have hTestMetricVariedMatter :=
    integratedIndependentMatterEulerCurve_hasDerivAt period hPeriod
      candidateMeasure matterContract.massSquared fields
      test.complete.independent.metrics varied.complete.independent.matter
      testMetricVariedMatterContract
  have hBase := hasDerivAt_const (x := (0 : Real))
    (candidateACoupledMetricMatterRobinTrueLLEuler period hPeriod
      candidateMeasure interactionScale coefficients fields matterContract
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure junction test)
  have hCombined :=
    ((((hBase.add (hPartial.sub_const
      (candidateAPartialSectorialEulerCurve period hPeriod candidateMeasure
        interactionScale coefficients
        (independentMatterMetricActionData period hPeriod fields
          candidateMeasure matterContract)
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields
        junction test varied 0))).add
      (hPure.sub_const
        (integratedIndependentMatterMetricFirstVariationAlongSecond period
          hPeriod candidateMeasure matterContract.massSquared fields
          test.complete.independent.metrics varied.complete.independent.metrics
          0))).add
      (hVariedMetricTestMatter.sub_const
        (integratedIndependentMatterEulerCurve period hPeriod candidateMeasure
          matterContract.massSquared fields
          varied.complete.independent.metrics test.complete.independent.matter
          0))).add
      (hTestMetricVariedMatter.sub_const
        (integratedIndependentMatterEulerCurve period hPeriod candidateMeasure
          matterContract.massSquared fields test.complete.independent.metrics
          varied.complete.independent.matter 0)))
  unfold candidateACoupledMetricCompletedEulerCurve
  dsimp only
  refine hCombined.congr_deriv ?_
  unfold candidateACoupledMetricCompletedSectorialHessian
    candidateACoupledCrossCompletedSectorialHessian
    candidateACoupledMetricMatterCrossHessian
  ring

end

end P0EFTJanusMappingTorusCandidateACoupledMetricMatterRobinTrueLLAction4D
end JanusFormal
