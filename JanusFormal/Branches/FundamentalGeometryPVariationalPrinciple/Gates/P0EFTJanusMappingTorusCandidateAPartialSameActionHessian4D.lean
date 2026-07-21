import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D

/-!
# Sectorial same-action Hessian with Candidate A

This gate adds the genuine eight-component Candidate-A Hessian to the existing
matter + Robin + true-LL Hessian on `ProgramPRobinCompleteVariation4D`.
It remains sectorial: Einstein--Hilbert, Maxwell, ghosts, and identification
with a full natural Fredholm family are not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCandidateAPartialSameActionHessian4D

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
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusCandidateAIntegratedMetricHessian4D
open P0EFTJanusMappingTorusCandidateARobinCompleteMatterTrueLLActionBridge4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D

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

/-- Hessian of the sectorial sum: Candidate A + matter + Robin + true LL. -/
def candidateAPartialSectorialSameActionHessian
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  integratedCandidateAMetricHessian period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      first.complete.independent.metrics second.complete.independent.metrics +
    robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second

/-- The sectorial Hessian is symmetric under the visible Candidate-A C2
hypothesis; the other three summands are already unconditionally symmetric. -/
theorem candidateAPartialSectorialSameActionHessian_symmetric
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPRobinCompleteVariation4D period hPeriod)
    (contract : CandidateAGlobalDensityC2Contract interactionScale coefficients) :
    candidateAPartialSectorialSameActionHessian period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second =
      candidateAPartialSectorialSameActionHessian period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus robinMeasure frame
        llMeasure fields second first := by
  unfold candidateAPartialSectorialSameActionHessian
  rw [integratedCandidateAMetricHessian_symmetric period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      first.complete.independent.metrics second.complete.independent.metrics
      contract,
    robinCompleteMatterTrueLLHessian_symmetric period hPeriod matterData kPlus
      kMinus robinMeasure frame llMeasure fields first second]

/-- Euler pairing in the first direction along the scale-chart/field curve
generated by the second direction. -/
def candidateAPartialSectorialEulerCurve
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
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  integratedCandidateAFirstVariationAlongSecond period hPeriod candidateMeasure
      interactionScale coefficients fields.metrics
      test.complete.independent.metrics varied.complete.independent.metrics parameter +
    robinCompleteMatterTrueLLEulerCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure
      (independentMatterComponentFamily period hPeriod fields) junction fields
      test varied parameter

/-- At the base point this is exactly the Euler pairing already proved to be
the first derivative of the summed sectorial action. -/
theorem candidateAPartialSectorialEulerCurve_zero
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
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod) :
    candidateAPartialSectorialEulerCurve period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction test varied 0 =
      candidateARobinCompleteMatterTrueLLEuler period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction test := by
  unfold candidateAPartialSectorialEulerCurve
    candidateARobinCompleteMatterTrueLLEuler
  rw [integratedCandidateAFirstVariationAlongSecond_zero]
  congr 1
  have hMatterCurve : matterMultipletAffineCurve period hPeriod
      (independentMatterComponentFamily period hPeriod fields)
      (matterVariationComponentFamily period hPeriod
        (toFullMatterRobinLLDirections period hPeriod varied).common.matter) 0 =
      independentMatterComponentFamily period hPeriod fields := by
    funext index
    ext point
    simp [matterMultipletAffineCurve, scalarAffineCurve]
  unfold robinCompleteMatterTrueLLEulerCurve
    robinCompleteMatterTrueLLEuler globalMatterRobinFullLLFirstVariation
    fullMatterRobinTrueLLEuler
  dsimp only
  rw [hMatterCurve]
  simp [junctionAffineCurve, fullLLCurve]

/-- The Euler pairing of the same sectorial action differentiates to the
displayed symmetric Hessian. -/
theorem candidateAPartialSectorialEulerCurve_hasDerivAt
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
    (test varied : ProgramPRobinCompleteVariation4D period hPeriod)
    (contract : DominatedCandidateASecondVariationContract period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      test.complete.independent.metrics varied.complete.independent.metrics) :
    HasDerivAt
      (candidateAPartialSectorialEulerCurve period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction test varied)
      (candidateAPartialSectorialSameActionHessian period hPeriod candidateMeasure
        interactionScale coefficients matterData kPlus kMinus robinMeasure frame
        llMeasure fields test varied) 0 := by
  unfold candidateAPartialSectorialEulerCurve
    candidateAPartialSectorialSameActionHessian
  exact
    (integratedCandidateAFirstVariationAlongSecond_hasDerivAt period hPeriod
      candidateMeasure interactionScale coefficients fields.metrics
      test.complete.independent.metrics varied.complete.independent.metrics
      contract).add
    (robinCompleteMatterTrueLLEuler_hasDerivAt period hPeriod matterData kPlus
      kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      (independentMatterComponentFamily period hPeriod fields) junction fields
      test varied)

/-- The base Euler used above is the first derivative of the same summed
sectorial action curve. -/
theorem candidateAPartialSectorialAction_hasDerivAt
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
        robinMeasure frame llMeasure fields junction direction) 0 :=
  candidateARobinCompleteMatterTrueLLAction_hasDerivAt period hPeriod
    candidateMeasure interactionScale coefficients matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
    contract

end

end P0EFTJanusMappingTorusCandidateAPartialSameActionHessian4D
end JanusFormal
