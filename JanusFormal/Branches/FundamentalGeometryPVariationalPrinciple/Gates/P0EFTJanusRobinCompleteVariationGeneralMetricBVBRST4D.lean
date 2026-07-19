import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D

/-!
# Robin-complete variation with the general metric BV doublet

This gate places the already constructed general Lorentz metric BV phase in
the full-metric slot of `ProgramPRobinCompleteVariation4D`.  The same wrapper
retains the Robin velocity and all independent fields used by the genuine
matter + Robin + three-slot LL action, Euler derivative and Hessian.

The metric differential is the existing linear BV rule `Q(h,h⁺)=(h⁺,0)`.
It leaves those sectorial variational quantities and the current boundary
domain unchanged, while its D9 metric reading is the exact antifield tensor.
No EH or Maxwell term, and no nonlinear/global BRST operator on the whole
wrapper, is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusRobinCompleteVariationGeneralMetricBVBRST4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff InnerProduct ENNReal
open MeasureTheory
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Put the even tensor pair of the genuine metric BV phase in the complete
metric slot while retaining an arbitrary Robin velocity. -/
def robinCompleteVariationWithGeneralMetricBV
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    ProgramPRobinCompleteVariation4D period hPeriod where
  complete := completeVariationWithGeneralMetricBV period hPeriod variation phase
  robin := robin

@[simp]
theorem robinCompleteVariationWithGeneralMetricBV_complete
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
      phase).complete =
        completeVariationWithGeneralMetricBV period hPeriod variation phase :=
  rfl

@[simp]
theorem robinCompleteVariationWithGeneralMetricBV_independent
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
      phase).complete.independent = variation :=
  rfl

@[simp]
theorem robinCompleteVariationWithGeneralMetricBV_robin
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
      phase).robin = robin :=
  rfl

/-- The existing BV differential is read exactly in the wrapper's complete
full-metric slot; Robin is not altered. -/
theorem robinCompleteVariationWithGeneralMetricBV_BRST_fullMetric
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) :
    (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
      (smoothGeneralMetricBVBRST period hPeriod phase)
      ).complete.fullMetricPerturbation sector =
      generalMetricTensorPairSector period hPeriod phase.2 sector :=
  completeVariationWithGeneralMetricBV_BRST_fullMetric period hPeriod variation
    phase sector

/-- Applying the metric BV differential twice gives the zero-metric complete
inclusion and retains the same Robin velocity. -/
theorem robinCompleteVariationWithGeneralMetricBV_BRST_square
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
        (smoothGeneralMetricBVBRST period hPeriod
          (smoothGeneralMetricBVBRST period hPeriod phase)) =
      { complete := independentCompleteVariation period hPeriod variation
        robin := robin } := by
  unfold robinCompleteVariationWithGeneralMetricBV
  rw [completeVariationWithGeneralMetricBV_BRST_square]

/-- Before applying `Q`, D9 reads the six spatial coefficients of the even
metric tensor in the requested sector. -/
theorem robinCompleteVariationWithGeneralMetricBV_metricPerturbationAt
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
      phase).complete.metricPerturbationAt period hPeriod sector point =
      d9FullMetricProjection
        (d9TensorChartMetricVariation period hPeriod
          (generalMetricTensorPairSector period hPeriod phase.1 sector)
          (selectedD9ThroatHolonomicPatch period hPeriod point)
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)) :=
  completeVariationWithGeneralMetricBV_metricPerturbationAt period hPeriod
    variation phase sector point

/-- After `Q`, the same D9 observation reads the antifield tensor exactly. -/
theorem robinCompleteVariationWithGeneralMetricBV_BRST_metricPerturbationAt
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
      (smoothGeneralMetricBVBRST period hPeriod phase)
      ).complete.metricPerturbationAt period hPeriod sector point =
      d9FullMetricProjection
        (d9TensorChartMetricVariation period hPeriod
          (generalMetricTensorPairSector period hPeriod phase.2 sector)
          (selectedD9ThroatHolonomicPatch period hPeriod point)
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)) :=
  completeVariationWithGeneralMetricBV_BRST_metricPerturbationAt period hPeriod
    variation phase sector point

/-- The genuine matter + Robin + full LL action curve is unchanged by the
metric BV step because its independent and Robin directions are identical. -/
theorem robinCompleteMatterTrueLLActionCurve_generalMetricBV_BRST
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction robin : SmoothThroatField period hPeriod Real)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real) :
    robinCompleteMatterTrueLLActionCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
          (smoothGeneralMetricBVBRST period hPeriod phase)) parameter =
      robinCompleteMatterTrueLLActionCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
          phase) parameter :=
  rfl

/-- Its Euler coefficient is unchanged for the same reason. -/
theorem robinCompleteMatterTrueLLEuler_generalMetricBV_BRST
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction robin : SmoothThroatField period hPeriod Real)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    robinCompleteMatterTrueLLEuler period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
          (smoothGeneralMetricBVBRST period hPeriod phase)) =
      robinCompleteMatterTrueLLEuler period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
          phase) :=
  rfl

/-- Both slots of the actual sectorial Hessian are unchanged by `Q`. -/
theorem robinCompleteMatterTrueLLHessian_generalMetricBV_BRST
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (firstVariation secondVariation : IndependentFieldVariation period hPeriod)
    (firstRobin secondRobin : SmoothThroatField period hPeriod Real)
    (firstPhase secondPhase : SmoothGeneralMetricBVField period hPeriod) :
    robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (robinCompleteVariationWithGeneralMetricBV period hPeriod firstVariation
          firstRobin (smoothGeneralMetricBVBRST period hPeriod firstPhase))
        (robinCompleteVariationWithGeneralMetricBV period hPeriod secondVariation
          secondRobin (smoothGeneralMetricBVBRST period hPeriod secondPhase)) =
      robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (robinCompleteVariationWithGeneralMetricBV period hPeriod firstVariation
          firstRobin firstPhase)
        (robinCompleteVariationWithGeneralMetricBV period hPeriod secondVariation
          secondRobin secondPhase) :=
  rfl

/-- The current boundary domain is likewise invariant under the metric BV
step.  This remains the independent-field boundary condition, not a new
metric-BV or Robin boundary law. -/
theorem robinCompleteVariationWithGeneralMetricBV_BRST_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
        (smoothGeneralMetricBVBRST period hPeriod phase) ∈
        programPRobinBoundaryTangentDomain4D period hPeriod domain ↔
      robinCompleteVariationWithGeneralMetricBV period hPeriod variation robin
        phase ∈ programPRobinBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

end
end P0EFTJanusRobinCompleteVariationGeneralMetricBVBRST4D
end JanusFormal
