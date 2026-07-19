import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLGeneralMetricBVAgreement4D

/-!
# One complete variation for the visible action quotient, metric BV and D9

This gate records that the algebraic quotient of the present matter--LL action
and Hessian is represented by the same `ProgramPCompleteVariation4D` whose
general metric slot is read by D9 and whose independent slot is tested by the
current boundary domain.  It supplies no EH or Maxwell dynamics.
-/

namespace JanusFormal
namespace P0EFTJanusMatterLLVisibleQuotientGeneralMetricBVD9Bridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusIndependentMatterLLActionVisibleQuotient4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusCompleteVariationGlobalMetricD9Projection4D
open P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
open P0EFTJanusCompleteVariationMatterLLGeneralMetricBVAgreement4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
open P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

theorem visibleQuotientActionCurve_withGeneralMetricBV
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real) :
    matterLLVisibleQuotientActionCurve period hPeriod data frame fields mu
        parameter ((matterLLActionInvisibleSubmodule period hPeriod).mkQ variation) =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod variation phase)
        mu parameter := by
  rw [matterLLVisibleQuotientActionCurve_mkQ]
  exact (matterLLActionCurve_withGeneralMetricBV period hPeriod data frame fields
    variation phase mu parameter).symm

theorem visibleQuotientHessian_withGeneralMetricBV
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : IndependentFieldVariation period hPeriod)
    (firstPhase secondPhase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    matterLLActionVisibleQuotientHessian period hPeriod data frame fields mu
        ((matterLLActionInvisibleSubmodule period hPeriod).mkQ first)
        ((matterLLActionInvisibleSubmodule period hPeriod).mkQ second) =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (completeVariationWithGeneralMetricBV period hPeriod first firstPhase)
        (completeVariationWithGeneralMetricBV period hPeriod second secondPhase) mu := by
  rw [matterLLActionVisibleQuotientHessian_mkQ]
  exact (matterLLHessian_withGeneralMetricBV period hPeriod data frame fields
    first second firstPhase secondPhase mu).symm

/-- One typed statement links the sectorial action quotient and Hessian to the
genuine D9 metric observation and to the current Program-P boundary domain.
The first two conjuncts remain explicitly matter--LL only. -/
theorem visibleQuotient_generalMetricBV_D9_boundary_agreement
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation first second : IndependentFieldVariation period hPeriod)
    (phase firstPhase secondPhase : SmoothGeneralMetricBVField period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (parameter : Real) (sector : Sector)
    (point : EffectiveThroat period hPeriod) :
    (matterLLVisibleQuotientActionCurve period hPeriod data frame fields mu
          parameter
          ((matterLLActionInvisibleSubmodule period hPeriod).mkQ variation) =
        completeVariationMatterLLActionCurve period hPeriod data frame fields
          (completeVariationWithGeneralMetricBV period hPeriod variation phase)
          mu parameter) ∧
    (matterLLActionVisibleQuotientHessian period hPeriod data frame fields mu
          ((matterLLActionInvisibleSubmodule period hPeriod).mkQ first)
          ((matterLLActionInvisibleSubmodule period hPeriod).mkQ second) =
        completeVariationMatterLLHessian period hPeriod data frame fields
          (completeVariationWithGeneralMetricBV period hPeriod first firstPhase)
          (completeVariationWithGeneralMetricBV period hPeriod second secondPhase) mu) ∧
    ((completeVariationWithGeneralMetricBV period hPeriod variation phase
        ).metricPerturbationAt period hPeriod sector point =
      d9FullMetricProjection
        (d9TensorChartMetricVariation period hPeriod
          (generalMetricTensorPairSector period hPeriod phase.1 sector)
          (selectedD9ThroatHolonomicPatch period hPeriod point)
          (selectedD9ThroatHolonomicCoordinate period hPeriod point))) ∧
    (completeVariationWithGeneralMetricBV period hPeriod variation phase ∈
          programPBoundaryTangentDomain4D period hPeriod domain ↔
        variation ∈ independentBoundaryTangentDomain4D period hPeriod domain) := by
  exact ⟨visibleQuotientActionCurve_withGeneralMetricBV period hPeriod data frame
      fields variation phase mu parameter,
    visibleQuotientHessian_withGeneralMetricBV period hPeriod data frame fields
      first second firstPhase secondPhase mu,
    completeVariationWithGeneralMetricBV_metricPerturbationAt period hPeriod
      variation phase sector point,
    completeVariationWithGeneralMetricBV_mem_boundaryDomain_iff period hPeriod
      domain variation phase⟩

end
end P0EFTJanusMatterLLVisibleQuotientGeneralMetricBVD9Bridge4D
end JanusFormal
