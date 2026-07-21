import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActiveQuotientHessian4D

/-!
# Reconstruction through the active matter--Robin--LL quotient

Both Euler and Hessian use only the active projection.  The reconstruction
retains the same explicit Robin normalization constant and does not concern
the complete Candidate-A action.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActiveQuotientReconstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusCommonMatterRobinLLActionReconstruction4D
open P0EFTJanusCommonMatterRobinLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

theorem commonMatterRobinLLEuler_congr_active
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    {first second : MatterRobinLLEnrichedDirections period hPeriod}
    (hActive : activeDirection period hPeriod first =
      activeDirection period hPeriod second) :
    commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction first =
      commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction second := by
  have hMatter := congrArg ActiveMatterRobinLLDirection.matter hActive
  have hRobin := congrArg ActiveMatterRobinLLDirection.robin hActive
  have hLL := congrArg ActiveMatterRobinLLDirection.ll hActive
  change matterVariationComponentFamily period hPeriod first.common.matter =
    matterVariationComponentFamily period hPeriod second.common.matter at hMatter
  change first.robin = second.robin at hRobin
  change first.common.ll = second.common.ll at hLL
  unfold commonMatterRobinLLEuler
  rw [hMatter, hRobin, hLL]

/-- Euler pairing descended to the active-direction quotient. -/
def quotientMatterRobinLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveMatterRobinLLQuotient period hPeriod) : Real :=
  Quotient.liftOn direction
    (commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction)
    (by
      intro first second hActive
      exact commonMatterRobinLLEuler_congr_active period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields
        junction hActive)

@[simp]
theorem quotientMatterRobinLLEuler_mk
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    quotientMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction
        (Quotient.mk (activeDirectionSetoid period hPeriod) direction) =
      commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction :=
  rfl

/-- Active projection of the radial enriched direction is exactly its matter,
Robin and LL triple. -/
@[simp]
theorem activeDirection_radial
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) :
    activeDirection period hPeriod
        (matterRobinLLRadialDirection period hPeriod fields junction) =
      { matter := matterVariationComponentFamily period hPeriod fields.matter
        robin := junction
        ll := fields.llField } := by
  rfl

/-- Reconstruction expressed through the active quotient Hessian. -/
theorem commonMatterRobinLLAction_reconstructed_through_active_quotient
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) :
    matterRobinLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure
        (independentMatterComponentFamily period hPeriod fields) junction fields =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          0 robinMeasure +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          0 junction robinMeasure +
        (1 / 2 : Real) *
          quotientMatterRobinLLHessian period hPeriod matterData kPlus kMinus
            robinMeasure frame llMeasure fields
            (Quotient.mk (activeDirectionSetoid period hPeriod)
              (matterRobinLLRadialDirection period hPeriod fields junction))
            (Quotient.mk (activeDirectionSetoid period hPeriod)
              (matterRobinLLRadialDirection period hPeriod fields junction)) := by
  rw [quotientMatterRobinLLHessian_mk]
  exact commonMatterRobinLLAction_reconstructed period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction

end

end P0EFTJanusCommonMatterRobinLLActiveQuotientReconstruction4D
end JanusFormal
