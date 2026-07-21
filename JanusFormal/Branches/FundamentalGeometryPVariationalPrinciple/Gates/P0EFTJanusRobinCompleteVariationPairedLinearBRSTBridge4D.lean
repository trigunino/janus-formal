import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationPairedLinearBRSTBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D

/-!
# Paired linear BRST ghosts on the Robin-complete variation

This gate transports the existing genuine global `U(1)^2` ghost pair and
smooth throat diffeomorphism ghost to `ProgramPRobinCompleteVariation4D`, with
zero Robin velocity.  It retains the established square-zero statement and
the current boundary-domain result.  The matter + Robin + LL action and its
Hessian are insensitive to this ghost-coordinate step.

The intrinsic abelian gauge potentials are still not inserted into the
coordinate gauge slot.  Thus no Maxwell term, global nonlinear BRST complex,
ghost Fredholm block, regulator, or anomaly cancellation is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusRobinCompleteVariationPairedLinearBRSTBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff InnerProduct ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D
open P0EFTJanusCompleteVariationPairedLinearBRSTBridge4D
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

/-- The paired global ghost coordinates in the same Robin-complete tangent
used by the current matter + Robin + LL action and Hessian. -/
def robinCompleteVariationPairedLinearBRSTGhosts
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    ProgramPRobinCompleteVariation4D period hPeriod :=
  includeCompleteVariation period hPeriod
    (completeVariationPairedLinearBRSTGhosts period hPeriod state)

@[simp]
theorem robinCompleteVariationPairedLinearBRSTGhosts_complete
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state).complete =
      completeVariationPairedLinearBRSTGhosts period hPeriod state :=
  rfl

@[simp]
theorem robinCompleteVariationPairedLinearBRSTGhosts_robin
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state).robin =
      0 :=
  rfl

@[simp]
theorem robinCompleteVariationPairedLinearBRSTGhosts_ghosts
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state
      ).complete.independent.ghosts =
      (state.firstU1.ghost, state.secondU1.ghost) :=
  rfl

/-- The existing square-zero differential remains square-zero in the
Robin-complete wrapper. -/
theorem robinCompleteVariationPairedLinearBRSTGhosts_BRST_square
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
        (commonPairedD9LinearBRSTDifferential period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state)) =
      robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
        (zeroCommonPairedD9LinearBRSTBlock period hPeriod) := by
  unfold robinCompleteVariationPairedLinearBRSTGhosts
  rw [completeVariationPairedLinearBRSTGhosts_BRST_square]

/-- The BRST image satisfies the pulled-back current boundary domain. -/
theorem robinCompleteVariationPairedLinearBRSTGhosts_BRST_mem_boundaryDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
        (commonPairedD9LinearBRSTDifferential period hPeriod state) ∈
      programPRobinBoundaryTangentDomain4D period hPeriod domain := by
  change completeVariationPairedLinearBRSTGhosts period hPeriod
      (commonPairedD9LinearBRSTDifferential period hPeriod state) ∈
    programPBoundaryTangentDomain4D period hPeriod domain
  exact completeVariationPairedLinearBRSTGhosts_BRST_mem_boundaryDomain
    period hPeriod domain state

/-- The current matter + Robin + LL action is insensitive to this linear
ghost-coordinate BRST step.  This is not Maxwell or EH invariance. -/
theorem robinCompleteMatterTrueLLActionCurve_pairedLinearBRSTGhosts
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (parameter : Real) :
    robinCompleteMatterTrueLLActionCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state)) parameter =
      robinCompleteMatterTrueLLActionCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state)
        parameter :=
  rfl

/-- Both slots of the current matter + Robin + LL Hessian are insensitive to
the paired linear ghost-coordinate BRST step. -/
theorem robinCompleteMatterTrueLLHessian_pairedLinearBRSTGhosts
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : CommonPairedD9LinearBRSTBlock period hPeriod) :
    robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod first))
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod second)) =
      robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod first)
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod second) :=
  rfl

end
end P0EFTJanusRobinCompleteVariationPairedLinearBRSTBridge4D
end JanusFormal
