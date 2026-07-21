import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinCompleteVariationPairedLinearBRSTBridge4D

/-!
# Paired linear BRST and the reduced Fredholm projection

The paired `U(1)^2` and throat-diffeomorphism ghost coordinates already live
in the same `ProgramPRobinCompleteVariation4D` wrapper as the current
matter + Robin + LL action, boundary domain, Hessian and reduced Fredholm
pairing.  This gate proves that the canonical Robin + LL Fredholm projection
is unchanged by the paired linear BRST differential and records the existing
same-action Hessian/Fredholm identity on that projection.

This is deliberately sectorial: the projection discards all ghost coordinates.
No ghost Fredholm operator, Maxwell/EH block, global nonlinear BRST complex,
regulator or anomaly statement is constructed.
-/

namespace JanusFormal
namespace P0EFTJanusRobinCompleteVariationPairedLinearBRSTReducedFredholm4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff InnerProduct ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusRobinCompleteVariationPairedLinearBRSTBridge4D

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

/-- The canonical reduced Robin + LL sector forgets every paired ghost
coordinate.  In particular it cannot be mistaken for a ghost Fredholm block. -/
theorem reducedRobinLLSector_robinCompletePairedLinearBRST
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    reducedRobinLLSector period hPeriod
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state) =
      reducedRobinLLSector period hPeriod
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
          (zeroCommonPairedD9LinearBRSTBlock period hPeriod)) :=
  rfl

/-- The actual vector supplied to the reduced Fredholm operator is therefore
independent of all paired linear BRST ghost coordinates. -/
theorem reducedRobinLLFredholmVector_robinCompletePairedLinearBRST
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    reducedRobinLLFredholmVector period hPeriod scalarData robinMeasure llData
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state) =
      reducedRobinLLFredholmVector period hPeriod scalarData robinMeasure llData
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
          (zeroCommonPairedD9LinearBRSTBlock period hPeriod)) :=
  rfl

/-- Applying the paired linear BRST differential does not change the reduced
Fredholm pairing against any tangent in the same Robin-complete wrapper. -/
theorem reducedRobinLLFredholmPairing_pairedLinearBRST_invariant
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (test : ProgramPRobinCompleteVariation4D period hPeriod) :
    reducedRobinLLFredholmPairing period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
          (commonPairedD9LinearBRSTDifferential period hPeriod state)) test =
      reducedRobinLLFredholmPairing period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state)
        test := by
  unfold reducedRobinLLFredholmPairing
  rw [reducedRobinLLFredholmVector_robinCompletePairedLinearBRST
      period hPeriod scalarData robinMeasure llData
      (commonPairedD9LinearBRSTDifferential period hPeriod state),
    reducedRobinLLFredholmVector_robinCompletePairedLinearBRST
      period hPeriod scalarData robinMeasure llData state]

/-- On the same wrapper and its canonical Robin + LL projection, the Hessian
of the actual matter + Robin + LL action is the reduced Fredholm pairing even
after the paired BRST step.  The equality remains zero-ghost-sectorial. -/
theorem robinCompleteHessian_reducedPairedLinearBRST_BRST_eq_fredholmPairing
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    [IsFiniteMeasure llData.mu]
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (test : ProgramPRobinCompleteVariation4D period hPeriod) :
    robinCompleteMatterTrueLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields
        (reducedRobinLLSector period hPeriod
          (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod
            (commonPairedD9LinearBRSTDifferential period hPeriod state)))
        (reducedRobinLLSector period hPeriod test) =
      reducedRobinLLFredholmPairing period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (robinCompleteVariationPairedLinearBRSTGhosts period hPeriod state)
        test := by
  rw [robinCompleteHessian_reducedRobinLL_eq_fredholmPairing]
  exact reducedRobinLLFredholmPairing_pairedLinearBRST_invariant
    period hPeriod scalarData kPlus kMinus robinMeasure llData state test

end
end P0EFTJanusRobinCompleteVariationPairedLinearBRSTReducedFredholm4D
end JanusFormal
