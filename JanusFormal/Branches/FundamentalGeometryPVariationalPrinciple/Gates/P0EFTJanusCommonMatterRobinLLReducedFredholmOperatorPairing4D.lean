import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D

/-!
# Operator pairing for the shared Robin--LL Fredholm block

This identifies the pairing of the actual reduced block-diagonal continuous
operator with the common matter--Robin--LL Hessian only on the smooth Robin +
LL inclusion with zero scalar/matter direction.  It is not an identification
of the two complete actions.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D

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
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D

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

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Smooth inclusion of the shared Robin + LL block into the completed reduced
bosonic Jacobi space, with scalar component zero. -/
def reducedRobinLLInclusion
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData)
    [IsFiniteMeasure robinMeasure] :
    ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData :=
  (staticScalarEnergyEmbedding period hPeriod scalarData 0,
    smoothThroatFieldToL2 period hPeriod robinMeasure robin,
    llH1SmoothEmbedding period hPeriod llData ll)

/-- Componentwise Hilbert pairing of the actual block-diagonal operator. -/
def reducedBosonicJacobiOperatorBlockPairing
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (first second :
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData) : Real :=
  let applied := reducedBosonicJacobiOperator period hPeriod scalarData
    kPlus kMinus robinMeasure llData first
  inner Real applied.1 second.1 + inner Real applied.2.1 second.2.1 +
    inner Real applied.2.2 second.2.2

/-- Pairing of the genuine completed Fredholm operator equals the Hessian of
the common assembled action on the shared smooth Robin + LL directions. -/
theorem reducedBosonicJacobiOperator_pairing_eq_commonMatterRobinLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    reducedBosonicJacobiOperatorBlockPairing period hPeriod scalarData
        kPlus kMinus robinMeasure llData
        (reducedRobinLLInclusion period hPeriod scalarData robinMeasure
          llData robinFirst llFirst)
        (reducedRobinLLInclusion period hPeriod scalarData robinMeasure
          llData robinSecond llSecond) =
      commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu llData.fields
        (commonRobinLLDirection period hPeriod robinFirst llFirst.toTest)
        (commonRobinLLDirection period hPeriod robinSecond llSecond.toTest) := by
  rw [commonMatterRobinLLHessian_eq_reducedNatural_robinLL_block]
  unfold reducedBosonicJacobiOperatorBlockPairing reducedBosonicNaturalHessian
  rfl

/-- With the already required nonzero Robin coupling, vanishing of the actual
operator on a shared included vector forces that completed vector itself to
be zero.  No injectivity of the raw smooth parameterization is added here. -/
theorem reducedBosonicJacobiOperator_shared_inclusion_kernel
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real)
    (ll : LLH1Smooth period hPeriod llData)
    (hZero : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      robinMeasure llData
      (reducedRobinLLInclusion period hPeriod scalarData robinMeasure llData
        robin ll) = 0) :
    reducedRobinLLInclusion period hPeriod scalarData robinMeasure llData
        robin ll = 0 := by
  apply reducedBosonicJacobiOperator_injective period hPeriod scalarData
    kPlus kMinus hCoupling robinMeasure llData
  simpa using hZero

end

end P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D
end JanusFormal
