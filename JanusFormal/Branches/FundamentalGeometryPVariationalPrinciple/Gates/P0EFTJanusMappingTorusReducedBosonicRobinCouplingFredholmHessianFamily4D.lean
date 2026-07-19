import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D

/-!
# Reduced Robin-coupling Fredholm Hessian family

On the fixed reduced scalar + Robin + LL spaces, this gate varies only the
first Robin coupling.  The resulting bounded operator family is smooth in
operator norm, is bijective of index zero away from the single degenerate
coupling, and its smooth-sector pairing is the mixed Hessian of the same
assembled reduced action at every parameter.

This is not the natural Fredholm family of the global Program-P action:
geometry, metric, gauge, ghost, domain and regulator parameters are fixed or
absent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusReducedBosonicRobinCouplingFredholmHessianFamily4D

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
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
open P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D

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

/-- The genuine reduced block operator with only `kPlus` varying. -/
def reducedBosonicRobinCouplingOperatorFamily
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) (kPlus : Real) :
    ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData →L[Real]
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData :=
  reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
    robinMeasure llData

/-- Componentwise pairing of one member of the coupling family. -/
def reducedBosonicRobinCouplingOperatorFamilyPairing
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) (kPlus : Real)
    (first second :
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData) :
    Real :=
  let applied := reducedBosonicRobinCouplingOperatorFamily period hPeriod
    scalarData kMinus robinMeasure llData kPlus first
  inner Real applied.1 second.1 + inner Real applied.2.1 second.2.1 +
    inner Real applied.2.2 second.2.2

/-- Varying the Robin coupling gives a `C∞` family in the bounded-operator
norm on the fixed reduced space. -/
theorem reducedBosonicRobinCouplingOperatorFamily_contDiff
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    ContDiff Real (⊤ : WithTop ℕ∞)
      (reducedBosonicRobinCouplingOperatorFamily period hPeriod scalarData
        kMinus robinMeasure llData) := by
  unfold reducedBosonicRobinCouplingOperatorFamily
    reducedBosonicJacobiOperator robinL2HessianOperator
  let innerProdMap := ContinuousLinearMap.prodMapL Real
    (ThroatScalarL2 period hPeriod robinMeasure)
    (ThroatScalarL2 period hPeriod robinMeasure)
    (LLH1Space period hPeriod llData)
    (LLH1Space period hPeriod llData)
  let outerProdMap := ContinuousLinearMap.prodMapL Real
    (StaticScalarEnergyH1 period hPeriod scalarData)
    (StaticScalarEnergyH1 period hPeriod scalarData)
    (ThroatScalarL2 period hPeriod robinMeasure ×
      LLH1Space period hPeriod llData)
    (ThroatScalarL2 period hPeriod robinMeasure ×
      LLH1Space period hPeriod llData)
  change ContDiff Real (⊤ : WithTop ℕ∞)
    (fun kPlus : Real =>
      outerProdMap
        (completedStaticScalarJacobiOperator period hPeriod scalarData,
          innerProdMap
            ((kPlus + kMinus) • ContinuousLinearMap.id Real
                (ThroatScalarL2 period hPeriod robinMeasure),
              completedLLJacobiOperator period hPeriod llData)))
  fun_prop

/-- Every nondegenerate member of the reduced family is a bounded bijection
with closed range and algebraic Fredholm index zero. -/
theorem reducedBosonicRobinCouplingOperatorFamily_fredholm_index_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (kPlus : Real) (hCoupling : kPlus + kMinus ≠ 0) :
    Function.Bijective
        (reducedBosonicRobinCouplingOperatorFamily period hPeriod scalarData
          kMinus robinMeasure llData kPlus) ∧
      IsClosed
        (LinearMap.range
          (reducedBosonicRobinCouplingOperatorFamily period hPeriod scalarData
            kMinus robinMeasure llData kPlus).toLinearMap :
          Set (ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure
            llData)) ∧
      reducedBosonicJacobiIndex period hPeriod scalarData kPlus kMinus
        robinMeasure llData = 0 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact reducedBosonicJacobiOperator_injective period hPeriod scalarData
      kPlus kMinus hCoupling robinMeasure llData
  · exact reducedBosonicJacobiOperator_surjective period hPeriod scalarData
      kPlus kMinus hCoupling robinMeasure llData
  · exact reducedBosonicJacobiOperator_range_isClosed period hPeriod
      scalarData kPlus kMinus hCoupling robinMeasure llData
  · exact reducedBosonicJacobiIndex_zero period hPeriod scalarData kPlus
      kMinus hCoupling robinMeasure llData

/-- At every Robin coupling, the pairing of that same family member on the
smooth reduced domain is the actual mixed Hessian of the assembled scalar +
Robin + LL action carrying the identical coupling. -/
theorem reducedBosonicRobinCouplingOperatorFamily_pairing_eq_sameActionHessian
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (kPlus : Real)
    (scalarBase : GlobalScalarTestSpace period hPeriod)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (scalarFirst scalarSecond :
      StaticGlobalScalarTest period hPeriod scalarData)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    reducedBosonicRobinCouplingOperatorFamilyPairing period hPeriod scalarData
        kMinus robinMeasure llData kPlus
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) =
      reducedBosonicSmoothActionMixedHessian period hPeriod scalarData kPlus
        kMinus bulkPlus bulkMinus robinMeasure
        (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu scalarBase
        scalarFirst.toField scalarSecond.toField junction robinFirst robinSecond
        llData.fields llFirst.toTest llSecond.toTest := by
  calc
    _ = reducedBosonicJacobiOperatorBlockPairing period hPeriod scalarData
        kPlus kMinus robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := rfl
    _ = reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) := by
      unfold reducedBosonicJacobiOperatorBlockPairing
        reducedBosonicNaturalHessian
      rfl
    _ = _ :=
      reducedBosonicNaturalHessian_smooth_eq_assembledActionMixedHessian
        period hPeriod scalarData kPlus kMinus robinMeasure llData scalarBase
        bulkPlus bulkMinus junction scalarFirst scalarSecond robinFirst
        robinSecond llFirst llSecond

end
end P0EFTJanusMappingTorusReducedBosonicRobinCouplingFredholmHessianFamily4D
end JanusFormal
