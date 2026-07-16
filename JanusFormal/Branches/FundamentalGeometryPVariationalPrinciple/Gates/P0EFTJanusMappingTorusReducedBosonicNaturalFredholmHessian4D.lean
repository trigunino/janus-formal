import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D

/-!
# Reduced bosonic natural Fredholm Hessian on the effective D8 quotient

This gate assembles the already constructed static scalar, Robin junction and
PT-symmetric LL Hessian operators as one block-diagonal operator.  It does not
include metric, gauge or ghost blocks and is not the full Candidate-A Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

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
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D

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

/-- Product of the three completed reduced bosonic form spaces. -/
abbrev ReducedBosonicJacobiSpace
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :=
  StaticScalarEnergyH1 period hPeriod scalarData ×
    (ThroatScalarL2 period hPeriod robinMeasure ×
      LLH1Space period hPeriod llData)

/-- The concrete block-diagonal sum of the three natural Hessian operators. -/
def reducedBosonicJacobiOperator
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData →L[Real]
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData :=
  (completedStaticScalarJacobiOperator period hPeriod scalarData).prodMap
    ((robinL2HessianOperator period hPeriod kPlus kMinus robinMeasure).prodMap
      (completedLLJacobiOperator period hPeriod llData))

@[simp]
theorem reducedBosonicJacobiOperator_apply
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (field : ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData) :
    reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        robinMeasure llData field =
      (completedStaticScalarJacobiOperator period hPeriod scalarData field.1,
        (robinL2HessianOperator period hPeriod kPlus kMinus robinMeasure
            field.2.1,
          completedLLJacobiOperator period hPeriod llData field.2.2)) :=
  rfl

/-- The operator pairing is the sum of the three completed natural Hessian
pairings. -/
def reducedBosonicNaturalHessian
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (first second :
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData) :
    Real :=
  inner Real
      (completedStaticScalarJacobiOperator period hPeriod scalarData first.1)
      second.1 +
    inner Real
      (robinL2HessianOperator period hPeriod kPlus kMinus robinMeasure first.2.1)
      second.2.1 +
    inner Real (completedLLJacobiOperator period hPeriod llData first.2.2)
      second.2.2

/-- The sum of the three completed natural Hessian pairings is symmetric. -/
theorem reducedBosonicNaturalHessian_comm
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (first second :
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData) :
    reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData first second =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData second first := by
  unfold reducedBosonicNaturalHessian
  rw [completedStaticScalarJacobiOperator_isSymmetric,
    robinL2HessianOperator_isSymmetric,
    completedLLJacobiOperator_isSymmetric]
  simp only [real_inner_comm]

/-- On the three smooth dense sectors, the assembled pairing is exactly the
sum of the already constructed action Hessians. -/
theorem reducedBosonicNaturalHessian_smooth_eq
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (scalarFirst scalarSecond :
      StaticGlobalScalarTest period hPeriod scalarData)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarFirst,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData scalarSecond,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond) =
      globalHolonomicScalarJacobiForm period hPeriod scalarData.formData
          scalarFirst.toField scalarSecond.toField +
        robinHessian period hPeriod kPlus kMinus robinFirst robinSecond
          robinMeasure +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          (finiteSmoothThroatGeneratingFrame period hPeriod) llData.fields
          llFirst.toTest llSecond.toTest llData.mu := by
  unfold reducedBosonicNaturalHessian
  rw [completedStaticScalarJacobiOperator_smooth_pairing,
    robinL2HessianOperator_smooth_pairing,
    completedLLJacobiOperator_smooth_pairing]

theorem reducedBosonicJacobiOperator_injective
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Injective
      (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        robinMeasure llData) := by
  intro first second hEqual
  have hScalar := congrArg Prod.fst hEqual
  change completedStaticScalarJacobiOperator period hPeriod scalarData first.1 =
      completedStaticScalarJacobiOperator period hPeriod scalarData second.1 at hScalar
  have hRobin := congrArg (fun field => field.2.1) hEqual
  change robinL2HessianOperator period hPeriod kPlus kMinus robinMeasure
      first.2.1 = robinL2HessianOperator period hPeriod kPlus kMinus
        robinMeasure second.2.1 at hRobin
  have hLL := congrArg (fun field => field.2.2) hEqual
  change completedLLJacobiOperator period hPeriod llData first.2.2 =
      completedLLJacobiOperator period hPeriod llData second.2.2 at hLL
  apply Prod.ext
  · exact completedStaticScalarJacobiOperator_injective period hPeriod scalarData
      hScalar
  · apply Prod.ext
    · exact robinL2HessianOperator_injective period hPeriod kPlus kMinus
        hCoupling robinMeasure hRobin
    · exact completedLLJacobiOperator_injective period hPeriod llData
        hLL

theorem reducedBosonicJacobiOperator_surjective
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Surjective
      (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        robinMeasure llData) := by
  rintro ⟨scalar, robin, ll⟩
  obtain ⟨scalarPreimage, hScalar⟩ :=
    completedStaticScalarJacobiOperator_surjective period hPeriod scalarData scalar
  obtain ⟨robinPreimage, hRobin⟩ :=
    robinL2HessianOperator_surjective period hPeriod kPlus kMinus hCoupling
      robinMeasure robin
  obtain ⟨llPreimage, hLL⟩ :=
    completedLLJacobiOperator_surjective period hPeriod llData ll
  refine ⟨(scalarPreimage, robinPreimage, llPreimage), ?_⟩
  apply Prod.ext
  · exact hScalar
  · apply Prod.ext
    · exact hRobin
    · exact hLL

theorem reducedBosonicJacobiOperator_ker_eq_bot
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    LinearMap.ker
        (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
          robinMeasure llData).toLinearMap = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (reducedBosonicJacobiOperator_injective period hPeriod scalarData kPlus
      kMinus hCoupling robinMeasure llData)

theorem reducedBosonicJacobiOperator_range_eq_top
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    LinearMap.range
        (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
          robinMeasure llData).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr
    (reducedBosonicJacobiOperator_surjective period hPeriod scalarData kPlus
      kMinus hCoupling robinMeasure llData)

theorem reducedBosonicJacobiOperator_range_isClosed
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    IsClosed
      (LinearMap.range
        (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
          robinMeasure llData).toLinearMap :
        Set (ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure
          llData)) := by
  rw [reducedBosonicJacobiOperator_range_eq_top period hPeriod scalarData
    kPlus kMinus hCoupling robinMeasure llData]
  exact isClosed_univ

def reducedBosonicJacobiIndex
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) : Int :=
  (reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
    robinMeasure llData).toLinearMap.index

theorem reducedBosonicJacobiIndex_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    reducedBosonicJacobiIndex period hPeriod scalarData kPlus kMinus
      robinMeasure llData = 0 := by
  unfold reducedBosonicJacobiIndex
  rw [LinearMap.index_of_surjective
      (reducedBosonicJacobiOperator_surjective period hPeriod scalarData kPlus
        kMinus hCoupling robinMeasure llData),
    reducedBosonicJacobiOperator_ker_eq_bot period hPeriod scalarData kPlus
      kMinus hCoupling robinMeasure llData]
  simp

end

end P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
end JanusFormal
