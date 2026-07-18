import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

/-!
# Hilbert direct sum for the reduced bosonic D8 Hessian

The three completed scalar, Robin and LL sectors are assembled with the true
`L²` product norm.  The block operator is therefore a bounded self-adjoint
Fredholm operator on a genuine Hilbert space.  Metric, gauge and ghost blocks
remain outside this reduced construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusReducedBosonicHilbertFredholmHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff InnerProduct InnerProductSpace ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D

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

/-- Genuine three-block Hilbert sum with the nested `L²` product norm. -/
abbrev ReducedBosonicHilbertSpace
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :=
  WithLp 2
    (StaticScalarEnergyH1 period hPeriod scalarData ×
      WithLp 2
        (ThroatScalarL2 period hPeriod robinMeasure ×
          LLH1Space period hPeriod llData))

/-- Forget the `L²` product wrappers while preserving all three components. -/
def reducedBosonicHilbertUnpack
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    ReducedBosonicHilbertSpace period hPeriod scalarData robinMeasure llData ≃L[Real]
      ReducedBosonicJacobiSpace period hPeriod scalarData robinMeasure llData :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (StaticScalarEnergyH1 period hPeriod scalarData)
      (WithLp 2
        (ThroatScalarL2 period hPeriod robinMeasure ×
          LLH1Space period hPeriod llData))).trans
    ((ContinuousLinearEquiv.refl Real
      (StaticScalarEnergyH1 period hPeriod scalarData)).prodCongr
        (WithLp.prodContinuousLinearEquiv 2 Real
          (ThroatScalarL2 period hPeriod robinMeasure)
          (LLH1Space period hPeriod llData)))

@[simp]
theorem reducedBosonicHilbertUnpack_apply
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (field : ReducedBosonicHilbertSpace period hPeriod scalarData robinMeasure
      llData) :
    reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure llData
        field =
      (field.fst, field.snd.fst, field.snd.snd) :=
  rfl

/-- The raw block operator conjugated onto the true Hilbert direct sum. -/
def reducedBosonicHilbertJacobiOperator
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    ReducedBosonicHilbertSpace period hPeriod scalarData robinMeasure llData →L[Real]
      ReducedBosonicHilbertSpace period hPeriod scalarData robinMeasure llData :=
  ((reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
    llData).symm.toContinuousLinearMap).comp
      ((reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        robinMeasure llData).comp
          (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
            llData).toContinuousLinearMap)

@[simp]
theorem reducedBosonicHilbertUnpack_operator
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (field : ReducedBosonicHilbertSpace period hPeriod scalarData robinMeasure
      llData) :
    reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure llData
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData field) =
      reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData field) := by
  simp [reducedBosonicHilbertJacobiOperator]

/-- The Hilbert pairing is exactly the previously assembled sum of the three
natural Hessian pairings. -/
theorem reducedBosonicHilbertJacobiOperator_pairing
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod)
    (first second : ReducedBosonicHilbertSpace period hPeriod scalarData
      robinMeasure llData) :
    inner Real
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first) second =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData first)
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData second) := by
  have hOperator := reducedBosonicHilbertUnpack_operator period hPeriod
    scalarData kPlus kMinus robinMeasure llData first
  change
    ((reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).fst,
      ((reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).snd.fst,
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).snd.snd)) =
      (first.fst, ((kPlus + kMinus) • first.snd.fst, first.snd.snd)) at hOperator
  have hScalar :
      (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).fst = first.fst := by
    simpa using congrArg Prod.fst hOperator
  have hRobin :
      (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).snd.fst =
        (kPlus + kMinus) • first.snd.fst := by
    simpa using congrArg (fun field => field.2.1) hOperator
  have hLL :
      (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).snd.snd = first.snd.snd := by
    simpa using congrArg (fun field => field.2.2) hOperator
  unfold reducedBosonicNaturalHessian
  simp only [WithLp.prod_inner_apply, reducedBosonicHilbertUnpack_apply]
  change
    inner Real
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first).fst second.fst +
      (inner Real
          (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
            kMinus robinMeasure llData first).snd.fst second.snd.fst +
        inner Real
          (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
            kMinus robinMeasure llData first).snd.snd second.snd.snd) =
      inner Real
          (completedStaticScalarJacobiOperator period hPeriod scalarData
            first.fst) second.fst +
        inner Real ((kPlus + kMinus) • first.snd.fst) second.snd.fst +
        inner Real
          (completedLLJacobiOperator period hPeriod llData first.snd.snd)
          second.snd.snd
  rw [hScalar, hRobin, hLL]
  simp only [completedStaticScalarJacobiOperator_apply,
    completedLLJacobiOperator_apply]
  ring

theorem reducedBosonicHilbertJacobiOperator_isSelfAdjoint
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint
      (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
        kMinus robinMeasure llData) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  calc
    inner Real
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData first) second =
      reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData first)
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData second) :=
      reducedBosonicHilbertJacobiOperator_pairing period hPeriod scalarData
        kPlus kMinus robinMeasure llData first second
    _ = reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
        robinMeasure llData
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData second)
        (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
          llData first) :=
      reducedBosonicNaturalHessian_comm period hPeriod scalarData kPlus
        kMinus robinMeasure llData _ _
    _ = inner Real
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData second) first :=
      (reducedBosonicHilbertJacobiOperator_pairing period hPeriod scalarData
        kPlus kMinus robinMeasure llData second first).symm
    _ = inner Real first
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData second) := real_inner_comm _ _

theorem reducedBosonicHilbertJacobiOperator_injective
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Injective
      (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
        kMinus robinMeasure llData) := by
  intro first second hEqual
  apply (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
    llData).injective
  apply reducedBosonicJacobiOperator_injective period hPeriod scalarData kPlus
    kMinus hCoupling robinMeasure llData
  simpa only [reducedBosonicHilbertUnpack_operator] using congrArg
    (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure llData)
    hEqual

theorem reducedBosonicHilbertJacobiOperator_surjective
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    Function.Surjective
      (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
        kMinus robinMeasure llData) := by
  intro target
  obtain ⟨preimage, hPreimage⟩ :=
    reducedBosonicJacobiOperator_surjective period hPeriod scalarData kPlus
      kMinus hCoupling robinMeasure llData
      (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure llData
        target)
  refine ⟨(reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
    llData).symm preimage, ?_⟩
  apply (reducedBosonicHilbertUnpack period hPeriod scalarData robinMeasure
    llData).injective
  simpa only [reducedBosonicHilbertUnpack_operator,
    ContinuousLinearEquiv.apply_symm_apply] using hPreimage

theorem reducedBosonicHilbertJacobiOperator_ker_eq_bot
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    LinearMap.ker
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData).toLinearMap = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (reducedBosonicHilbertJacobiOperator_injective period hPeriod scalarData
      kPlus kMinus hCoupling robinMeasure llData)

theorem reducedBosonicHilbertJacobiOperator_range_eq_top
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    LinearMap.range
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr
    (reducedBosonicHilbertJacobiOperator_surjective period hPeriod scalarData
      kPlus kMinus hCoupling robinMeasure llData)

theorem reducedBosonicHilbertJacobiOperator_range_isClosed
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    IsClosed
      (LinearMap.range
        (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus
          kMinus robinMeasure llData).toLinearMap :
        Set (ReducedBosonicHilbertSpace period hPeriod scalarData robinMeasure
          llData)) := by
  rw [reducedBosonicHilbertJacobiOperator_range_eq_top period hPeriod scalarData
    kPlus kMinus hCoupling robinMeasure llData]
  exact isClosed_univ

def reducedBosonicHilbertJacobiIndex
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) : Int :=
  (reducedBosonicHilbertJacobiOperator period hPeriod scalarData kPlus kMinus
    robinMeasure llData).toLinearMap.index

theorem reducedBosonicHilbertJacobiIndex_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (llData : PositiveLLH1Data period hPeriod) :
    reducedBosonicHilbertJacobiIndex period hPeriod scalarData kPlus kMinus
      robinMeasure llData = 0 := by
  unfold reducedBosonicHilbertJacobiIndex
  rw [LinearMap.index_of_surjective
      (reducedBosonicHilbertJacobiOperator_surjective period hPeriod scalarData
        kPlus kMinus hCoupling robinMeasure llData),
    reducedBosonicHilbertJacobiOperator_ker_eq_bot period hPeriod scalarData
      kPlus kMinus hCoupling robinMeasure llData]
  simp

end

end P0EFTJanusMappingTorusReducedBosonicHilbertFredholmHessian4D
end JanusFormal
