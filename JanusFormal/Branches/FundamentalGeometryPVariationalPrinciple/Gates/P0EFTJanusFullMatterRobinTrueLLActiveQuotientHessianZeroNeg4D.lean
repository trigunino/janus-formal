import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianAdditivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientEulerC2Additivity4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianZeroNeg4D

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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2InversePolarization4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianAdditivity4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientEulerC2Additivity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

private def zeroFullDirection : FullMatterRobinLLDirections period hPeriod :=
  {
    common := {
      metric := {
        plusLogDirection := 0
        minusLogDirection := 0
      }
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := 0
    }
    robin := 0
    llAuxMetric := 0
    llMeasure := 0
  }

/-- The zero active class, represented by the zero full direction. -/
def activeQuotientZero : ActiveQuotient period hPeriod :=
  ⟦zeroFullDirection period hPeriod⟧

/-- Canonical negation obtained from the chosen active representative. -/
def activeQuotientNeg (direction : ActiveQuotient period hPeriod) :
    ActiveQuotient period hPeriod :=
  ⟦negDirection period hPeriod
    (activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod direction))⟧

theorem quotientHessian_activeQuotientNeg_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientNeg period hPeriod first) second =
      -quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first second := by
  let x := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod first)
  let y := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod second)
  have h := assembledHessian_neg_first period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields x y
  rw [← quotientHessian_mk, ← quotientHessian_mk] at h
  rw [activeRepresentative_class period hPeriod first,
    activeRepresentative_class period hPeriod second] at h
  simpa [activeQuotientNeg, x, y] using h

theorem quotientHessian_activeQuotientNeg_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first (activeQuotientNeg period hPeriod second) =
      -quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first second := by
  rw [quotientHessian_symmetric, quotientHessian_activeQuotientNeg_first,
    quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields second first]

theorem quotientHessian_activeQuotientZero_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientZero period hPeriod) direction = 0 := by
  let y := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod direction)
  have h := assembledHessian_neg_first period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields (zeroFullDirection period hPeriod) y
  simp [zeroFullDirection, negDirection] at h
  rw [← quotientHessian_mk] at h
  dsimp [y] at h
  rw [activeRepresentative_class period hPeriod direction] at h
  have h' :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientZero period hPeriod) direction =
      -quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientZero period hPeriod) direction := by
    simpa [activeQuotientZero, zeroFullDirection] using h
  linarith

theorem quotientHessian_activeQuotientZero_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        direction (activeQuotientZero period hPeriod) = 0 := by
  rw [quotientHessian_symmetric, quotientHessian_activeQuotientZero_first]

theorem quotientHessian_activeQuotientSub_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second third : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientSub period hPeriod first second) third =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first third -
        quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          second third := by
  let x := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod first)
  let y := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod second)
  let z := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod third)
  have h := assembledHessian_add_first period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields x (negDirection period hPeriod y) z
  rw [assembledHessian_neg_first] at h
  rw [← quotientHessian_mk, ← quotientHessian_mk, ← quotientHessian_mk] at h
  rw [activeRepresentative_class period hPeriod first,
    activeRepresentative_class period hPeriod second,
    activeRepresentative_class period hPeriod third] at h
  simpa [activeQuotientSub, subDirection, x, y, z, sub_eq_add_neg] using h

theorem quotientHessian_activeQuotientSub_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second third : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first (activeQuotientSub period hPeriod second third) =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first second -
        quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first third := by
  rw [quotientHessian_symmetric, quotientHessian_activeQuotientSub_first,
    quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields second first,
    quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields third first]

theorem activeQuotientC2_neg
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientNeg period hPeriod direction) =
      activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        direction := by
  rw [activeQuotientC2_eq_half_Hessian, quotientHessian_activeQuotientNeg_first,
    quotientHessian_activeQuotientNeg_second, neg_neg,
    ← activeQuotientC2_eq_half_Hessian]

theorem activeQuotientC2_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientZero period hPeriod) = 0 := by
  rw [activeQuotientC2_eq_half_Hessian, quotientHessian_activeQuotientZero_first, mul_zero]

theorem activeQuotientC2_sub_exact_cross
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientSub period hPeriod first second) =
      activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first +
        activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields second -
        quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first second := by
  rw [activeQuotientC2_eq_half_Hessian,
    quotientHessian_activeQuotientSub_first,
    quotientHessian_activeQuotientSub_second,
    quotientHessian_activeQuotientSub_second,
    quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields second first,
    quotientHessian_diagonal_eq_two_activeQuotientC2,
    quotientHessian_diagonal_eq_two_activeQuotientC2]
  ring

theorem activeQuotientC2_parallelogram
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          (activeQuotientAdd period hPeriod first second) +
        activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          (activeQuotientSub period hPeriod first second) =
      2 * activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first +
        2 * activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          second := by
  rw [activeQuotientC2_add_exact_cross, activeQuotientC2_sub_exact_cross]
  ring

theorem quotientHessian_eq_half_C2_add_sub_difference
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first second =
      (activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          (activeQuotientAdd period hPeriod first second) -
        activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          (activeQuotientSub period hPeriod first second)) / 2 := by
  rw [activeQuotientC2_add_exact_cross, activeQuotientC2_sub_exact_cross]
  ring

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianZeroNeg4D
end JanusFormal
