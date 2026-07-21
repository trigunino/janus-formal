import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2InversePolarization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianAdditivity4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem quotientHessian_activeQuotientAdd_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second third : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientAdd period hPeriod first second) third =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first third +
        quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          second third := by
  let x := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod first)
  let y := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod second)
  let z := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod third)
  have h := assembledHessian_add_first period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields x y z
  rw [← quotientHessian_mk, ← quotientHessian_mk, ← quotientHessian_mk] at h
  rw [activeRepresentative_class period hPeriod first,
    activeRepresentative_class period hPeriod second,
    activeRepresentative_class period hPeriod third] at h
  simpa [activeQuotientAdd, x, y, z] using h

theorem quotientHessian_activeQuotientAdd_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second third : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first (activeQuotientAdd period hPeriod second third) =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first second +
        quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first third := by
  rw [quotientHessian_symmetric,
    quotientHessian_activeQuotientAdd_first,
    quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields second first,
    quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields third first]

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianAdditivity4D
end JanusFormal
