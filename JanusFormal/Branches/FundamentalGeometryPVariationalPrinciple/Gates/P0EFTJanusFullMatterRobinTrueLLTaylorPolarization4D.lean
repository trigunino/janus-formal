import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinHessianExplicitLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitPolarization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D
open P0EFTJanusMatterRobinHessianExplicitLinearity4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem assembledHessian_add_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (x y z : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (addDirection period hPeriod x y) z =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x z +
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields y z := by
  have hll := fullLLHessian_add_first period hPeriod frame fields x y z llMeasure
  change globalPTFullLLHessianForm period hPeriod frame fields (addDirection period hPeriod x y) z llMeasure =
    globalPTFullLLHessianForm period hPeriod frame fields x z llMeasure +
      globalPTFullLLHessianForm period hPeriod frame fields y z llMeasure at hll
  unfold globalMatterRobinFullLLHessian
  rw [globalMatterMultipletHessian_add_first, robinHessian_add_first, hll]
  ring

theorem assembledHessian_neg_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (x z : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (negDirection period hPeriod x) z =
      -globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x z := by
  have hll := fullLLHessian_neg_first period hPeriod frame fields x z llMeasure
  change globalPTFullLLHessianForm period hPeriod frame fields (negDirection period hPeriod x) z llMeasure =
    -globalPTFullLLHessianForm period hPeriod frame fields x z llMeasure at hll
  unfold globalMatterRobinFullLLHessian
  rw [globalMatterMultipletHessian_neg_first, robinHessian_neg_first, hll]
  ring

theorem assembledHessian_add_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (x y z : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        x (addDirection period hPeriod y z) =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x y +
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x z := by
  rw [globalMatterRobinFullLLHessian_symmetric, assembledHessian_add_first,
    globalMatterRobinFullLLHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields y x,
    globalMatterRobinFullLLHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields z x]

theorem assembledHessian_neg_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        x (negDirection period hPeriod y) =
      -globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x y := by
  rw [globalMatterRobinFullLLHessian_symmetric, assembledHessian_neg_first,
    globalMatterRobinFullLLHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields y x]

theorem assembledHessian_polarization
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x y =
      (1 / 4 : Real) *
        (globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (addDirection period hPeriod x y) (addDirection period hPeriod x y) -
         globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (subDirection period hPeriod x y) (subDirection period hPeriod x y)) := by
  unfold subDirection
  rw [assembledHessian_add_first, assembledHessian_add_second, assembledHessian_add_second]
  rw [assembledHessian_add_first, assembledHessian_add_second, assembledHessian_add_second]
  rw [assembledHessian_neg_first, assembledHessian_neg_second, assembledHessian_neg_second]
  rw [globalMatterRobinFullLLHessian_symmetric period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields y x, assembledHessian_neg_first]
  ring

theorem assembledHessian_eq_difference_C2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x y =
      (1 / 2 : Real) *
        (fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (addDirection period hPeriod x y) -
         fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (subDirection period hPeriod x y)) := by
  have hp := assembledHessian_polarization period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields x y
  have hcPlus := fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (addDirection period hPeriod x y)
  have hcMinus := fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (subDirection period hPeriod x y)
  linarith

end
end P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D
end JanusFormal
