import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitAdditivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinHessianExplicitLinearity4D

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
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem matterVariationComponentFamily_addDirection
    (x y : FullMatterRobinLLDirections period hPeriod) :
    matterVariationComponentFamily period hPeriod (addDirection period hPeriod x y).common.matter =
      matterVariationComponentFamily period hPeriod x.common.matter +
        matterVariationComponentFamily period hPeriod y.common.matter := by
  funext component
  ext point
  unfold matterVariationComponentFamily addDirection
  by_cases h : component.1 = 0
  · simp only [h, if_true, Pi.add_apply]
    exact map_add (EuclideanSpace.proj component.2) _ _
  · simp only [h, if_false, Pi.add_apply]
    exact map_add (EuclideanSpace.proj component.2) _ _

theorem matterVariationComponentFamily_negDirection
    (x : FullMatterRobinLLDirections period hPeriod) :
    matterVariationComponentFamily period hPeriod (negDirection period hPeriod x).common.matter =
      -matterVariationComponentFamily period hPeriod x.common.matter := by
  funext component
  ext point
  unfold matterVariationComponentFamily negDirection
  by_cases h : component.1 = 0
  · simp only [h, if_true, Pi.neg_apply]
    exact map_neg (EuclideanSpace.proj component.2) _
  · simp only [h, if_false, Pi.neg_apply]
    exact map_neg (EuclideanSpace.proj component.2) _

@[simp] theorem addDirection_robin
    (x y : FullMatterRobinLLDirections period hPeriod) :
    (addDirection period hPeriod x y).robin = x.robin + y.robin := rfl

@[simp] theorem negDirection_robin
    (x : FullMatterRobinLLDirections period hPeriod) :
    (negDirection period hPeriod x).robin = -x.robin := rfl

theorem globalMatterMultipletHessian_add_first
    (data : MatterMultipletActionData period hPeriod)
    (x y z : FullMatterRobinLLDirections period hPeriod) :
    globalMatterMultipletHessian period hPeriod data
        (matterVariationComponentFamily period hPeriod (addDirection period hPeriod x y).common.matter)
        (matterVariationComponentFamily period hPeriod z.common.matter) =
      globalMatterMultipletHessian period hPeriod data
          (matterVariationComponentFamily period hPeriod x.common.matter)
          (matterVariationComponentFamily period hPeriod z.common.matter) +
        globalMatterMultipletHessian period hPeriod data
          (matterVariationComponentFamily period hPeriod y.common.matter)
          (matterVariationComponentFamily period hPeriod z.common.matter) := by
  rw [matterVariationComponentFamily_addDirection]
  unfold globalMatterMultipletHessian
  simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.map_add]
  rw [Finset.sum_add_distrib]

theorem globalMatterMultipletHessian_neg_first
    (data : MatterMultipletActionData period hPeriod)
    (x z : FullMatterRobinLLDirections period hPeriod) :
    globalMatterMultipletHessian period hPeriod data
        (matterVariationComponentFamily period hPeriod (negDirection period hPeriod x).common.matter)
        (matterVariationComponentFamily period hPeriod z.common.matter) =
      -globalMatterMultipletHessian period hPeriod data
        (matterVariationComponentFamily period hPeriod x.common.matter)
        (matterVariationComponentFamily period hPeriod z.common.matter) := by
  rw [matterVariationComponentFamily_negDirection]
  unfold globalMatterMultipletHessian
  simp

theorem robinHessian_add_first
    (kPlus kMinus : Real) (x y z : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    robinHessian period hPeriod kPlus kMinus (addDirection period hPeriod x y).robin z.robin mu =
      robinHessian period hPeriod kPlus kMinus x.robin z.robin mu +
        robinHessian period hPeriod kPlus kMinus y.robin z.robin mu := by
  change robinHessianBilinear period hPeriod kPlus kMinus mu (x.robin + y.robin) z.robin = _
  simp

theorem robinHessian_neg_first
    (kPlus kMinus : Real) (x z : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    robinHessian period hPeriod kPlus kMinus (negDirection period hPeriod x).robin z.robin mu =
      -robinHessian period hPeriod kPlus kMinus x.robin z.robin mu := by
  change robinHessianBilinear period hPeriod kPlus kMinus mu (-x.robin) z.robin = _
  simp

end
end P0EFTJanusMatterRobinHessianExplicitLinearity4D
end JanusFormal
