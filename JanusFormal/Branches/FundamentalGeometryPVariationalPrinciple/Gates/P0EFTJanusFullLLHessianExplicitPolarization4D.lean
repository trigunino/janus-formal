import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitAdditivity4D

namespace JanusFormal
namespace P0EFTJanusFullLLHessianExplicitPolarization4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def subDirection (x y : FullMatterRobinLLDirections period hPeriod) :
    FullMatterRobinLLDirections period hPeriod :=
  addDirection period hPeriod x (negDirection period hPeriod y)

theorem fullLLHessian_add_second
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (x y z : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    fullLLHessian period hPeriod frame fields x (addDirection period hPeriod y z) mu =
      fullLLHessian period hPeriod frame fields x y mu +
        fullLLHessian period hPeriod frame fields x z mu := by
  rw [fullLLHessian_symmetric period hPeriod frame fields x
    (addDirection period hPeriod y z) mu]
  rw [fullLLHessian_add_first]
  rw [fullLLHessian_symmetric period hPeriod frame fields y x mu,
    fullLLHessian_symmetric period hPeriod frame fields z x mu]

theorem fullLLHessian_neg_second
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    fullLLHessian period hPeriod frame fields x (negDirection period hPeriod y) mu =
      -fullLLHessian period hPeriod frame fields x y mu := by
  rw [fullLLHessian_symmetric period hPeriod frame fields x
    (negDirection period hPeriod y) mu]
  rw [fullLLHessian_neg_first]
  rw [fullLLHessian_symmetric period hPeriod frame fields y x mu]

/-- Exact real polarization of the genuine full LL Hessian on explicitly
added/subtracted complete directions. -/
theorem fullLLHessian_polarization
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    fullLLHessian period hPeriod frame fields x y mu =
      (1 / 4 : Real) *
        (fullLLHessian period hPeriod frame fields
            (addDirection period hPeriod x y) (addDirection period hPeriod x y) mu -
          fullLLHessian period hPeriod frame fields
            (subDirection period hPeriod x y) (subDirection period hPeriod x y) mu) := by
  unfold subDirection
  rw [fullLLHessian_add_first, fullLLHessian_add_second,
    fullLLHessian_add_second]
  rw [fullLLHessian_add_first, fullLLHessian_add_second,
    fullLLHessian_add_second]
  rw [fullLLHessian_neg_first, fullLLHessian_neg_second,
    fullLLHessian_neg_second]
  rw [fullLLHessian_symmetric period hPeriod frame fields y x mu]
  rw [fullLLHessian_neg_first]
  ring

end
end P0EFTJanusFullLLHessianExplicitPolarization4D
end JanusFormal
