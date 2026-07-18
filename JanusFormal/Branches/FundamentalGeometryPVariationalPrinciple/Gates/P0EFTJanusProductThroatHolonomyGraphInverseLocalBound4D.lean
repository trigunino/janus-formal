import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D

/-!
# Local uniform bound for the inverse common-graph family

Operator-norm continuity implies that the inverse norms are uniformly bounded
on a neighborhood of every real holonomy.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphInverseLocalBound4D

set_option autoImplicit false

noncomputable section

open Filter
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D
open scoped Topology

theorem productThroatCommonGraphDiracInverse_norm_isBoundedUnder
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    (𝓝 holonomy).IsBoundedUnder (· ≤ ·)
      (fun parameter =>
        ‖productThroatCommonGraphDiracInverseCLM
          data fold reference parameter‖) :=
  (productThroatCommonGraphDiracInverse_continuousAt
    data fold reference holonomy).norm.isBoundedUnder_le

end


end P0EFTJanusProductThroatHolonomyGraphInverseLocalBound4D
end JanusFormal
