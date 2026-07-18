import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusMonopoleSphereHeatTrace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatFiniteSectorFamilyTraceRegularity4D

/-!
# Infinite nuclear heat trace on the product throat

The already proved monopole-sphere heat series is combined with the concrete
circle nuclear expansion.  At every positive time the resulting series over
`ℕ × ℤ` is absolutely summable and its trace factors exactly as the product of
the sphere and circle traces.  PT preserves the full product trace.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatNuclearHeatTrace4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceClass

/-- Product coefficient for one monopole-sphere level and one circle Fourier
mode. -/
def productThroatNuclearHeatTerm
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) : Real :=
  sphereHeatTerm data time.1 index.1 *
    circleOperatorHeatWeight time fold twist index.2

theorem productThroatNuclearHeatTerm_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    0 ≤ productThroatNuclearHeatTerm data time fold twist index := by
  exact mul_nonneg
    (sphere_heat_term_nonnegative data time.1 index.1)
    (circleOperatorHeatWeight_nonnegative time fold twist index.2)

/-- Absolute summability of the genuine infinite product spectrum. -/
theorem productThroatNuclearHeatTerm_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (productThroatNuclearHeatTerm data time fold twist) := by
  apply (summable_prod_of_nonneg
    (productThroatNuclearHeatTerm_nonnegative data time fold twist)).2
  constructor
  · intro level
    exact (circleOperatorHeatWeight_summable time fold twist).mul_left
      (sphereHeatTerm data time.1 level)
  · have hSphere := sphere_heat_trace_summable data time.1 time.2
    have hScaled := hSphere.mul_right (circleHeatNuclearTrace time fold twist)
    exact hScaled.congr fun level => by
      unfold productThroatNuclearHeatTerm circleHeatNuclearTrace
      simp only [Prod.fst, Prod.snd]
      rw [tsum_mul_left]

/-- Infinite nuclear heat trace of the product throat. -/
def productThroatNuclearHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' index : Nat × Int,
    productThroatNuclearHeatTerm data time fold twist index

/-- Exact factorization into the monopole-sphere trace and the concrete circle
nuclear trace. -/
theorem productThroatNuclearHeatTrace_factorizes
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatNuclearHeatTrace data time fold twist =
      sphereHeatTrace data time.1 * circleHeatNuclearTrace time fold twist := by
  unfold productThroatNuclearHeatTrace
  rw [(productThroatNuclearHeatTerm_summable data time fold twist).tsum_prod]
  simp_rw [productThroatNuclearHeatTerm, tsum_mul_left]
  rw [tsum_mul_right]
  rfl

theorem productThroatNuclearHeatTrace_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    0 ≤ productThroatNuclearHeatTrace data time fold twist := by
  unfold productThroatNuclearHeatTrace
  exact tsum_nonneg
    (productThroatNuclearHeatTerm_nonnegative data time fold twist)

/-- PT preserves the complete infinite product-throat trace. -/
theorem productThroatNuclearHeatTrace_pt_eq_positive
    (data : ProductThroatSpectralData) (time : HeatTime)
    (twist : CircleTwist) :
    productThroatNuclearHeatTrace data time .pt twist =
      productThroatNuclearHeatTrace data time .positive twist := by
  rw [productThroatNuclearHeatTrace_factorizes,
    productThroatNuclearHeatTrace_factorizes,
    circleHeatNuclearTrace_pt_eq_positive]

end

end P0EFTJanusProductThroatNuclearHeatTrace4D
end JanusFormal
