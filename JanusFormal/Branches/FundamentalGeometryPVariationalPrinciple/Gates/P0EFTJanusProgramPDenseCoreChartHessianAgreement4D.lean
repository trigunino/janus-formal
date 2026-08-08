import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D

/-!
# Exact agreement between a displayed core Hessian and a finite chart sum

The graph-norm estimate is useful only when the finite chart sum is identified
with the actual Hessian retained by the variational construction.  This file
stores that equality and turns it into the standard product-bound packet.

For Candidate-A the target is the six-block non-Robin remainder.  Its equality
with the interaction, two Einstein--Hilbert, two Maxwell and finite-BV chart
Hessians is the only algebraic specialization needed before the existing H11
dense extension is invoked.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDenseCoreChartHessianAgreement4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D

variable {Core Hilbert Chart Block : Type*}
  [NormedAddCommGroup Core] [NormedSpace Real Core]
  [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]
  [NormedAddCommGroup Chart] [NormedSpace Real Chart]
  [Fintype Block] [DecidableEq Block]

/-- Standard product estimate on a displayed core bilinear form. -/
structure DenseCoreBilinearProductBound
    (embedding : Core →ₗ[Real] Hilbert)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real) : Prop where
  constant : Real
  constant_nonneg : 0 ≤ constant
  estimate : ∀ first second,
    ‖target first second‖ ≤
      constant * ‖embedding first‖ * ‖embedding second‖

/-- Identification of one actual core Hessian with a finite family of true
chart Hessians. -/
structure DenseCoreFiniteChartHessianAgreement
    (chartMap : Core →ₗ[Real] Chart)
    (form : Block → Chart →L[Real] Chart →L[Real] Real)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real) : Prop where
  target_eq : target = denseCoreFiniteChartHessianSum chartMap form

/-- Exact chart agreement plus one chart-map bound produces the product bound
consumed by completion. -/
def DenseCoreFiniteChartHessianAgreement.toProductBound
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Block → Chart →L[Real] Chart →L[Real] Real)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : DenseCoreFiniteChartHessianAgreement chartMap form target) :
    DenseCoreBilinearProductBound embedding target where
  constant := (∑ block : Block, ‖form block‖) * bound.constant ^ 2
  constant_nonneg :=
    denseCoreFiniteChartHessianSum_constant_nonneg bound form
  estimate := by
    intro first second
    rw [agreement.target_eq]
    exact denseCoreFiniteChartHessianSum_bound embedding chartMap bound form
      first second

/-- The product constant is canonical for the chosen finite chart family. -/
@[simp]
theorem DenseCoreFiniteChartHessianAgreement.toProductBound_constant
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Block → Chart →L[Real] Chart →L[Real] Real)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : DenseCoreFiniteChartHessianAgreement chartMap form target) :
    (agreement.toProductBound embedding chartMap bound form target).constant =
      (∑ block : Block, ‖form block‖) * bound.constant ^ 2 :=
  rfl

/-- Public exact-agreement checkpoint. -/
theorem dense_core_chart_hessian_agreement_gate
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (bound : DenseCoreChartMapBound embedding chartMap)
    (form : Block → Chart →L[Real] Chart →L[Real] Real)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : DenseCoreFiniteChartHessianAgreement chartMap form target) :
    DenseCoreBilinearProductBound embedding target :=
  agreement.toProductBound embedding chartMap bound form target

end
end P0EFTJanusProgramPDenseCoreChartHessianAgreement4D
end JanusFormal
