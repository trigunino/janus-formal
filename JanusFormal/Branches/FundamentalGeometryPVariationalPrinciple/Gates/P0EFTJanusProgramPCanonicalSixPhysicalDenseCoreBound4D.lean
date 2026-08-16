import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDenseCoreChartHessianAgreement4D

/-!
# Dense-core bound for the canonical six physical Hessians

The earlier finite-chart theorem accepted an arbitrary finite family of
bilinear forms.  For Candidate-A that freedom is unnecessary: the six forms
are the genuine second Frechet derivatives of the six scalar action fields.
This file fixes that family canonically and leaves only the graph-norm estimate
for the smooth-core chart map and the exact core agreement with the displayed
physical remainder.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCanonicalSixPhysicalDenseCoreBound4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
open P0EFTJanusProgramPDenseCoreChartHessianAgreement4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

universe u

variable {Core Hilbert Chart : Type*}
  [NormedAddCommGroup Core] [NormedSpace Real Core]
  [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]
  [NormedAddCommGroup Chart] [NormedSpace Real Chart]

/-- Indexed canonical family used by the existing finite-sum estimate. -/
def canonicalSixPhysicalIndexedHessian
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart) :
    CanonicalSixPhysicalBlock → Chart →L[Real] Chart →L[Real] Real :=
  fun block => canonicalSixPhysicalBlockHessian blocks block point

/-- Finite dense-core pullback of the six canonical chart Hessians. -/
def canonicalSixPhysicalDenseCoreSum
    (chartMap : Core →ₗ[Real] Chart)
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart) :
    Core →ₗ[Real] Core →ₗ[Real] Real :=
  denseCoreFiniteChartHessianSum chartMap
    (canonicalSixPhysicalIndexedHessian blocks point)

/-- The finite indexed presentation is the explicit six-term Hessian sum. -/
theorem canonicalSixPhysicalIndexedHessian_sum_eq
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart) :
    (∑ block : CanonicalSixPhysicalBlock,
      canonicalSixPhysicalIndexedHessian blocks point block) =
        canonicalSixPhysicalHessianSum blocks point := by
  simp [canonicalSixPhysicalIndexedHessian,
    canonicalSixPhysicalHessianSum,
    canonicalSixPhysicalBlockHessian,
    canonicalSixPhysicalBlockAction]

/-- Exact identification of one displayed core form with the canonical six
physical Hessians.  No bilinear form is stored in this packet. -/
structure CanonicalSixPhysicalDenseCoreAgreement
    (chartMap : Core →ₗ[Real] Chart)
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real) : Prop where
  target_eq : target =
    canonicalSixPhysicalDenseCoreSum chartMap blocks point

/-- Convert canonical six-block agreement into the generic agreement packet. -/
def CanonicalSixPhysicalDenseCoreAgreement.toFiniteAgreement
    (chartMap : Core →ₗ[Real] Chart)
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : CanonicalSixPhysicalDenseCoreAgreement
      chartMap blocks point target) :
    DenseCoreFiniteChartHessianAgreement chartMap
      (canonicalSixPhysicalIndexedHessian blocks point) target where
  target_eq := agreement.target_eq

/-- One graph-norm estimate on the genuine chart map now controls the canonical
six-block physical remainder. -/
def CanonicalSixPhysicalDenseCoreAgreement.toProductBound
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (chartBound : DenseCoreChartMapBound embedding chartMap)
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : CanonicalSixPhysicalDenseCoreAgreement
      chartMap blocks point target) :
    DenseCoreBilinearProductBound embedding target :=
  (agreement.toFiniteAgreement chartMap blocks point target).toProductBound
    embedding chartMap chartBound
      (canonicalSixPhysicalIndexedHessian blocks point) target

/-- The resulting constant is the sum of the six true chart-Hessian norms,
multiplied by the square of the core-to-chart bound. -/
@[simp]
theorem CanonicalSixPhysicalDenseCoreAgreement.toProductBound_constant
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (chartBound : DenseCoreChartMapBound embedding chartMap)
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : CanonicalSixPhysicalDenseCoreAgreement
      chartMap blocks point target) :
    (agreement.toProductBound embedding chartMap chartBound blocks point
      target).constant =
      (∑ block : CanonicalSixPhysicalBlock,
        ‖canonicalSixPhysicalBlockHessian blocks block point‖) *
          chartBound.constant ^ 2 :=
  rfl

/-- Public checkpoint for the canonical, non-arbitrary H11 six-block bound. -/
theorem canonical_six_physical_dense_core_bound_gate
    (embedding : Core →ₗ[Real] Hilbert)
    (chartMap : Core →ₗ[Real] Chart)
    (chartBound : DenseCoreChartMapBound embedding chartMap)
    (blocks : FullCoupledActionBlocks Chart)
    (point : Chart)
    (target : Core →ₗ[Real] Core →ₗ[Real] Real)
    (agreement : CanonicalSixPhysicalDenseCoreAgreement
      chartMap blocks point target) :
    DenseCoreBilinearProductBound embedding target :=
  agreement.toProductBound embedding chartMap chartBound blocks point target

end
end P0EFTJanusProgramPCanonicalSixPhysicalDenseCoreBound4D
end JanusFormal
