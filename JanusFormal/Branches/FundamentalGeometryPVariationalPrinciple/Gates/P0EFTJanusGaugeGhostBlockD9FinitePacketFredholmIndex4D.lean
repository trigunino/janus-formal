import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketFredholmIndex4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
open P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- Cokernel of the actual finite block-diagonal packet operator. -/
abbrev D9GaugeGhostFinitePacketCokernel {ι : Type*}
    (covector : ι → TangentVector3) :=
  D9GaugeGhostFinitePacket ι ⧸
    LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)

/-- Canonical projection to the packet cokernel. -/
def d9GaugeGhostFinitePacketCokernelProjection {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real]
      D9GaugeGhostFinitePacketCokernel covector :=
  (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)).mkQ

/-- Fredholm-style index of the actual finite packet endomorphism. -/
def d9GaugeGhostFinitePacketOperatorIndex {ι : Type*} [Fintype ι]
    (covector : ι → TangentVector3) : Int :=
  (Module.finrank Real
      (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) : Int) -
    (Module.finrank Real
      (D9GaugeGhostFinitePacketCokernel covector) : Int)

/-- The kernel dimension is the dimension of the genuine zero-mode packet. -/
theorem d9GaugeGhostFinitePacketKernel_finrank_eq_zeroModeData
    {ι : Type*} (covector : ι → TangentVector3) :
    Module.finrank Real
        (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) =
      Module.finrank Real (D9GaugeGhostPacketZeroModeData covector) :=
  (d9GaugeGhostFinitePacketKernelEquivZeroModeData covector).finrank_eq

/-- Finite zero-mode data has the expected filtered multiplicity times the
one-block coordinate dimension.  The subtype `Fintype` is installed only
inside the proof, so no decidable equality on tangent covectors leaks into the
public statement. -/
theorem d9GaugeGhostPacketZeroModeData_finrank
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real (D9GaugeGhostPacketZeroModeData covector) =
      d9ZeroCovectorMultiplicity Finset.univ covector *
        Module.finrank Real D9GaugeGhostLinearCoordinate := by
  classical
  letI : Fintype (D9GaugeGhostPacketZeroMode covector) :=
    Fintype.ofFinite _
  have hCard :
      Fintype.card (D9GaugeGhostPacketZeroMode covector) =
        d9ZeroCovectorMultiplicity Finset.univ covector := by
    change Fintype.card {mode : ι // covector mode = zeroTangent} =
      (Finset.univ.filter fun mode : ι =>
        covector mode = zeroTangent).card
    exact Fintype.card_of_subtype
      (Finset.univ.filter fun mode : ι => covector mode = zeroTangent)
      (by
        intro mode
        simp)
  rw [Module.finrank_pi_fintype]
  simp [hCard]

private theorem d9GaugeGhostCoordinate_finrank_eq_zeroCokernelFinrank :
    Module.finrank Real D9GaugeGhostLinearCoordinate =
      d9GaugeGhostZeroCokernelFinrank := by
  unfold d9GaugeGhostZeroCokernelFinrank
  exact d9GaugeGhostBlock_zero_cokernel_finrank.symm

/-- Exact nullity formula for the actual block-diagonal operator. -/
theorem d9GaugeGhostFinitePacketKernel_finrank_eq_zeroMultiplicity_mul
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real
        (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) =
      d9ZeroCovectorMultiplicity Finset.univ covector *
        d9GaugeGhostZeroCokernelFinrank := by
  calc
    Module.finrank Real
        (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) =
        Module.finrank Real (D9GaugeGhostPacketZeroModeData covector) :=
      d9GaugeGhostFinitePacketKernel_finrank_eq_zeroModeData covector
    _ = d9ZeroCovectorMultiplicity Finset.univ covector *
        Module.finrank Real D9GaugeGhostLinearCoordinate :=
      d9GaugeGhostPacketZeroModeData_finrank covector
    _ = d9ZeroCovectorMultiplicity Finset.univ covector *
        d9GaugeGhostZeroCokernelFinrank := by
      rw [d9GaugeGhostCoordinate_finrank_eq_zeroCokernelFinrank]

/-- Since the packet symbol is an endomorphism of a finite-dimensional space,
its kernel and cokernel have equal dimension. -/
theorem d9GaugeGhostFinitePacketKernel_finrank_eq_cokernel_finrank
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real
        (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) =
      Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) := by
  have hRankNullity :
      Module.finrank Real
          (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)) +
        Module.finrank Real
          (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) =
      Module.finrank Real (D9GaugeGhostFinitePacket ι) :=
    LinearMap.finrank_range_add_finrank_ker
      (d9GaugeGhostFinitePacketSymbol covector)
  have hQuotient :
      Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) +
        Module.finrank Real
          (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)) =
      Module.finrank Real (D9GaugeGhostFinitePacket ι) :=
    (LinearMap.range
      (d9GaugeGhostFinitePacketSymbol covector)).finrank_quotient_add_finrank
  omega

/-- Exact cokernel formula for the actual finite packet operator. -/
theorem d9GaugeGhostFinitePacketCokernel_finrank_eq_zeroMultiplicity_mul
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) =
      d9ZeroCovectorMultiplicity Finset.univ covector *
        d9GaugeGhostZeroCokernelFinrank := by
  calc
    Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) =
        Module.finrank Real
          (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) :=
      (d9GaugeGhostFinitePacketKernel_finrank_eq_cokernel_finrank
        covector).symm
    _ = d9ZeroCovectorMultiplicity Finset.univ covector *
        d9GaugeGhostZeroCokernelFinrank :=
      d9GaugeGhostFinitePacketKernel_finrank_eq_zeroMultiplicity_mul covector

/-- The cokernel of the genuine packet operator matches the earlier sum of
pointwise cokernel dimensions over all finite modes. -/
theorem d9GaugeGhostFinitePacketCokernel_finrank_eq_pointwise_sum
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) =
      d9GaugeGhostFiniteCokernelFinrank Finset.univ covector := by
  calc
    Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) =
        d9ZeroCovectorMultiplicity Finset.univ covector *
          d9GaugeGhostZeroCokernelFinrank :=
      d9GaugeGhostFinitePacketCokernel_finrank_eq_zeroMultiplicity_mul covector
    _ = d9GaugeGhostFiniteCokernelFinrank Finset.univ covector :=
      (d9GaugeGhostFiniteCokernelFinrank_eq_zeroMultiplicity_mul
        Finset.univ covector).symm

/-- The actual finite block-diagonal packet operator has Fredholm index zero
for every mixture of zero and nonzero principal covectors. -/
theorem d9GaugeGhostFinitePacketOperatorIndex_zero
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    d9GaugeGhostFinitePacketOperatorIndex covector = 0 := by
  rw [d9GaugeGhostFinitePacketOperatorIndex,
    d9GaugeGhostFinitePacketKernel_finrank_eq_cokernel_finrank covector]
  omega

/-- If every mode has nonzero covector, the actual packet cokernel is trivial. -/
theorem d9GaugeGhostFinitePacketCokernel_eq_zero_of_nonzero
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent)
    (cokernel : D9GaugeGhostFinitePacketCokernel covector) :
    cokernel = 0 := by
  obtain ⟨packet, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)) cokernel
  change (Submodule.Quotient.mk packet :
    D9GaugeGhostFinitePacketCokernel covector) = 0
  rw [Submodule.Quotient.mk_eq_zero,
    d9GaugeGhostFinitePacketSymbol_range_eq_top_of_nonzero
      covector hNonzero]
  trivial

/-- All-nonzero finite packets are operator-level exact: zero kernel, total
range, trivial cokernel and zero index. -/
theorem d9GaugeGhostFinitePacket_nonzero_exactness_certificate
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent) :
    LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) = ⊥ ∧
      LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) = ⊤ ∧
      (∀ cokernel : D9GaugeGhostFinitePacketCokernel covector,
        cokernel = 0) ∧
      d9GaugeGhostFinitePacketOperatorIndex covector = 0 := by
  exact ⟨d9GaugeGhostFinitePacketSymbol_ker_eq_bot_of_nonzero
      covector hNonzero,
    d9GaugeGhostFinitePacketSymbol_range_eq_top_of_nonzero
      covector hNonzero,
    d9GaugeGhostFinitePacketCokernel_eq_zero_of_nonzero
      covector hNonzero,
    d9GaugeGhostFinitePacketOperatorIndex_zero covector⟩

/-- Full closure certificate connecting the genuine operator to the earlier
pointwise finite-multiplicity accounting. -/
theorem d9GaugeGhostFinitePacketFredholm_certificate
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real
        (LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) =
        d9ZeroCovectorMultiplicity Finset.univ covector *
          d9GaugeGhostZeroCokernelFinrank ∧
      Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) =
        d9ZeroCovectorMultiplicity Finset.univ covector *
          d9GaugeGhostZeroCokernelFinrank ∧
      Module.finrank Real (D9GaugeGhostFinitePacketCokernel covector) =
        d9GaugeGhostFiniteCokernelFinrank Finset.univ covector ∧
      d9GaugeGhostFinitePacketOperatorIndex covector = 0 := by
  exact ⟨d9GaugeGhostFinitePacketKernel_finrank_eq_zeroMultiplicity_mul
      covector,
    d9GaugeGhostFinitePacketCokernel_finrank_eq_zeroMultiplicity_mul
      covector,
    d9GaugeGhostFinitePacketCokernel_finrank_eq_pointwise_sum covector,
    d9GaugeGhostFinitePacketOperatorIndex_zero covector⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketFredholmIndex4D
end JanusFormal
