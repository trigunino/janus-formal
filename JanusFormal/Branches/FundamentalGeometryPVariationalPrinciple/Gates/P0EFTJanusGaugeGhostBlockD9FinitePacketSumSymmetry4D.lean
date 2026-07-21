import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketDisjointSum4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketSumSymmetry4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketReindex4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketDisjointSum4D

/-- Exchange the two summands of a disjoint mode family. -/
def d9PacketSumSwapEquiv (ι κ : Type*) : Sum ι κ ≃ Sum κ ι where
  toFun value :=
    match value with
    | Sum.inl left => Sum.inr left
    | Sum.inr right => Sum.inl right
  invFun value :=
    match value with
    | Sum.inl right => Sum.inr right
    | Sum.inr left => Sum.inl left
  left_inv value := by
    cases value <;> rfl
  right_inv value := by
    cases value <;> rfl

@[simp] theorem d9PacketSumSwapEquiv_inl
    {ι κ : Type*} (mode : ι) :
    d9PacketSumSwapEquiv ι κ (Sum.inl mode) = Sum.inr mode := rfl

@[simp] theorem d9PacketSumSwapEquiv_inr
    {ι κ : Type*} (mode : κ) :
    d9PacketSumSwapEquiv ι κ (Sum.inr mode) = Sum.inl mode := rfl

/-- Relabel a linear packet by exchanging the two disjoint mode families. -/
def packetDisjointSumSwapLinearEquiv {ι κ V : Type*}
    [AddCommMonoid V] [Module Real V] :
    (Sum ι κ → V) ≃ₗ[Real] (Sum κ ι → V) :=
  packetReindexLinearEquiv (d9PacketSumSwapEquiv κ ι)

@[simp] theorem packetDisjointSumSwapLinearEquiv_inl_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum ι κ → V) (mode : κ) :
    packetDisjointSumSwapLinearEquiv packet (Sum.inl mode) =
      packet (Sum.inr mode) := rfl

@[simp] theorem packetDisjointSumSwapLinearEquiv_inr_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum ι κ → V) (mode : ι) :
    packetDisjointSumSwapLinearEquiv packet (Sum.inr mode) =
      packet (Sum.inl mode) := rfl

/-- The packet swap is an involution after exchanging the source labels back. -/
theorem packetDisjointSumSwapLinearEquiv_involutive
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum ι κ → V) :
    packetDisjointSumSwapLinearEquiv
        (packetDisjointSumSwapLinearEquiv packet) = packet := by
  funext mode
  cases mode <;> rfl

/-- Exchange the two mode families of a combined D9 zero-cokernel packet. -/
def d9GaugeGhostZeroCokernelPacketSwap (ι κ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum ι κ) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum κ ι) :=
  packetDisjointSumSwapLinearEquiv

/-- Exchange the two mode families of a gauge-coordinate packet. -/
def d9GaugeZeroCoordinatePacketSwap (ι κ : Type*) :
    D9GaugeZeroCoordinatePacket (Sum ι κ) ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket (Sum κ ι) :=
  packetDisjointSumSwapLinearEquiv

/-- Exchange the two mode families of a ghost-coordinate packet. -/
def d9GhostZeroCoordinatePacketSwap (ι κ : Type*) :
    D9GhostZeroCoordinatePacket (Sum ι κ) ≃ₗ[Real]
      D9GhostZeroCoordinatePacket (Sum κ ι) :=
  packetDisjointSumSwapLinearEquiv

/-- Gauge--ghost splitting commutes with exchanging the two disjoint mode
families. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_swap_naturality
    {ι κ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι κ)) :
    d9GaugeGhostZeroCokernelPacketEquiv (Sum κ ι)
        (d9GaugeGhostZeroCokernelPacketSwap ι κ packet) =
      (d9GaugeZeroCoordinatePacketSwap ι κ
          (d9GaugeGhostZeroCokernelPacketEquiv (Sum ι κ) packet).1,
        d9GhostZeroCoordinatePacketSwap ι κ
          (d9GaugeGhostZeroCokernelPacketEquiv (Sum ι κ) packet).2) := by
  apply Prod.ext
  · funext mode
    cases mode <;> rfl
  · funext mode
    cases mode <;> rfl

/-- Splitting a swapped combined packet reverses the two packet components. -/
theorem d9GaugeGhostZeroCokernelPacketDisjointSum_swap_naturality
    {ι κ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι κ)) :
    d9GaugeGhostZeroCokernelPacketDisjointSumEquiv κ ι
        (d9GaugeGhostZeroCokernelPacketSwap ι κ packet) =
      ((d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ packet).2,
        (d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ packet).1) := by
  apply Prod.ext
  · funext mode
    rfl
  · funext mode
    rfl

/-- The same reversed-component law for gauge-coordinate packets. -/
theorem d9GaugeZeroCoordinatePacketDisjointSum_swap_naturality
    {ι κ : Type*}
    (packet : D9GaugeZeroCoordinatePacket (Sum ι κ)) :
    d9GaugeZeroCoordinatePacketDisjointSumEquiv κ ι
        (d9GaugeZeroCoordinatePacketSwap ι κ packet) =
      ((d9GaugeZeroCoordinatePacketDisjointSumEquiv ι κ packet).2,
        (d9GaugeZeroCoordinatePacketDisjointSumEquiv ι κ packet).1) := by
  apply Prod.ext
  · funext mode
    rfl
  · funext mode
    rfl

/-- The same reversed-component law for ghost-coordinate packets. -/
theorem d9GhostZeroCoordinatePacketDisjointSum_swap_naturality
    {ι κ : Type*}
    (packet : D9GhostZeroCoordinatePacket (Sum ι κ)) :
    d9GhostZeroCoordinatePacketDisjointSumEquiv κ ι
        (d9GhostZeroCoordinatePacketSwap ι κ packet) =
      ((d9GhostZeroCoordinatePacketDisjointSumEquiv ι κ packet).2,
        (d9GhostZeroCoordinatePacketDisjointSumEquiv ι κ packet).1) := by
  apply Prod.ext
  · funext mode
    rfl
  · funext mode
    rfl

/-- Exchanging the two families twice recovers the original combined packet. -/
theorem d9GaugeGhostZeroCokernelPacketSwap_involutive
    {ι κ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι κ)) :
    d9GaugeGhostZeroCokernelPacketSwap κ ι
        (d9GaugeGhostZeroCokernelPacketSwap ι κ packet) = packet := by
  funext mode
  cases mode <;> rfl

/-- Combined zero-cokernel packet dimension is symmetric under exchange of the
two mode families. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_sum_swap
    (ι κ : Type*) :
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum κ ι)) :=
  LinearEquiv.finrank_eq (d9GaugeGhostZeroCokernelPacketSwap ι κ)

/-- Gauge-coordinate packet dimension has the same symmetry. -/
theorem d9GaugeZeroCoordinatePacket_finrank_sum_swap
    (ι κ : Type*) :
    Module.finrank Real (D9GaugeZeroCoordinatePacket (Sum ι κ)) =
      Module.finrank Real (D9GaugeZeroCoordinatePacket (Sum κ ι)) :=
  LinearEquiv.finrank_eq (d9GaugeZeroCoordinatePacketSwap ι κ)

/-- Ghost-coordinate packet dimension has the same symmetry. -/
theorem d9GhostZeroCoordinatePacket_finrank_sum_swap
    (ι κ : Type*) :
    Module.finrank Real (D9GhostZeroCoordinatePacket (Sum ι κ)) =
      Module.finrank Real (D9GhostZeroCoordinatePacket (Sum κ ι)) :=
  LinearEquiv.finrank_eq (d9GhostZeroCoordinatePacketSwap ι κ)

/-- Reusable coherence certificate for exchanging two finite or infinite
labels of disjoint D9 zero-mode packets. -/
theorem d9GaugeGhostFinitePacketSumSymmetry_certificate
    {ι κ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι κ)) :
    d9GaugeGhostZeroCokernelPacketSwap κ ι
          (d9GaugeGhostZeroCokernelPacketSwap ι κ packet) = packet ∧
      d9GaugeGhostZeroCokernelPacketDisjointSumEquiv κ ι
          (d9GaugeGhostZeroCokernelPacketSwap ι κ packet) =
        ((d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ packet).2,
          (d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ packet).1) ∧
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
        Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum κ ι)) := by
  exact ⟨d9GaugeGhostZeroCokernelPacketSwap_involutive packet,
    d9GaugeGhostZeroCokernelPacketDisjointSum_swap_naturality packet,
    d9GaugeGhostZeroCokernelPacket_finrank_sum_swap ι κ⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketSumSymmetry4D
end JanusFormal
