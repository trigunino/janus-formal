import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketReindex4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketDisjointSum4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D

/-- A packet indexed by a disjoint sum is linearly equivalent to a pair of
packets indexed by the two summands.  This generic construction is independent
of the D9 fibres. -/
def packetDisjointSumLinearEquiv {ι κ V : Type*}
    [AddCommMonoid V] [Module Real V] :
    (Sum ι κ → V) ≃ₗ[Real] ((ι → V) × (κ → V)) where
  toFun packet :=
    (fun mode => packet (Sum.inl mode),
      fun mode => packet (Sum.inr mode))
  invFun separated := Sum.elim separated.1 separated.2
  left_inv packet := by
    funext mode
    cases mode <;> rfl
  right_inv separated := by
    rcases separated with ⟨left, right⟩
    apply Prod.ext
    · funext mode
      rfl
    · funext mode
      rfl
  map_add' first second := by
    apply Prod.ext
    · funext mode
      rfl
    · funext mode
      rfl
  map_smul' scalar packet := by
    apply Prod.ext
    · funext mode
      rfl
    · funext mode
      rfl

@[simp] theorem packetDisjointSumLinearEquiv_fst_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum ι κ → V) (mode : ι) :
    (packetDisjointSumLinearEquiv packet).1 mode =
      packet (Sum.inl mode) := rfl

@[simp] theorem packetDisjointSumLinearEquiv_snd_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum ι κ → V) (mode : κ) :
    (packetDisjointSumLinearEquiv packet).2 mode =
      packet (Sum.inr mode) := rfl

@[simp] theorem packetDisjointSumLinearEquiv_symm_inl_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (separated : (ι → V) × (κ → V)) (mode : ι) :
    (packetDisjointSumLinearEquiv.symm separated) (Sum.inl mode) =
      separated.1 mode := rfl

@[simp] theorem packetDisjointSumLinearEquiv_symm_inr_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (separated : (ι → V) × (κ → V)) (mode : κ) :
    (packetDisjointSumLinearEquiv.symm separated) (Sum.inr mode) =
      separated.2 mode := rfl

/-- Split a combined D9 zero-mode packet into two disjoint mode families. -/
def d9GaugeGhostZeroCokernelPacketDisjointSumEquiv
    (ι κ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum ι κ) ≃ₗ[Real]
      (D9GaugeGhostZeroCokernelPacket ι ×
        D9GaugeGhostZeroCokernelPacket κ) :=
  packetDisjointSumLinearEquiv

/-- Split the corresponding gauge-coordinate packet. -/
def d9GaugeZeroCoordinatePacketDisjointSumEquiv
    (ι κ : Type*) :
    D9GaugeZeroCoordinatePacket (Sum ι κ) ≃ₗ[Real]
      (D9GaugeZeroCoordinatePacket ι × D9GaugeZeroCoordinatePacket κ) :=
  packetDisjointSumLinearEquiv

/-- Split the corresponding ghost-coordinate packet. -/
def d9GhostZeroCoordinatePacketDisjointSumEquiv
    (ι κ : Type*) :
    D9GhostZeroCoordinatePacket (Sum ι κ) ≃ₗ[Real]
      (D9GhostZeroCoordinatePacket ι × D9GhostZeroCoordinatePacket κ) :=
  packetDisjointSumLinearEquiv

/-- Restricting the gauge--ghost splitting to the left mode family agrees with
first splitting the full disjoint packet. -/
theorem d9GaugeGhostZeroCokernelPacketDisjointSum_left_naturality
    {ι κ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι κ)) :
    d9GaugeGhostZeroCokernelPacketEquiv ι
        (d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ packet).1 =
      ((d9GaugeZeroCoordinatePacketDisjointSumEquiv ι κ
          (d9GaugeGhostZeroCokernelPacketEquiv (Sum ι κ) packet).1).1,
        (d9GhostZeroCoordinatePacketDisjointSumEquiv ι κ
          (d9GaugeGhostZeroCokernelPacketEquiv (Sum ι κ) packet).2).1) := by
  apply Prod.ext
  · funext mode
    rfl
  · funext mode
    rfl

/-- The same naturality statement for the right mode family. -/
theorem d9GaugeGhostZeroCokernelPacketDisjointSum_right_naturality
    {ι κ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι κ)) :
    d9GaugeGhostZeroCokernelPacketEquiv κ
        (d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ packet).2 =
      ((d9GaugeZeroCoordinatePacketDisjointSumEquiv ι κ
          (d9GaugeGhostZeroCokernelPacketEquiv (Sum ι κ) packet).1).2,
        (d9GhostZeroCoordinatePacketDisjointSumEquiv ι κ
          (d9GaugeGhostZeroCokernelPacketEquiv (Sum ι κ) packet).2).2) := by
  apply Prod.ext
  · funext mode
    rfl
  · funext mode
    rfl

/-- Combined zero-mode packet dimensions add across disjoint mode families. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_disjointSum
    (ι κ : Type*) :
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) +
        Module.finrank Real (D9GaugeGhostZeroCokernelPacket κ) := by
  calc
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
        Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket ι ×
            D9GaugeGhostZeroCokernelPacket κ) :=
      LinearEquiv.finrank_eq
        (d9GaugeGhostZeroCokernelPacketDisjointSumEquiv ι κ)
    _ = Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) +
        Module.finrank Real (D9GaugeGhostZeroCokernelPacket κ) :=
      Module.finrank_prod

/-- Gauge-coordinate packet dimensions add across disjoint mode families. -/
theorem d9GaugeZeroCoordinatePacket_finrank_disjointSum
    (ι κ : Type*) :
    Module.finrank Real (D9GaugeZeroCoordinatePacket (Sum ι κ)) =
      Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
        Module.finrank Real (D9GaugeZeroCoordinatePacket κ) := by
  calc
    Module.finrank Real (D9GaugeZeroCoordinatePacket (Sum ι κ)) =
        Module.finrank Real
          (D9GaugeZeroCoordinatePacket ι × D9GaugeZeroCoordinatePacket κ) :=
      LinearEquiv.finrank_eq
        (d9GaugeZeroCoordinatePacketDisjointSumEquiv ι κ)
    _ = Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
        Module.finrank Real (D9GaugeZeroCoordinatePacket κ) :=
      Module.finrank_prod

/-- Ghost-coordinate packet dimensions add across disjoint mode families. -/
theorem d9GhostZeroCoordinatePacket_finrank_disjointSum
    (ι κ : Type*) :
    Module.finrank Real (D9GhostZeroCoordinatePacket (Sum ι κ)) =
      Module.finrank Real (D9GhostZeroCoordinatePacket ι) +
        Module.finrank Real (D9GhostZeroCoordinatePacket κ) := by
  calc
    Module.finrank Real (D9GhostZeroCoordinatePacket (Sum ι κ)) =
        Module.finrank Real
          (D9GhostZeroCoordinatePacket ι × D9GhostZeroCoordinatePacket κ) :=
      LinearEquiv.finrank_eq
        (d9GhostZeroCoordinatePacketDisjointSumEquiv ι κ)
    _ = Module.finrank Real (D9GhostZeroCoordinatePacket ι) +
        Module.finrank Real (D9GhostZeroCoordinatePacket κ) :=
      Module.finrank_prod

/-- For finite mode families, disjoint-family additivity and gauge--ghost
additivity combine into a four-packet dimension formula. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_disjointSum_gaugeGhost
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
      (Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
        Module.finrank Real (D9GhostZeroCoordinatePacket ι)) +
      (Module.finrank Real (D9GaugeZeroCoordinatePacket κ) +
        Module.finrank Real (D9GhostZeroCoordinatePacket κ)) := by
  rw [d9GaugeGhostZeroCokernelPacket_finrank_disjointSum,
    d9GaugeGhostZeroCokernelPacket_finrank_additive ι,
    d9GaugeGhostZeroCokernelPacket_finrank_additive κ]

/-- Closure certificate for disjoint finite mode packets. -/
theorem d9GaugeGhostFinitePacketDisjointSum_certificate
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
        Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) +
          Module.finrank Real (D9GaugeGhostZeroCokernelPacket κ) ∧
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket (Sum ι κ)) =
        (Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
          Module.finrank Real (D9GhostZeroCoordinatePacket ι)) +
        (Module.finrank Real (D9GaugeZeroCoordinatePacket κ) +
          Module.finrank Real (D9GhostZeroCoordinatePacket κ)) := by
  exact ⟨d9GaugeGhostZeroCokernelPacket_finrank_disjointSum ι κ,
    d9GaugeGhostZeroCokernelPacket_finrank_disjointSum_gaugeGhost ι κ⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketDisjointSum4D
end JanusFormal
