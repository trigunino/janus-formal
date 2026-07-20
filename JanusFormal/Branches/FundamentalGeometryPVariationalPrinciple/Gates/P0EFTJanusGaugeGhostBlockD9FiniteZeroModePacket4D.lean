import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

/-- A packet of D9 combined gauge--ghost zero-covector cokernel classes. -/
abbrev D9GaugeGhostZeroCokernelPacket (ι : Type*) :=
  ι → D9GaugeGhostBlockCokernel zeroTangent

/-- Gauge coordinates extracted from a packet of zero-covector classes. -/
abbrev D9GaugeZeroCoordinatePacket (ι : Type*) :=
  ι → D9GaugeLinearCoordinate

/-- Ghost coordinates extracted from a packet of zero-covector classes. -/
abbrev D9GhostZeroCoordinatePacket (ι : Type*) :=
  ι → D9PairedGhostCoordinateSpace

/-- The pointwise zero-mode gauge--ghost splitting upgrades to a linear
splitting of arbitrary packets.  Finite field multiplicities are obtained by
taking `ι` to be a finite type. -/
def d9GaugeGhostZeroCokernelPacketEquiv (ι : Type*) :
    D9GaugeGhostZeroCokernelPacket ι ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket ι × D9GhostZeroCoordinatePacket ι where
  toFun packet :=
    (fun mode => zeroCokernelGaugeProjection (packet mode),
      fun mode => zeroCokernelGhostProjection (packet mode))
  invFun separated := fun mode =>
    zeroCokernelGaugeInclusion (separated.1 mode) +
      zeroCokernelGhostInclusion (separated.2 mode)
  left_inv packet := by
    funext mode
    exact zeroCokernel_gauge_add_ghost (packet mode)
  right_inv separated := by
    rcases separated with ⟨gauge, ghost⟩
    apply Prod.ext
    · funext mode
      simp [zeroCokernelGaugeProjection_inclusion,
        zeroCokernelGaugeProjection_ghostInclusion]
    · funext mode
      simp [zeroCokernelGhostProjection_inclusion,
        zeroCokernelGhostProjection_gaugeInclusion]
  map_add' first second := by
    apply Prod.ext
    · funext mode
      simp
    · funext mode
      simp
  map_smul' scalar packet := by
    apply Prod.ext
    · funext mode
      simp
    · funext mode
      simp

@[simp] theorem d9GaugeGhostZeroCokernelPacketEquiv_fst_apply
    {ι : Type*} (packet : D9GaugeGhostZeroCokernelPacket ι) (mode : ι) :
    (d9GaugeGhostZeroCokernelPacketEquiv ι packet).1 mode =
      zeroCokernelGaugeProjection (packet mode) := rfl

@[simp] theorem d9GaugeGhostZeroCokernelPacketEquiv_snd_apply
    {ι : Type*} (packet : D9GaugeGhostZeroCokernelPacket ι) (mode : ι) :
    (d9GaugeGhostZeroCokernelPacketEquiv ι packet).2 mode =
      zeroCokernelGhostProjection (packet mode) := rfl

@[simp] theorem d9GaugeGhostZeroCokernelPacketEquiv_symm_apply
    {ι : Type*}
    (separated : D9GaugeZeroCoordinatePacket ι × D9GhostZeroCoordinatePacket ι)
    (mode : ι) :
    ((d9GaugeGhostZeroCokernelPacketEquiv ι).symm separated) mode =
      zeroCokernelGaugeInclusion (separated.1 mode) +
        zeroCokernelGhostInclusion (separated.2 mode) := rfl

/-- Two combined zero-mode packets coincide as soon as both their gauge and
Ghost projections coincide mode by mode. -/
theorem d9GaugeGhostZeroCokernelPacket_ext {ι : Type*}
    {first second : D9GaugeGhostZeroCokernelPacket ι}
    (hGauge : ∀ mode,
      zeroCokernelGaugeProjection (first mode) =
        zeroCokernelGaugeProjection (second mode))
    (hGhost : ∀ mode,
      zeroCokernelGhostProjection (first mode) =
        zeroCokernelGhostProjection (second mode)) :
    first = second := by
  funext mode
  calc
    first mode =
        zeroCokernelGaugeInclusion (zeroCokernelGaugeProjection (first mode)) +
          zeroCokernelGhostInclusion (zeroCokernelGhostProjection (first mode)) :=
      (zeroCokernel_gauge_add_ghost (first mode)).symm
    _ =
        zeroCokernelGaugeInclusion (zeroCokernelGaugeProjection (second mode)) +
          zeroCokernelGhostInclusion (zeroCokernelGhostProjection (second mode)) := by
      rw [hGauge mode, hGhost mode]
    _ = second mode := zeroCokernel_gauge_add_ghost (second mode)

/-- For a finite multiplicity type, the actual combined zero-mode packet has
exactly the sum of the gauge-packet and ghost-packet dimensions. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_additive
    (ι : Type*) [Fintype ι] :
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) =
      Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
        Module.finrank Real (D9GhostZeroCoordinatePacket ι) := by
  calc
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) =
        Module.finrank Real
          (D9GaugeZeroCoordinatePacket ι × D9GhostZeroCoordinatePacket ι) :=
      LinearEquiv.finrank_eq (d9GaugeGhostZeroCokernelPacketEquiv ι)
    _ =
        Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
          Module.finrank Real (D9GhostZeroCoordinatePacket ι) :=
      Module.finrank_prod

/-- Closure certificate bundling the packet equivalence, reconstruction and
finite-dimensional additivity used by later regulator or internal-space
multiplicity arguments. -/
theorem d9GaugeGhostFiniteZeroModePacket_certificate
    (ι : Type*) [Fintype ι]
    (packet : D9GaugeGhostZeroCokernelPacket ι) :
    (d9GaugeGhostZeroCokernelPacketEquiv ι).symm
          (d9GaugeGhostZeroCokernelPacketEquiv ι packet) = packet ∧
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) =
        Module.finrank Real (D9GaugeZeroCoordinatePacket ι) +
          Module.finrank Real (D9GhostZeroCoordinatePacket ι) := by
  exact ⟨(d9GaugeGhostZeroCokernelPacketEquiv ι).left_inv packet,
    d9GaugeGhostZeroCokernelPacket_finrank_additive ι⟩

end
end P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
end JanusFormal
