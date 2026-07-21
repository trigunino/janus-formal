import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketReindex4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
open P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D
open P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D
open P0EFTJanusGaugeGhostBlockD9PointwiseCohomologyIndex4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- Pull a linear packet back along an equivalence of its mode labels.  This
small generic equivalence is kept independent of the D9 geometry so later
finite field, regulator and internal-space packets can reuse it. -/
def packetReindexLinearEquiv {ι κ V : Type*}
    [AddCommMonoid V] [Module Real V] (equiv : ι ≃ κ) :
    (κ → V) ≃ₗ[Real] (ι → V) where
  toFun packet mode := packet (equiv mode)
  invFun packet mode := packet (equiv.symm mode)
  left_inv packet := by
    funext mode
    simp
  right_inv packet := by
    funext mode
    simp
  map_add' first second := by
    funext mode
    rfl
  map_smul' scalar packet := by
    funext mode
    rfl

@[simp] theorem packetReindexLinearEquiv_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (equiv : ι ≃ κ) (packet : κ → V) (mode : ι) :
    packetReindexLinearEquiv equiv packet mode = packet (equiv mode) := rfl

@[simp] theorem packetReindexLinearEquiv_symm_apply
    {ι κ V : Type*} [AddCommMonoid V] [Module Real V]
    (equiv : ι ≃ κ) (packet : ι → V) (mode : κ) :
    (packetReindexLinearEquiv equiv).symm packet mode =
      packet (equiv.symm mode) := rfl

@[simp] theorem packetReindexLinearEquiv_refl_apply
    {ι V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : ι → V) :
    packetReindexLinearEquiv (Equiv.refl ι) packet = packet := by
  funext mode
  rfl

theorem packetReindexLinearEquiv_trans_apply
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (first : ι ≃ κ) (second : κ ≃ μ) (packet : μ → V) :
    packetReindexLinearEquiv first
        (packetReindexLinearEquiv second packet) =
      packetReindexLinearEquiv (first.trans second) packet := by
  funext mode
  rfl

/-- Reindex the combined D9 zero-covector cokernel packet. -/
def d9GaugeGhostZeroCokernelPacketReindex {ι κ : Type*}
    (equiv : ι ≃ κ) :
    D9GaugeGhostZeroCokernelPacket κ ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket ι :=
  packetReindexLinearEquiv equiv

/-- Reindex the separated gauge-coordinate packet. -/
def d9GaugeZeroCoordinatePacketReindex {ι κ : Type*}
    (equiv : ι ≃ κ) :
    D9GaugeZeroCoordinatePacket κ ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket ι :=
  packetReindexLinearEquiv equiv

/-- Reindex the separated ghost-coordinate packet. -/
def d9GhostZeroCoordinatePacketReindex {ι κ : Type*}
    (equiv : ι ≃ κ) :
    D9GhostZeroCoordinatePacket κ ≃ₗ[Real]
      D9GhostZeroCoordinatePacket ι :=
  packetReindexLinearEquiv equiv

@[simp] theorem d9GaugeGhostZeroCokernelPacketReindex_apply
    {ι κ : Type*} (equiv : ι ≃ κ)
    (packet : D9GaugeGhostZeroCokernelPacket κ) (mode : ι) :
    d9GaugeGhostZeroCokernelPacketReindex equiv packet mode =
      packet (equiv mode) := rfl

@[simp] theorem d9GaugeZeroCoordinatePacketReindex_apply
    {ι κ : Type*} (equiv : ι ≃ κ)
    (packet : D9GaugeZeroCoordinatePacket κ) (mode : ι) :
    d9GaugeZeroCoordinatePacketReindex equiv packet mode =
      packet (equiv mode) := rfl

@[simp] theorem d9GhostZeroCoordinatePacketReindex_apply
    {ι κ : Type*} (equiv : ι ≃ κ)
    (packet : D9GhostZeroCoordinatePacket κ) (mode : ι) :
    d9GhostZeroCoordinatePacketReindex equiv packet mode =
      packet (equiv mode) := rfl

/-- Gauge--ghost zero-mode splitting is natural under every relabelling of the
packet modes. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_reindex_naturality
    {ι κ : Type*} (equiv : ι ≃ κ)
    (packet : D9GaugeGhostZeroCokernelPacket κ) :
    d9GaugeGhostZeroCokernelPacketEquiv ι
        (d9GaugeGhostZeroCokernelPacketReindex equiv packet) =
      (d9GaugeZeroCoordinatePacketReindex equiv
          (d9GaugeGhostZeroCokernelPacketEquiv κ packet).1,
        d9GhostZeroCoordinatePacketReindex equiv
          (d9GaugeGhostZeroCokernelPacketEquiv κ packet).2) := by
  apply Prod.ext
  · funext mode
    rfl
  · funext mode
    rfl

/-- Reconstruction from separated gauge and ghost packets is natural under
mode relabelling as well. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_symm_reindex_naturality
    {ι κ : Type*} (equiv : ι ≃ κ)
    (separated :
      D9GaugeZeroCoordinatePacket κ × D9GhostZeroCoordinatePacket κ) :
    d9GaugeGhostZeroCokernelPacketReindex equiv
        ((d9GaugeGhostZeroCokernelPacketEquiv κ).symm separated) =
      (d9GaugeGhostZeroCokernelPacketEquiv ι).symm
        (d9GaugeZeroCoordinatePacketReindex equiv separated.1,
          d9GhostZeroCoordinatePacketReindex equiv separated.2) := by
  funext mode
  rfl

/-- The combined zero-mode packet dimension is independent of the chosen
finite mode labelling. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_reindex
    {ι κ : Type*} (equiv : ι ≃ κ) :
    Module.finrank Real (D9GaugeGhostZeroCokernelPacket κ) =
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) :=
  LinearEquiv.finrank_eq (d9GaugeGhostZeroCokernelPacketReindex equiv)

/-- The gauge packet dimension is independent of the chosen mode labelling. -/
theorem d9GaugeZeroCoordinatePacket_finrank_reindex
    {ι κ : Type*} (equiv : ι ≃ κ) :
    Module.finrank Real (D9GaugeZeroCoordinatePacket κ) =
      Module.finrank Real (D9GaugeZeroCoordinatePacket ι) :=
  LinearEquiv.finrank_eq (d9GaugeZeroCoordinatePacketReindex equiv)

/-- The ghost packet dimension is independent of the chosen mode labelling. -/
theorem d9GhostZeroCoordinatePacket_finrank_reindex
    {ι κ : Type*} (equiv : ι ≃ κ) :
    Module.finrank Real (D9GhostZeroCoordinatePacket κ) =
      Module.finrank Real (D9GhostZeroCoordinatePacket ι) :=
  LinearEquiv.finrank_eq (d9GhostZeroCoordinatePacketReindex equiv)

/-- The finite pointwise index is invariant when the selected modes are
transported through an equivalence. -/
theorem d9GaugeGhostFinitePointwiseIndex_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9GaugeGhostFinitePointwiseIndex (modes.map equiv.toEmbedding) covector =
      d9GaugeGhostFinitePointwiseIndex modes
        (fun mode => covector (equiv mode)) := by
  classical
  simpa [d9GaugeGhostFinitePointwiseIndex] using
    (Finset.sum_map modes equiv.toEmbedding
      (fun mode : κ => d9GaugeGhostBlockPointwiseIndex (covector mode)))

/-- The separated gauge-plus-ghost pointwise index has the same relabelling
invariance. -/
theorem d9SeparatedFinitePointwiseIndex_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9SeparatedFinitePointwiseIndex (modes.map equiv.toEmbedding) covector =
      d9SeparatedFinitePointwiseIndex modes
        (fun mode => covector (equiv mode)) := by
  classical
  simpa [d9SeparatedFinitePointwiseIndex] using
    (Finset.sum_map modes equiv.toEmbedding
      (fun mode : κ =>
        d9GaugePointwiseIndex (covector mode) +
          d9GhostPointwiseIndex (covector mode)))

/-- Combined D9 cokernel finrank is invariant under finite packet
relabelling. -/
theorem d9GaugeGhostFiniteCokernelFinrank_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9GaugeGhostFiniteCokernelFinrank (modes.map equiv.toEmbedding) covector =
      d9GaugeGhostFiniteCokernelFinrank modes
        (fun mode => covector (equiv mode)) := by
  classical
  simpa [d9GaugeGhostFiniteCokernelFinrank] using
    (Finset.sum_map modes equiv.toEmbedding
      (fun mode : κ =>
        Module.finrank Real (D9GaugeGhostBlockCokernel (covector mode))))

/-- The separated cokernel finrank calculation is invariant under the same
finite packet relabelling. -/
theorem d9SeparatedFiniteCokernelFinrank_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9SeparatedFiniteCokernelFinrank (modes.map equiv.toEmbedding) covector =
      d9SeparatedFiniteCokernelFinrank modes
        (fun mode => covector (equiv mode)) := by
  classical
  simpa [d9SeparatedFiniteCokernelFinrank] using
    (Finset.sum_map modes equiv.toEmbedding
      (fun mode : κ =>
        Module.finrank Real (D9GaugeCokernel (covector mode)) +
          Module.finrank Real (D9GhostCokernel (covector mode))))

/-- The actual support finset of zero covectors is transported exactly by an
equivalence of mode labels. -/
theorem d9ZeroCovectorModes_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9ZeroCovectorModes (modes.map equiv.toEmbedding) covector =
      (d9ZeroCovectorModes modes
        (fun mode => covector (equiv mode))).map equiv.toEmbedding := by
  classical
  simpa [d9ZeroCovectorModes, Function.comp_def] using
    (Finset.filter_map
      (f := equiv.toEmbedding) (s := modes)
      (p := fun mode : κ => covector mode = zeroTangent))

/-- Therefore the number of zero-covector modes is independent of the mode
labelling. -/
theorem d9ZeroCovectorMultiplicity_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9ZeroCovectorMultiplicity (modes.map equiv.toEmbedding) covector =
      d9ZeroCovectorMultiplicity modes
        (fun mode => covector (equiv mode)) := by
  unfold d9ZeroCovectorMultiplicity
  rw [d9ZeroCovectorModes_map_equiv]
  exact Finset.card_map equiv.toEmbedding

/-- The exact zero-mode support formula is stable under arbitrary finite mode
relabellings. -/
theorem d9GaugeGhostFiniteCokernelSupport_map_equiv
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9GaugeGhostFiniteCokernelFinrank (modes.map equiv.toEmbedding) covector =
      d9ZeroCovectorMultiplicity modes
          (fun mode => covector (equiv mode)) *
        d9GaugeGhostZeroCokernelFinrank := by
  calc
    d9GaugeGhostFiniteCokernelFinrank (modes.map equiv.toEmbedding) covector =
        d9GaugeGhostFiniteCokernelFinrank modes
          (fun mode => covector (equiv mode)) :=
      d9GaugeGhostFiniteCokernelFinrank_map_equiv equiv modes covector
    _ = d9ZeroCovectorMultiplicity modes
          (fun mode => covector (equiv mode)) *
        d9GaugeGhostZeroCokernelFinrank :=
      d9GaugeGhostFiniteCokernelFinrank_eq_zeroMultiplicity_mul modes
        (fun mode => covector (equiv mode))

/-- Reusable certificate that mode equivalences preserve every finite D9
quantity introduced by the index and cokernel-support leaves. -/
theorem d9GaugeGhostFinitePacketReindex_certificate
    {ι κ : Type*} (equiv : ι ≃ κ) (modes : Finset ι)
    (covector : κ → TangentVector3) :
    d9GaugeGhostFinitePointwiseIndex (modes.map equiv.toEmbedding) covector =
        d9GaugeGhostFinitePointwiseIndex modes
          (fun mode => covector (equiv mode)) ∧
      d9SeparatedFinitePointwiseIndex (modes.map equiv.toEmbedding) covector =
        d9SeparatedFinitePointwiseIndex modes
          (fun mode => covector (equiv mode)) ∧
      d9GaugeGhostFiniteCokernelFinrank
          (modes.map equiv.toEmbedding) covector =
        d9GaugeGhostFiniteCokernelFinrank modes
          (fun mode => covector (equiv mode)) ∧
      d9ZeroCovectorMultiplicity (modes.map equiv.toEmbedding) covector =
        d9ZeroCovectorMultiplicity modes
          (fun mode => covector (equiv mode)) := by
  exact ⟨d9GaugeGhostFinitePointwiseIndex_map_equiv equiv modes covector,
    d9SeparatedFinitePointwiseIndex_map_equiv equiv modes covector,
    d9GaugeGhostFiniteCokernelFinrank_map_equiv equiv modes covector,
    d9ZeroCovectorMultiplicity_map_equiv equiv modes covector⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketReindex4D
end JanusFormal
