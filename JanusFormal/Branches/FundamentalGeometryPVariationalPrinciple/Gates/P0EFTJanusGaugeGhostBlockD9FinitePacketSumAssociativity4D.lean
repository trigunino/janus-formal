import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketDisjointSum4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketSumAssociativity4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketDisjointSum4D

/-- Canonical reassociation of three disjoint mode families. -/
def d9PacketSumAssocEquiv (ι κ μ : Type*) :
    Sum (Sum ι κ) μ ≃ Sum ι (Sum κ μ) where
  toFun value :=
    match value with
    | Sum.inl (Sum.inl left) => Sum.inl left
    | Sum.inl (Sum.inr middle) => Sum.inr (Sum.inl middle)
    | Sum.inr right => Sum.inr (Sum.inr right)
  invFun value :=
    match value with
    | Sum.inl left => Sum.inl (Sum.inl left)
    | Sum.inr (Sum.inl middle) => Sum.inl (Sum.inr middle)
    | Sum.inr (Sum.inr right) => Sum.inr right
  left_inv value := by
    cases value with
    | inl left =>
        cases left <;> rfl
    | inr right => rfl
  right_inv value := by
    cases value with
    | inl left => rfl
    | inr right =>
        cases right <;> rfl

@[simp] theorem d9PacketSumAssocEquiv_inl_inl
    {ι κ μ : Type*} (mode : ι) :
    d9PacketSumAssocEquiv ι κ μ (Sum.inl (Sum.inl mode)) =
      Sum.inl mode := rfl

@[simp] theorem d9PacketSumAssocEquiv_inl_inr
    {ι κ μ : Type*} (mode : κ) :
    d9PacketSumAssocEquiv ι κ μ (Sum.inl (Sum.inr mode)) =
      Sum.inr (Sum.inl mode) := rfl

@[simp] theorem d9PacketSumAssocEquiv_inr
    {ι κ μ : Type*} (mode : μ) :
    d9PacketSumAssocEquiv ι κ μ (Sum.inr mode) =
      Sum.inr (Sum.inr mode) := rfl

/-- Reassociate a linear packet indexed by three disjoint mode families. -/
def packetDisjointSumAssocLinearEquiv {ι κ μ V : Type*}
    [AddCommMonoid V] [Module Real V] :
    (Sum (Sum ι κ) μ → V) ≃ₗ[Real] (Sum ι (Sum κ μ) → V) where
  toFun packet value :=
    match value with
    | Sum.inl left => packet (Sum.inl (Sum.inl left))
    | Sum.inr (Sum.inl middle) => packet (Sum.inl (Sum.inr middle))
    | Sum.inr (Sum.inr right) => packet (Sum.inr right)
  invFun packet value :=
    match value with
    | Sum.inl (Sum.inl left) => packet (Sum.inl left)
    | Sum.inl (Sum.inr middle) => packet (Sum.inr (Sum.inl middle))
    | Sum.inr right => packet (Sum.inr (Sum.inr right))
  left_inv packet := by
    funext value
    cases value with
    | inl left =>
        cases left <;> rfl
    | inr right => rfl
  right_inv packet := by
    funext value
    cases value with
    | inl left => rfl
    | inr right =>
        cases right <;> rfl
  map_add' first second := by
    funext value
    cases value with
    | inl left => rfl
    | inr right =>
        cases right <;> rfl
  map_smul' scalar packet := by
    funext value
    cases value with
    | inl left => rfl
    | inr right =>
        cases right <;> rfl

@[simp] theorem packetDisjointSumAssocLinearEquiv_inl_apply
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum ι κ) μ → V) (mode : ι) :
    packetDisjointSumAssocLinearEquiv packet (Sum.inl mode) =
      packet (Sum.inl (Sum.inl mode)) := rfl

@[simp] theorem packetDisjointSumAssocLinearEquiv_middle_apply
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum ι κ) μ → V) (mode : κ) :
    packetDisjointSumAssocLinearEquiv packet (Sum.inr (Sum.inl mode)) =
      packet (Sum.inl (Sum.inr mode)) := rfl

@[simp] theorem packetDisjointSumAssocLinearEquiv_inr_apply
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum ι κ) μ → V) (mode : μ) :
    packetDisjointSumAssocLinearEquiv packet (Sum.inr (Sum.inr mode)) =
      packet (Sum.inr mode) := rfl

/-- Reassociation followed by inverse reassociation recovers every packet. -/
theorem packetDisjointSumAssocLinearEquiv_roundtrip
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum ι κ) μ → V) :
    (packetDisjointSumAssocLinearEquiv
        (ι := ι) (κ := κ) (μ := μ) (V := V)).symm
        (packetDisjointSumAssocLinearEquiv packet) = packet :=
  (packetDisjointSumAssocLinearEquiv
    (ι := ι) (κ := κ) (μ := μ) (V := V)).left_inv packet

/-- Iterated binary packet splitting is independent of the parenthesization. -/
theorem packetDisjointSumAssocLinearEquiv_split_naturality
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum ι κ) μ → V) :
    let leftOuter :=
      packetDisjointSumLinearEquiv
        (ι := Sum ι κ) (κ := μ) (V := V) packet
    let leftInner :=
      packetDisjointSumLinearEquiv
        (ι := ι) (κ := κ) (V := V) leftOuter.1
    let rightOuter :=
      packetDisjointSumLinearEquiv
        (ι := ι) (κ := Sum κ μ) (V := V)
        (packetDisjointSumAssocLinearEquiv packet)
    let rightInner :=
      packetDisjointSumLinearEquiv
        (ι := κ) (κ := μ) (V := V) rightOuter.2
    (rightOuter.1, (rightInner.1, rightInner.2)) =
      (leftInner.1, (leftInner.2, leftOuter.2)) := by
  rfl

/-- Reassociate the combined D9 gauge--ghost zero-cokernel packet. -/
def d9GaugeGhostZeroCokernelPacketAssoc (ι κ μ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ)) :=
  packetDisjointSumAssocLinearEquiv

/-- Reassociate the gauge-coordinate zero-mode packet. -/
def d9GaugeZeroCoordinatePacketAssoc (ι κ μ : Type*) :
    D9GaugeZeroCoordinatePacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket (Sum ι (Sum κ μ)) :=
  packetDisjointSumAssocLinearEquiv

/-- Reassociate the ghost-coordinate zero-mode packet. -/
def d9GhostZeroCoordinatePacketAssoc (ι κ μ : Type*) :
    D9GhostZeroCoordinatePacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GhostZeroCoordinatePacket (Sum ι (Sum κ μ)) :=
  packetDisjointSumAssocLinearEquiv

/-- Gauge--ghost splitting commutes with reassociation of three mode families. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_assoc_naturality
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) :
    d9GaugeGhostZeroCokernelPacketEquiv (Sum ι (Sum κ μ))
        (d9GaugeGhostZeroCokernelPacketAssoc ι κ μ packet) =
      (d9GaugeZeroCoordinatePacketAssoc ι κ μ
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum ι κ) μ) packet).1,
        d9GhostZeroCoordinatePacketAssoc ι κ μ
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum ι κ) μ) packet).2) := by
  apply Prod.ext
  · funext mode
    cases mode with
    | inl left => rfl
    | inr right =>
        cases right <;> rfl
  · funext mode
    cases mode with
    | inl left => rfl
    | inr right =>
        cases right <;> rfl

/-- The D9 combined packet has the same iterated binary splitting under either
parenthesization. -/
theorem d9GaugeGhostZeroCokernelPacketDisjointSum_assoc_naturality
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) :
    let leftOuter :=
      d9GaugeGhostZeroCokernelPacketDisjointSumEquiv
        (Sum ι κ) μ packet
    let leftInner :=
      d9GaugeGhostZeroCokernelPacketDisjointSumEquiv
        ι κ leftOuter.1
    let rightOuter :=
      d9GaugeGhostZeroCokernelPacketDisjointSumEquiv
        ι (Sum κ μ)
        (d9GaugeGhostZeroCokernelPacketAssoc ι κ μ packet)
    let rightInner :=
      d9GaugeGhostZeroCokernelPacketDisjointSumEquiv
        κ μ rightOuter.2
    (rightOuter.1, (rightInner.1, rightInner.2)) =
      (leftInner.1, (leftInner.2, leftOuter.2)) :=
  packetDisjointSumAssocLinearEquiv_split_naturality packet

/-- Combined zero-cokernel packet dimension is invariant under reassociation. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_sum_assoc
    (ι κ μ : Type*) :
    Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) =
      Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) :=
  LinearEquiv.finrank_eq (d9GaugeGhostZeroCokernelPacketAssoc ι κ μ)

/-- Gauge-coordinate packet dimension is invariant under reassociation. -/
theorem d9GaugeZeroCoordinatePacket_finrank_sum_assoc
    (ι κ μ : Type*) :
    Module.finrank Real
        (D9GaugeZeroCoordinatePacket (Sum (Sum ι κ) μ)) =
      Module.finrank Real
        (D9GaugeZeroCoordinatePacket (Sum ι (Sum κ μ))) :=
  LinearEquiv.finrank_eq (d9GaugeZeroCoordinatePacketAssoc ι κ μ)

/-- Ghost-coordinate packet dimension is invariant under reassociation. -/
theorem d9GhostZeroCoordinatePacket_finrank_sum_assoc
    (ι κ μ : Type*) :
    Module.finrank Real
        (D9GhostZeroCoordinatePacket (Sum (Sum ι κ) μ)) =
      Module.finrank Real
        (D9GhostZeroCoordinatePacket (Sum ι (Sum κ μ))) :=
  LinearEquiv.finrank_eq (d9GhostZeroCoordinatePacketAssoc ι κ μ)

/-- For finite mode types, the left-associated packet has the expected
three-family dimension formula. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_three_additive_left
    (ι κ μ : Type*) [Fintype ι] [Fintype κ] [Fintype μ] :
    Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) =
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) +
        (Module.finrank Real (D9GaugeGhostZeroCokernelPacket κ) +
          Module.finrank Real (D9GaugeGhostZeroCokernelPacket μ)) := by
  rw [d9GaugeGhostZeroCokernelPacket_finrank_disjointSum (Sum ι κ) μ,
    d9GaugeGhostZeroCokernelPacket_finrank_disjointSum ι κ]
  exact Nat.add_assoc _ _ _

/-- The right-associated packet has the same three-family dimension formula. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_three_additive_right
    (ι κ μ : Type*) [Fintype ι] [Fintype κ] [Fintype μ] :
    Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) =
      Module.finrank Real (D9GaugeGhostZeroCokernelPacket ι) +
        (Module.finrank Real (D9GaugeGhostZeroCokernelPacket κ) +
          Module.finrank Real (D9GaugeGhostZeroCokernelPacket μ)) := by
  rw [d9GaugeGhostZeroCokernelPacket_finrank_disjointSum ι (Sum κ μ),
    d9GaugeGhostZeroCokernelPacket_finrank_disjointSum κ μ]

/-- Reusable coherence certificate for reassociating three D9 zero-mode packet
families. -/
theorem d9GaugeGhostFinitePacketSumAssociativity_certificate
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) :
    (d9GaugeGhostZeroCokernelPacketAssoc ι κ μ).symm
          (d9GaugeGhostZeroCokernelPacketAssoc ι κ μ packet) = packet ∧
      d9GaugeGhostZeroCokernelPacketEquiv (Sum ι (Sum κ μ))
          (d9GaugeGhostZeroCokernelPacketAssoc ι κ μ packet) =
        (d9GaugeZeroCoordinatePacketAssoc ι κ μ
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum ι κ) μ) packet).1,
          d9GhostZeroCoordinatePacketAssoc ι κ μ
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum ι κ) μ) packet).2) ∧
      Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) =
        Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) := by
  exact ⟨(d9GaugeGhostZeroCokernelPacketAssoc ι κ μ).left_inv packet,
    d9GaugeGhostZeroCokernelPacketEquiv_assoc_naturality packet,
    d9GaugeGhostZeroCokernelPacket_finrank_sum_assoc ι κ μ⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketSumAssociativity4D
end JanusFormal
