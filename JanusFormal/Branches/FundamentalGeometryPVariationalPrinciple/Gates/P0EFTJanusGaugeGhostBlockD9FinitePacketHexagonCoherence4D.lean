import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketSumSymmetry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketSumAssociativity4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketHexagonCoherence4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketReindex4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketSumSymmetry4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketSumAssociativity4D

/-- Exchange the two labels inside the left summand while keeping the right
label fixed. -/
def d9PacketSumSwapLeftEquiv (ι κ μ : Type*) :
    Sum (Sum ι κ) μ ≃ Sum (Sum κ ι) μ where
  toFun value :=
    match value with
    | Sum.inl (Sum.inl first) => Sum.inl (Sum.inr first)
    | Sum.inl (Sum.inr second) => Sum.inl (Sum.inl second)
    | Sum.inr third => Sum.inr third
  invFun value :=
    match value with
    | Sum.inl (Sum.inl second) => Sum.inl (Sum.inr second)
    | Sum.inl (Sum.inr first) => Sum.inl (Sum.inl first)
    | Sum.inr third => Sum.inr third
  left_inv value := by
    cases value with
    | inl pair =>
        cases pair <;> rfl
    | inr third => rfl
  right_inv value := by
    cases value with
    | inl pair =>
        cases pair <;> rfl
    | inr third => rfl

/-- Exchange the two labels inside the right summand while keeping the left
label fixed. -/
def d9PacketSumSwapRightEquiv (ι κ μ : Type*) :
    Sum ι (Sum κ μ) ≃ Sum ι (Sum μ κ) where
  toFun value :=
    match value with
    | Sum.inl first => Sum.inl first
    | Sum.inr (Sum.inl second) => Sum.inr (Sum.inr second)
    | Sum.inr (Sum.inr third) => Sum.inr (Sum.inl third)
  invFun value :=
    match value with
    | Sum.inl first => Sum.inl first
    | Sum.inr (Sum.inl third) => Sum.inr (Sum.inr third)
    | Sum.inr (Sum.inr second) => Sum.inr (Sum.inl second)
  left_inv value := by
    cases value with
    | inl first => rfl
    | inr pair =>
        cases pair <;> rfl
  right_inv value := by
    cases value with
    | inl first => rfl
    | inr pair =>
        cases pair <;> rfl

/-- Direct route for moving the first label across a right-associated pair. -/
def d9PacketSumHexagonLeftShortEquiv (ι κ μ : Type*) :
    Sum ι (Sum κ μ) ≃ Sum κ (Sum μ ι) :=
  (d9PacketSumSwapEquiv ι (Sum κ μ)).trans
    (d9PacketSumAssocEquiv κ μ ι)

/-- Expanded route for moving the first label across the two members of the
right-associated pair one at a time. -/
def d9PacketSumHexagonLeftLongEquiv (ι κ μ : Type*) :
    Sum ι (Sum κ μ) ≃ Sum κ (Sum μ ι) :=
  ((((d9PacketSumAssocEquiv ι κ μ).symm).trans
      (d9PacketSumSwapLeftEquiv ι κ μ)).trans
    (d9PacketSumAssocEquiv κ ι μ)).trans
      (d9PacketSumSwapRightEquiv κ ι μ)

/-- The first braiding hexagon commutes on three disjoint labels. -/
theorem d9PacketSumHexagonLeft_coherence (ι κ μ : Type*) :
    d9PacketSumHexagonLeftShortEquiv ι κ μ =
      d9PacketSumHexagonLeftLongEquiv ι κ μ := by
  apply Equiv.ext
  intro value
  cases value with
  | inl first => rfl
  | inr pair =>
      cases pair <;> rfl

/-- Direct route for moving the right label across a left-associated pair. -/
def d9PacketSumHexagonRightShortEquiv (ι κ μ : Type*) :
    Sum (Sum ι κ) μ ≃ Sum μ (Sum ι κ) :=
  d9PacketSumSwapEquiv (Sum ι κ) μ

/-- Expanded route for moving the right label across the two members of the
left-associated pair one at a time. -/
def d9PacketSumHexagonRightLongEquiv (ι κ μ : Type*) :
    Sum (Sum ι κ) μ ≃ Sum μ (Sum ι κ) :=
  (((((d9PacketSumAssocEquiv ι κ μ).trans
      (d9PacketSumSwapRightEquiv ι κ μ)).trans
    ((d9PacketSumAssocEquiv ι μ κ).symm)).trans
      (d9PacketSumSwapLeftEquiv ι μ κ)).trans
        (d9PacketSumAssocEquiv μ ι κ)

/-- The second braiding hexagon commutes on three disjoint labels. -/
theorem d9PacketSumHexagonRight_coherence (ι κ μ : Type*) :
    d9PacketSumHexagonRightShortEquiv ι κ μ =
      d9PacketSumHexagonRightLongEquiv ι κ μ := by
  apply Equiv.ext
  intro value
  cases value with
  | inl pair =>
      cases pair <;> rfl
  | inr third => rfl

/-- Pull a linear packet along the direct route of the first hexagon. -/
def packetDisjointSumHexagonLeftShortLinearEquiv
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V] :
    (Sum ι (Sum κ μ) → V) ≃ₗ[Real]
      (Sum κ (Sum μ ι) → V) :=
  packetReindexLinearEquiv
    (d9PacketSumHexagonLeftShortEquiv ι κ μ).symm

/-- Pull a linear packet along the expanded route of the first hexagon. -/
def packetDisjointSumHexagonLeftLongLinearEquiv
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V] :
    (Sum ι (Sum κ μ) → V) ≃ₗ[Real]
      (Sum κ (Sum μ ι) → V) :=
  packetReindexLinearEquiv
    (d9PacketSumHexagonLeftLongEquiv ι κ μ).symm

/-- Every linear packet is transported identically along the two routes of the
first hexagon. -/
theorem packetDisjointSumHexagonLeft_coherence
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum ι (Sum κ μ) → V) :
    packetDisjointSumHexagonLeftShortLinearEquiv packet =
      packetDisjointSumHexagonLeftLongLinearEquiv packet := by
  unfold packetDisjointSumHexagonLeftShortLinearEquiv
    packetDisjointSumHexagonLeftLongLinearEquiv
  rw [d9PacketSumHexagonLeft_coherence]

/-- Pull a linear packet along the direct route of the second hexagon. -/
def packetDisjointSumHexagonRightShortLinearEquiv
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V] :
    (Sum (Sum ι κ) μ → V) ≃ₗ[Real]
      (Sum μ (Sum ι κ) → V) :=
  packetReindexLinearEquiv
    (d9PacketSumHexagonRightShortEquiv ι κ μ).symm

/-- Pull a linear packet along the expanded route of the second hexagon. -/
def packetDisjointSumHexagonRightLongLinearEquiv
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V] :
    (Sum (Sum ι κ) μ → V) ≃ₗ[Real]
      (Sum μ (Sum ι κ) → V) :=
  packetReindexLinearEquiv
    (d9PacketSumHexagonRightLongEquiv ι κ μ).symm

/-- Every linear packet is transported identically along the two routes of the
second hexagon. -/
theorem packetDisjointSumHexagonRight_coherence
    {ι κ μ V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum ι κ) μ → V) :
    packetDisjointSumHexagonRightShortLinearEquiv packet =
      packetDisjointSumHexagonRightLongLinearEquiv packet := by
  unfold packetDisjointSumHexagonRightShortLinearEquiv
    packetDisjointSumHexagonRightLongLinearEquiv
  rw [d9PacketSumHexagonRight_coherence]

/-- Combined D9 packet transported along the direct first-hexagon route. -/
def d9GaugeGhostZeroCokernelPacketHexagonLeftShort (ι κ μ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ)) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum κ (Sum μ ι)) :=
  d9GaugeGhostZeroCokernelPacketReindex
    (d9PacketSumHexagonLeftShortEquiv ι κ μ).symm

/-- Combined D9 packet transported along the expanded first-hexagon route. -/
def d9GaugeGhostZeroCokernelPacketHexagonLeftLong (ι κ μ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ)) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum κ (Sum μ ι)) :=
  d9GaugeGhostZeroCokernelPacketReindex
    (d9PacketSumHexagonLeftLongEquiv ι κ μ).symm

/-- Gauge packet transported along the direct first-hexagon route. -/
def d9GaugeZeroCoordinatePacketHexagonLeftShort (ι κ μ : Type*) :
    D9GaugeZeroCoordinatePacket (Sum ι (Sum κ μ)) ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket (Sum κ (Sum μ ι)) :=
  d9GaugeZeroCoordinatePacketReindex
    (d9PacketSumHexagonLeftShortEquiv ι κ μ).symm

/-- Ghost packet transported along the direct first-hexagon route. -/
def d9GhostZeroCoordinatePacketHexagonLeftShort (ι κ μ : Type*) :
    D9GhostZeroCoordinatePacket (Sum ι (Sum κ μ)) ≃ₗ[Real]
      D9GhostZeroCoordinatePacket (Sum κ (Sum μ ι)) :=
  d9GhostZeroCoordinatePacketReindex
    (d9PacketSumHexagonLeftShortEquiv ι κ μ).symm

/-- The combined D9 packet satisfies the first hexagon identity. -/
theorem d9GaugeGhostZeroCokernelPacket_hexagonLeft
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) :
    d9GaugeGhostZeroCokernelPacketHexagonLeftShort ι κ μ packet =
      d9GaugeGhostZeroCokernelPacketHexagonLeftLong ι κ μ packet := by
  unfold d9GaugeGhostZeroCokernelPacketHexagonLeftShort
    d9GaugeGhostZeroCokernelPacketHexagonLeftLong
  rw [d9PacketSumHexagonLeft_coherence]

/-- Gauge--ghost splitting is natural along the first hexagon. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_hexagonLeft_naturality
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) :
    d9GaugeGhostZeroCokernelPacketEquiv (Sum κ (Sum μ ι))
        (d9GaugeGhostZeroCokernelPacketHexagonLeftShort ι κ μ packet) =
      (d9GaugeZeroCoordinatePacketHexagonLeftShort ι κ μ
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum ι (Sum κ μ)) packet).1,
        d9GhostZeroCoordinatePacketHexagonLeftShort ι κ μ
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum ι (Sum κ μ)) packet).2) := by
  simpa [d9GaugeGhostZeroCokernelPacketHexagonLeftShort,
    d9GaugeZeroCoordinatePacketHexagonLeftShort,
    d9GhostZeroCoordinatePacketHexagonLeftShort] using
    (d9GaugeGhostZeroCokernelPacketEquiv_reindex_naturality
      (equiv := (d9PacketSumHexagonLeftShortEquiv ι κ μ).symm) packet)

/-- Combined packet dimension is invariant across the first hexagon. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_hexagonLeft
    (ι κ μ : Type*) :
    Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) =
      Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum κ (Sum μ ι))) :=
  LinearEquiv.finrank_eq
    (d9GaugeGhostZeroCokernelPacketHexagonLeftShort ι κ μ)

/-- Combined D9 packet transported along the direct second-hexagon route. -/
def d9GaugeGhostZeroCokernelPacketHexagonRightShort (ι κ μ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum μ (Sum ι κ)) :=
  d9GaugeGhostZeroCokernelPacketReindex
    (d9PacketSumHexagonRightShortEquiv ι κ μ).symm

/-- Combined D9 packet transported along the expanded second-hexagon route. -/
def d9GaugeGhostZeroCokernelPacketHexagonRightLong (ι κ μ : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum μ (Sum ι κ)) :=
  d9GaugeGhostZeroCokernelPacketReindex
    (d9PacketSumHexagonRightLongEquiv ι κ μ).symm

/-- Gauge packet transported along the direct second-hexagon route. -/
def d9GaugeZeroCoordinatePacketHexagonRightShort (ι κ μ : Type*) :
    D9GaugeZeroCoordinatePacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket (Sum μ (Sum ι κ)) :=
  d9GaugeZeroCoordinatePacketReindex
    (d9PacketSumHexagonRightShortEquiv ι κ μ).symm

/-- Ghost packet transported along the direct second-hexagon route. -/
def d9GhostZeroCoordinatePacketHexagonRightShort (ι κ μ : Type*) :
    D9GhostZeroCoordinatePacket (Sum (Sum ι κ) μ) ≃ₗ[Real]
      D9GhostZeroCoordinatePacket (Sum μ (Sum ι κ)) :=
  d9GhostZeroCoordinatePacketReindex
    (d9PacketSumHexagonRightShortEquiv ι κ μ).symm

/-- The combined D9 packet satisfies the second hexagon identity. -/
theorem d9GaugeGhostZeroCokernelPacket_hexagonRight
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) :
    d9GaugeGhostZeroCokernelPacketHexagonRightShort ι κ μ packet =
      d9GaugeGhostZeroCokernelPacketHexagonRightLong ι κ μ packet := by
  unfold d9GaugeGhostZeroCokernelPacketHexagonRightShort
    d9GaugeGhostZeroCokernelPacketHexagonRightLong
  rw [d9PacketSumHexagonRight_coherence]

/-- Gauge--ghost splitting is natural along the second hexagon. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_hexagonRight_naturality
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) :
    d9GaugeGhostZeroCokernelPacketEquiv (Sum μ (Sum ι κ))
        (d9GaugeGhostZeroCokernelPacketHexagonRightShort ι κ μ packet) =
      (d9GaugeZeroCoordinatePacketHexagonRightShort ι κ μ
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum ι κ) μ) packet).1,
        d9GhostZeroCoordinatePacketHexagonRightShort ι κ μ
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum ι κ) μ) packet).2) := by
  simpa [d9GaugeGhostZeroCokernelPacketHexagonRightShort,
    d9GaugeZeroCoordinatePacketHexagonRightShort,
    d9GhostZeroCoordinatePacketHexagonRightShort] using
    (d9GaugeGhostZeroCokernelPacketEquiv_reindex_naturality
      (equiv := (d9PacketSumHexagonRightShortEquiv ι κ μ).symm) packet)

/-- Combined packet dimension is invariant across the second hexagon. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_hexagonRight
    (ι κ μ : Type*) :
    Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) =
      Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum μ (Sum ι κ))) :=
  LinearEquiv.finrank_eq
    (d9GaugeGhostZeroCokernelPacketHexagonRightShort ι κ μ)

/-- Closure certificate for the first braiding hexagon. -/
theorem d9GaugeGhostFinitePacketHexagonLeft_certificate
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) :
    d9GaugeGhostZeroCokernelPacketHexagonLeftShort ι κ μ packet =
        d9GaugeGhostZeroCokernelPacketHexagonLeftLong ι κ μ packet ∧
      d9GaugeGhostZeroCokernelPacketEquiv (Sum κ (Sum μ ι))
          (d9GaugeGhostZeroCokernelPacketHexagonLeftShort ι κ μ packet) =
        (d9GaugeZeroCoordinatePacketHexagonLeftShort ι κ μ
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum ι (Sum κ μ)) packet).1,
          d9GhostZeroCoordinatePacketHexagonLeftShort ι κ μ
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum ι (Sum κ μ)) packet).2) ∧
      Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ μ))) =
        Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum κ (Sum μ ι))) := by
  exact ⟨d9GaugeGhostZeroCokernelPacket_hexagonLeft packet,
    d9GaugeGhostZeroCokernelPacketEquiv_hexagonLeft_naturality packet,
    d9GaugeGhostZeroCokernelPacket_finrank_hexagonLeft ι κ μ⟩

/-- Closure certificate for the second braiding hexagon. -/
theorem d9GaugeGhostFinitePacketHexagonRight_certificate
    {ι κ μ : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) :
    d9GaugeGhostZeroCokernelPacketHexagonRightShort ι κ μ packet =
        d9GaugeGhostZeroCokernelPacketHexagonRightLong ι κ μ packet ∧
      d9GaugeGhostZeroCokernelPacketEquiv (Sum μ (Sum ι κ))
          (d9GaugeGhostZeroCokernelPacketHexagonRightShort ι κ μ packet) =
        (d9GaugeZeroCoordinatePacketHexagonRightShort ι κ μ
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum ι κ) μ) packet).1,
          d9GhostZeroCoordinatePacketHexagonRightShort ι κ μ
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum ι κ) μ) packet).2) ∧
      Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum (Sum ι κ) μ)) =
        Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum μ (Sum ι κ))) := by
  exact ⟨d9GaugeGhostZeroCokernelPacket_hexagonRight packet,
    d9GaugeGhostZeroCokernelPacketEquiv_hexagonRight_naturality packet,
    d9GaugeGhostZeroCokernelPacket_finrank_hexagonRight ι κ μ⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketHexagonCoherence4D
end JanusFormal
