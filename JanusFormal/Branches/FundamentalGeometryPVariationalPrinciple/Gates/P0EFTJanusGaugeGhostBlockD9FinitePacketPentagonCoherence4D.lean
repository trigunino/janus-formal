import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketSumAssociativity4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketPentagonCoherence4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketReindex4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketSumAssociativity4D

/-- Reassociate the left three labels while leaving the fourth label fixed. -/
def d9PacketSumAssocLeftEquiv (ι κ μ ν : Type*) :
    Sum (Sum (Sum ι κ) μ) ν ≃ Sum (Sum ι (Sum κ μ)) ν where
  toFun value :=
    match value with
    | Sum.inl (Sum.inl (Sum.inl first)) => Sum.inl (Sum.inl first)
    | Sum.inl (Sum.inl (Sum.inr second)) =>
        Sum.inl (Sum.inr (Sum.inl second))
    | Sum.inl (Sum.inr third) => Sum.inl (Sum.inr (Sum.inr third))
    | Sum.inr fourth => Sum.inr fourth
  invFun value :=
    match value with
    | Sum.inl (Sum.inl first) => Sum.inl (Sum.inl (Sum.inl first))
    | Sum.inl (Sum.inr (Sum.inl second)) =>
        Sum.inl (Sum.inl (Sum.inr second))
    | Sum.inl (Sum.inr (Sum.inr third)) => Sum.inl (Sum.inr third)
    | Sum.inr fourth => Sum.inr fourth
  left_inv value := by
    cases value with
    | inl left =>
        cases left with
        | inl pair =>
            cases pair <;> rfl
        | inr third => rfl
    | inr fourth => rfl
  right_inv value := by
    cases value with
    | inl left =>
        cases left with
        | inl first => rfl
        | inr rest =>
            cases rest <;> rfl
    | inr fourth => rfl

/-- Reassociate the right three labels while leaving the first label fixed. -/
def d9PacketSumAssocRightEquiv (ι κ μ ν : Type*) :
    Sum ι (Sum (Sum κ μ) ν) ≃ Sum ι (Sum κ (Sum μ ν)) where
  toFun value :=
    match value with
    | Sum.inl first => Sum.inl first
    | Sum.inr (Sum.inl (Sum.inl second)) => Sum.inr (Sum.inl second)
    | Sum.inr (Sum.inl (Sum.inr third)) =>
        Sum.inr (Sum.inr (Sum.inl third))
    | Sum.inr (Sum.inr fourth) => Sum.inr (Sum.inr (Sum.inr fourth))
  invFun value :=
    match value with
    | Sum.inl first => Sum.inl first
    | Sum.inr (Sum.inl second) => Sum.inr (Sum.inl (Sum.inl second))
    | Sum.inr (Sum.inr (Sum.inl third)) =>
        Sum.inr (Sum.inl (Sum.inr third))
    | Sum.inr (Sum.inr (Sum.inr fourth)) => Sum.inr (Sum.inr fourth)
  left_inv value := by
    cases value with
    | inl first => rfl
    | inr rest =>
        cases rest with
        | inl pair =>
            cases pair <;> rfl
        | inr fourth => rfl
  right_inv value := by
    cases value with
    | inl first => rfl
    | inr rest =>
        cases rest with
        | inl second => rfl
        | inr tail =>
            cases tail <;> rfl

/-- The two-edge route around the associativity pentagon. -/
def d9PacketSumPentagonShortEquiv (ι κ μ ν : Type*) :
    Sum (Sum (Sum ι κ) μ) ν ≃ Sum ι (Sum κ (Sum μ ν)) :=
  (d9PacketSumAssocEquiv (Sum ι κ) μ ν).trans
    (d9PacketSumAssocEquiv ι κ (Sum μ ν))

/-- The three-edge route around the associativity pentagon. -/
def d9PacketSumPentagonLongEquiv (ι κ μ ν : Type*) :
    Sum (Sum (Sum ι κ) μ) ν ≃ Sum ι (Sum κ (Sum μ ν)) :=
  (d9PacketSumAssocLeftEquiv ι κ μ ν).trans
    ((d9PacketSumAssocEquiv ι (Sum κ μ) ν).trans
      (d9PacketSumAssocRightEquiv ι κ μ ν))

/-- Mac Lane's pentagon commutes on the four disjoint mode labels. -/
theorem d9PacketSumPentagon_coherence (ι κ μ ν : Type*) :
    d9PacketSumPentagonShortEquiv ι κ μ ν =
      d9PacketSumPentagonLongEquiv ι κ μ ν := by
  apply Equiv.ext
  intro value
  cases value with
  | inl left =>
      cases left with
      | inl pair =>
          cases pair <;> rfl
      | inr third => rfl
  | inr fourth => rfl

/-- Pull packets along the two-edge pentagon route. -/
def packetDisjointSumPentagonShortLinearEquiv
    {ι κ μ ν V : Type*} [AddCommMonoid V] [Module Real V] :
    (Sum (Sum (Sum ι κ) μ) ν → V) ≃ₗ[Real]
      (Sum ι (Sum κ (Sum μ ν)) → V) :=
  packetReindexLinearEquiv (d9PacketSumPentagonShortEquiv ι κ μ ν).symm

/-- Pull packets along the three-edge pentagon route. -/
def packetDisjointSumPentagonLongLinearEquiv
    {ι κ μ ν V : Type*} [AddCommMonoid V] [Module Real V] :
    (Sum (Sum (Sum ι κ) μ) ν → V) ≃ₗ[Real]
      (Sum ι (Sum κ (Sum μ ν)) → V) :=
  packetReindexLinearEquiv (d9PacketSumPentagonLongEquiv ι κ μ ν).symm

/-- Every linear packet is transported identically along the two pentagon
routes. -/
theorem packetDisjointSumPentagon_coherence
    {ι κ μ ν V : Type*} [AddCommMonoid V] [Module Real V]
    (packet : Sum (Sum (Sum ι κ) μ) ν → V) :
    packetDisjointSumPentagonShortLinearEquiv packet =
      packetDisjointSumPentagonLongLinearEquiv packet := by
  unfold packetDisjointSumPentagonShortLinearEquiv
    packetDisjointSumPentagonLongLinearEquiv
  rw [d9PacketSumPentagon_coherence]

/-- Combined D9 packet transported along the short pentagon route. -/
def d9GaugeGhostZeroCokernelPacketPentagonShort (ι κ μ ν : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum (Sum (Sum ι κ) μ) ν) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ (Sum μ ν))) :=
  d9GaugeGhostZeroCokernelPacketReindex
    (d9PacketSumPentagonShortEquiv ι κ μ ν).symm

/-- Combined D9 packet transported along the long pentagon route. -/
def d9GaugeGhostZeroCokernelPacketPentagonLong (ι κ μ ν : Type*) :
    D9GaugeGhostZeroCokernelPacket (Sum (Sum (Sum ι κ) μ) ν) ≃ₗ[Real]
      D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ (Sum μ ν))) :=
  d9GaugeGhostZeroCokernelPacketReindex
    (d9PacketSumPentagonLongEquiv ι κ μ ν).symm

/-- Gauge-coordinate packet transported along the short route. -/
def d9GaugeZeroCoordinatePacketPentagonShort (ι κ μ ν : Type*) :
    D9GaugeZeroCoordinatePacket (Sum (Sum (Sum ι κ) μ) ν) ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket (Sum ι (Sum κ (Sum μ ν))) :=
  d9GaugeZeroCoordinatePacketReindex
    (d9PacketSumPentagonShortEquiv ι κ μ ν).symm

/-- Gauge-coordinate packet transported along the long route. -/
def d9GaugeZeroCoordinatePacketPentagonLong (ι κ μ ν : Type*) :
    D9GaugeZeroCoordinatePacket (Sum (Sum (Sum ι κ) μ) ν) ≃ₗ[Real]
      D9GaugeZeroCoordinatePacket (Sum ι (Sum κ (Sum μ ν))) :=
  d9GaugeZeroCoordinatePacketReindex
    (d9PacketSumPentagonLongEquiv ι κ μ ν).symm

/-- Ghost-coordinate packet transported along the short route. -/
def d9GhostZeroCoordinatePacketPentagonShort (ι κ μ ν : Type*) :
    D9GhostZeroCoordinatePacket (Sum (Sum (Sum ι κ) μ) ν) ≃ₗ[Real]
      D9GhostZeroCoordinatePacket (Sum ι (Sum κ (Sum μ ν))) :=
  d9GhostZeroCoordinatePacketReindex
    (d9PacketSumPentagonShortEquiv ι κ μ ν).symm

/-- Ghost-coordinate packet transported along the long route. -/
def d9GhostZeroCoordinatePacketPentagonLong (ι κ μ ν : Type*) :
    D9GhostZeroCoordinatePacket (Sum (Sum (Sum ι κ) μ) ν) ≃ₗ[Real]
      D9GhostZeroCoordinatePacket (Sum ι (Sum κ (Sum μ ν))) :=
  d9GhostZeroCoordinatePacketReindex
    (d9PacketSumPentagonLongEquiv ι κ μ ν).symm

/-- The combined D9 packet satisfies the pentagon identity. -/
theorem d9GaugeGhostZeroCokernelPacket_pentagon
    {ι κ μ ν : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket
      (Sum (Sum (Sum ι κ) μ) ν)) :
    d9GaugeGhostZeroCokernelPacketPentagonShort ι κ μ ν packet =
      d9GaugeGhostZeroCokernelPacketPentagonLong ι κ μ ν packet := by
  unfold d9GaugeGhostZeroCokernelPacketPentagonShort
    d9GaugeGhostZeroCokernelPacketPentagonLong
  rw [d9PacketSumPentagon_coherence]

/-- The separated gauge packet satisfies the same pentagon identity. -/
theorem d9GaugeZeroCoordinatePacket_pentagon
    {ι κ μ ν : Type*}
    (packet : D9GaugeZeroCoordinatePacket
      (Sum (Sum (Sum ι κ) μ) ν)) :
    d9GaugeZeroCoordinatePacketPentagonShort ι κ μ ν packet =
      d9GaugeZeroCoordinatePacketPentagonLong ι κ μ ν packet := by
  unfold d9GaugeZeroCoordinatePacketPentagonShort
    d9GaugeZeroCoordinatePacketPentagonLong
  rw [d9PacketSumPentagon_coherence]

/-- The separated ghost packet satisfies the same pentagon identity. -/
theorem d9GhostZeroCoordinatePacket_pentagon
    {ι κ μ ν : Type*}
    (packet : D9GhostZeroCoordinatePacket
      (Sum (Sum (Sum ι κ) μ) ν)) :
    d9GhostZeroCoordinatePacketPentagonShort ι κ μ ν packet =
      d9GhostZeroCoordinatePacketPentagonLong ι κ μ ν packet := by
  unfold d9GhostZeroCoordinatePacketPentagonShort
    d9GhostZeroCoordinatePacketPentagonLong
  rw [d9PacketSumPentagon_coherence]

/-- Gauge--ghost splitting is natural along the short pentagon route. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_pentagonShort_naturality
    {ι κ μ ν : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket
      (Sum (Sum (Sum ι κ) μ) ν)) :
    d9GaugeGhostZeroCokernelPacketEquiv (Sum ι (Sum κ (Sum μ ν)))
        (d9GaugeGhostZeroCokernelPacketPentagonShort ι κ μ ν packet) =
      (d9GaugeZeroCoordinatePacketPentagonShort ι κ μ ν
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum (Sum ι κ) μ) ν) packet).1,
        d9GhostZeroCoordinatePacketPentagonShort ι κ μ ν
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum (Sum ι κ) μ) ν) packet).2) := by
  simpa [d9GaugeGhostZeroCokernelPacketPentagonShort,
    d9GaugeZeroCoordinatePacketPentagonShort,
    d9GhostZeroCoordinatePacketPentagonShort] using
    (d9GaugeGhostZeroCokernelPacketEquiv_reindex_naturality
      (equiv := (d9PacketSumPentagonShortEquiv ι κ μ ν).symm) packet)

/-- Gauge--ghost splitting is natural along the long pentagon route. -/
theorem d9GaugeGhostZeroCokernelPacketEquiv_pentagonLong_naturality
    {ι κ μ ν : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket
      (Sum (Sum (Sum ι κ) μ) ν)) :
    d9GaugeGhostZeroCokernelPacketEquiv (Sum ι (Sum κ (Sum μ ν)))
        (d9GaugeGhostZeroCokernelPacketPentagonLong ι κ μ ν packet) =
      (d9GaugeZeroCoordinatePacketPentagonLong ι κ μ ν
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum (Sum ι κ) μ) ν) packet).1,
        d9GhostZeroCoordinatePacketPentagonLong ι κ μ ν
          (d9GaugeGhostZeroCokernelPacketEquiv
            (Sum (Sum (Sum ι κ) μ) ν) packet).2) := by
  simpa [d9GaugeGhostZeroCokernelPacketPentagonLong,
    d9GaugeZeroCoordinatePacketPentagonLong,
    d9GhostZeroCoordinatePacketPentagonLong] using
    (d9GaugeGhostZeroCokernelPacketEquiv_reindex_naturality
      (equiv := (d9PacketSumPentagonLongEquiv ι κ μ ν).symm) packet)

/-- The combined packet dimension is invariant across the pentagon. -/
theorem d9GaugeGhostZeroCokernelPacket_finrank_pentagon
    (ι κ μ ν : Type*) :
    Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum (Sum (Sum ι κ) μ) ν)) =
      Module.finrank Real
        (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ (Sum μ ν)))) :=
  LinearEquiv.finrank_eq
    (d9GaugeGhostZeroCokernelPacketPentagonShort ι κ μ ν)

/-- The gauge packet dimension is invariant across the pentagon. -/
theorem d9GaugeZeroCoordinatePacket_finrank_pentagon
    (ι κ μ ν : Type*) :
    Module.finrank Real
        (D9GaugeZeroCoordinatePacket (Sum (Sum (Sum ι κ) μ) ν)) =
      Module.finrank Real
        (D9GaugeZeroCoordinatePacket (Sum ι (Sum κ (Sum μ ν)))) :=
  LinearEquiv.finrank_eq
    (d9GaugeZeroCoordinatePacketPentagonShort ι κ μ ν)

/-- The ghost packet dimension is invariant across the pentagon. -/
theorem d9GhostZeroCoordinatePacket_finrank_pentagon
    (ι κ μ ν : Type*) :
    Module.finrank Real
        (D9GhostZeroCoordinatePacket (Sum (Sum (Sum ι κ) μ) ν)) =
      Module.finrank Real
        (D9GhostZeroCoordinatePacket (Sum ι (Sum κ (Sum μ ν)))) :=
  LinearEquiv.finrank_eq
    (d9GhostZeroCoordinatePacketPentagonShort ι κ μ ν)

/-- Reusable D9 closure certificate for the full four-family associativity
pentagon. -/
theorem d9GaugeGhostFinitePacketPentagonCoherence_certificate
    {ι κ μ ν : Type*}
    (packet : D9GaugeGhostZeroCokernelPacket
      (Sum (Sum (Sum ι κ) μ) ν)) :
    d9GaugeGhostZeroCokernelPacketPentagonShort ι κ μ ν packet =
        d9GaugeGhostZeroCokernelPacketPentagonLong ι κ μ ν packet ∧
      d9GaugeGhostZeroCokernelPacketEquiv (Sum ι (Sum κ (Sum μ ν)))
          (d9GaugeGhostZeroCokernelPacketPentagonShort ι κ μ ν packet) =
        (d9GaugeZeroCoordinatePacketPentagonShort ι κ μ ν
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum (Sum ι κ) μ) ν) packet).1,
          d9GhostZeroCoordinatePacketPentagonShort ι κ μ ν
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum (Sum ι κ) μ) ν) packet).2) ∧
      d9GaugeGhostZeroCokernelPacketEquiv (Sum ι (Sum κ (Sum μ ν)))
          (d9GaugeGhostZeroCokernelPacketPentagonLong ι κ μ ν packet) =
        (d9GaugeZeroCoordinatePacketPentagonLong ι κ μ ν
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum (Sum ι κ) μ) ν) packet).1,
          d9GhostZeroCoordinatePacketPentagonLong ι κ μ ν
            (d9GaugeGhostZeroCokernelPacketEquiv
              (Sum (Sum (Sum ι κ) μ) ν) packet).2) ∧
      Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum (Sum (Sum ι κ) μ) ν)) =
        Module.finrank Real
          (D9GaugeGhostZeroCokernelPacket (Sum ι (Sum κ (Sum μ ν)))) := by
  exact ⟨d9GaugeGhostZeroCokernelPacket_pentagon packet,
    d9GaugeGhostZeroCokernelPacketEquiv_pentagonShort_naturality packet,
    d9GaugeGhostZeroCokernelPacketEquiv_pentagonLong_naturality packet,
    d9GaugeGhostZeroCokernelPacket_finrank_pentagon ι κ μ ν⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketPentagonCoherence4D
end JanusFormal
