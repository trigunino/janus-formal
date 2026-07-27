import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketFredholmIndex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketHodgeDecomposition4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketCokernelEquiv4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketGeneralizedInverse4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketHodgeDecomposition4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketFredholmIndex4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

private theorem d9GaugeGhostFinitePacketSymbol_range_le_zeroRestriction_ker
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) ≤
      LinearMap.ker (d9GaugeGhostPacketZeroRestriction covector) := by
  rw [d9GaugeGhostFinitePacketSymbol_range_eq_zeroVanishing,
    d9GaugeGhostPacketZeroRestriction_ker]

/-- Restriction to zero-symbol modes descends canonically through the actual
finite-packet cokernel. -/
def d9GaugeGhostFinitePacketCokernelToZeroModeData
    {ι : Type*} (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacketCokernel covector →ₗ[Real]
      D9GaugeGhostPacketZeroModeData covector :=
  (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)).liftQ
    (d9GaugeGhostPacketZeroRestriction covector)
    (d9GaugeGhostFinitePacketSymbol_range_le_zeroRestriction_ker covector)

/-- Zero-mode data defines a cokernel class by zero extension followed by the
canonical quotient projection. -/
def d9GaugeGhostZeroModeDataToFinitePacketCokernel
    {ι : Type*} (covector : ι → TangentVector3) :
    D9GaugeGhostPacketZeroModeData covector →ₗ[Real]
      D9GaugeGhostFinitePacketCokernel covector :=
  (d9GaugeGhostFinitePacketCokernelProjection covector).comp
    (d9GaugeGhostPacketZeroExtension covector)

@[simp] theorem d9GaugeGhostFinitePacketCokernelToZeroModeData_projection
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketCokernelToZeroModeData covector
        (d9GaugeGhostFinitePacketCokernelProjection covector packet) =
      d9GaugeGhostPacketZeroRestriction covector packet := by
  rfl

@[simp] theorem d9GaugeGhostFinitePacketCokernelToZeroModeData_zeroExtension
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostPacketZeroModeData covector) :
    d9GaugeGhostFinitePacketCokernelToZeroModeData covector
        (d9GaugeGhostZeroModeDataToFinitePacketCokernel covector packet) =
      packet := by
  simp [d9GaugeGhostZeroModeDataToFinitePacketCokernel]

/-- Every cokernel class is represented by the zero extension of its zero-mode
data. -/
theorem d9GaugeGhostZeroModeDataToFinitePacketCokernel_toZeroModeData
    {ι : Type*} (covector : ι → TangentVector3)
    (cokernel : D9GaugeGhostFinitePacketCokernel covector) :
    d9GaugeGhostZeroModeDataToFinitePacketCokernel covector
        (d9GaugeGhostFinitePacketCokernelToZeroModeData covector cokernel) =
      cokernel := by
  obtain ⟨packet, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector)) cokernel
  change (Submodule.Quotient.mk
      (d9GaugeGhostPacketZeroExtension covector
        (d9GaugeGhostPacketZeroRestriction covector packet)) :
      D9GaugeGhostFinitePacketCokernel covector) =
    Submodule.Quotient.mk packet
  apply (Submodule.Quotient.eq
    (LinearMap.range (d9GaugeGhostFinitePacketSymbol covector))).2
  rw [d9GaugeGhostFinitePacketSymbol_range_eq_zeroVanishing]
  intro mode hZero
  simp [d9GaugeGhostPacketZeroExtension,
    d9GaugeGhostPacketZeroRestriction, hZero]

/-- The actual finite-packet cokernel is canonically linearly equivalent to the
packet of zero-symbol data, not merely equal to it in dimension. -/
def d9GaugeGhostFinitePacketCokernelEquivZeroModeData
    {ι : Type*} (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacketCokernel covector ≃ₗ[Real]
      D9GaugeGhostPacketZeroModeData covector where
  toFun := d9GaugeGhostFinitePacketCokernelToZeroModeData covector
  invFun := d9GaugeGhostZeroModeDataToFinitePacketCokernel covector
  left_inv :=
    d9GaugeGhostZeroModeDataToFinitePacketCokernel_toZeroModeData covector
  right_inv :=
    d9GaugeGhostFinitePacketCokernelToZeroModeData_zeroExtension covector
  map_add' first second :=
    (d9GaugeGhostFinitePacketCokernelToZeroModeData covector).map_add first second
  map_smul' scalar cokernel :=
    (d9GaugeGhostFinitePacketCokernelToZeroModeData covector).map_smul
      scalar cokernel

/-- Kernel and cokernel are canonically equivalent through their common
zero-symbol packet data. -/
def d9GaugeGhostFinitePacketKernelEquivCokernel
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) ≃ₗ[Real]
      D9GaugeGhostFinitePacketCokernel covector :=
  (d9GaugeGhostFinitePacketKernelEquivZeroModeData covector).trans
    (d9GaugeGhostFinitePacketCokernelEquivZeroModeData covector).symm

@[simp] theorem d9GaugeGhostFinitePacketKernelEquivCokernel_toZeroModeData
    {ι : Type*} (covector : ι → TangentVector3)
    (kernel : LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) :
    d9GaugeGhostFinitePacketCokernelEquivZeroModeData covector
        (d9GaugeGhostFinitePacketKernelEquivCokernel covector kernel) =
      d9GaugeGhostFinitePacketKernelEquivZeroModeData covector kernel := by
  simp [d9GaugeGhostFinitePacketKernelEquivCokernel]

/-- Canonical zero-supported representative of a packet cokernel class. -/
def d9GaugeGhostFinitePacketCokernelCanonicalRepresentative
    {ι : Type*} (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacketCokernel covector →ₗ[Real]
      D9GaugeGhostFinitePacket ι :=
  (d9GaugeGhostPacketZeroExtension covector).comp
    (d9GaugeGhostFinitePacketCokernelToZeroModeData covector)

/-- The canonical representative maps back to its original cokernel class. -/
theorem d9GaugeGhostFinitePacketCokernelCanonicalRepresentative_projection
    {ι : Type*} (covector : ι → TangentVector3)
    (cokernel : D9GaugeGhostFinitePacketCokernel covector) :
    d9GaugeGhostFinitePacketCokernelProjection covector
        (d9GaugeGhostFinitePacketCokernelCanonicalRepresentative
          covector cokernel) = cokernel := by
  exact d9GaugeGhostZeroModeDataToFinitePacketCokernel_toZeroModeData
    covector cokernel

/-- The canonical cokernel representative is supported exactly on zero-symbol
modes. -/
theorem d9GaugeGhostFinitePacketCokernelCanonicalRepresentative_mem_kernel
    {ι : Type*} (covector : ι → TangentVector3)
    (cokernel : D9GaugeGhostFinitePacketCokernel covector) :
    d9GaugeGhostFinitePacketCokernelCanonicalRepresentative covector cokernel ∈
      LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) := by
  rw [d9GaugeGhostFinitePacketSymbol_ker_eq_zeroSupported]
  exact d9GaugeGhostPacketZeroExtension_mem_zeroSupported covector
    (d9GaugeGhostFinitePacketCokernelToZeroModeData covector cokernel)

/-- Zero-supported representatives of the same cokernel class are unique. -/
theorem d9GaugeGhostFinitePacketCokernel_zeroSupportedRepresentative_unique
    {ι : Type*} (covector : ι → TangentVector3)
    (first second : D9GaugeGhostFinitePacket ι)
    (hFirst : first ∈ d9GaugeGhostPacketZeroSupportedSubmodule covector)
    (hSecond : second ∈ d9GaugeGhostPacketZeroSupportedSubmodule covector)
    (hClass : d9GaugeGhostFinitePacketCokernelProjection covector first =
      d9GaugeGhostFinitePacketCokernelProjection covector second) :
    first = second := by
  have hRestriction :
      d9GaugeGhostPacketZeroRestriction covector first =
        d9GaugeGhostPacketZeroRestriction covector second := by
    simpa using congrArg
      (d9GaugeGhostFinitePacketCokernelToZeroModeData covector) hClass
  calc
    first = d9GaugeGhostFinitePacketZeroProjection covector first :=
      (d9GaugeGhostFinitePacketZeroProjection_eq_self_of_mem
        covector first hFirst).symm
    _ = d9GaugeGhostPacketZeroExtension covector
        (d9GaugeGhostPacketZeroRestriction covector first) := rfl
    _ = d9GaugeGhostPacketZeroExtension covector
        (d9GaugeGhostPacketZeroRestriction covector second) := by
      rw [hRestriction]
    _ = d9GaugeGhostFinitePacketZeroProjection covector second := rfl
    _ = second :=
      d9GaugeGhostFinitePacketZeroProjection_eq_self_of_mem
        covector second hSecond

/-- The symbol image is exactly the kernel of zero-mode restriction. -/
theorem d9GaugeGhostFinitePacket_shortExact_middle
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) =
      LinearMap.ker (d9GaugeGhostPacketZeroRestriction covector) := by
  rw [d9GaugeGhostFinitePacketSymbol_range_eq_zeroVanishing,
    d9GaugeGhostPacketZeroRestriction_ker]

/-- Zero-mode restriction is surjective. -/
theorem d9GaugeGhostPacketZeroRestriction_surjective
    {ι : Type*} (covector : ι → TangentVector3) :
    Function.Surjective (d9GaugeGhostPacketZeroRestriction covector) := by
  intro packet
  exact ⟨d9GaugeGhostPacketZeroExtension covector packet,
    d9GaugeGhostPacketZeroRestriction_extension covector packet⟩

/-- Full structural closure certificate: split exactness, a canonical cokernel
normal form, and a canonical kernel--cokernel equivalence. -/
theorem d9GaugeGhostFinitePacketCokernelEquiv_certificate
    {ι : Type*} (covector : ι → TangentVector3)
    (cokernel : D9GaugeGhostFinitePacketCokernel covector)
    (kernel : LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector)) :
    LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) =
        LinearMap.ker (d9GaugeGhostPacketZeroRestriction covector) ∧
      Function.Surjective (d9GaugeGhostPacketZeroRestriction covector) ∧
      d9GaugeGhostFinitePacketCokernelProjection covector
          (d9GaugeGhostFinitePacketCokernelCanonicalRepresentative
            covector cokernel) = cokernel ∧
      d9GaugeGhostFinitePacketCokernelEquivZeroModeData covector
          (d9GaugeGhostFinitePacketKernelEquivCokernel covector kernel) =
        d9GaugeGhostFinitePacketKernelEquivZeroModeData covector kernel := by
  exact ⟨d9GaugeGhostFinitePacket_shortExact_middle covector,
    d9GaugeGhostPacketZeroRestriction_surjective covector,
    d9GaugeGhostFinitePacketCokernelCanonicalRepresentative_projection
      covector cokernel,
    d9GaugeGhostFinitePacketKernelEquivCokernel_toZeroModeData
      covector kernel⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketCokernelEquiv4D
end JanusFormal
