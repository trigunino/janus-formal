import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketGeneralizedInverse4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketHodgeDecomposition4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketGeneralizedInverse4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- The regular packet component, equivalently the range-support submodule. -/
abbrev D9GaugeGhostPacketRegularData {ι : Type*}
    (covector : ι → TangentVector3) :=
  d9GaugeGhostPacketZeroVanishingSubmodule covector

/-- Canonical Hodge-style splitting of every finite D9 packet into its
zero-symbol data and its regular/range component. -/
def d9GaugeGhostFinitePacketHodgeEquiv {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι ≃ₗ[Real]
      (D9GaugeGhostPacketZeroModeData covector ×
        D9GaugeGhostPacketRegularData covector) where
  toFun packet :=
    (d9GaugeGhostPacketZeroRestriction covector packet,
      ⟨d9GaugeGhostFinitePacketRegularProjection covector packet,
        d9GaugeGhostFinitePacketRegularProjection_mem_zeroVanishing
          covector packet⟩)
  invFun separated :=
    d9GaugeGhostPacketZeroExtension covector separated.1 + separated.2.1
  left_inv packet := by
    exact d9GaugeGhostFinitePacket_zero_add_regular covector packet
  right_inv separated := by
    apply Prod.ext
    · have hRegularKernel : separated.2.1 ∈
          LinearMap.ker (d9GaugeGhostPacketZeroRestriction covector) := by
        rw [d9GaugeGhostPacketZeroRestriction_ker]
        exact separated.2.2
      have hRegularRestriction :
          d9GaugeGhostPacketZeroRestriction covector separated.2.1 = 0 :=
        LinearMap.mem_ker.mp hRegularKernel
      calc
        d9GaugeGhostPacketZeroRestriction covector
            (d9GaugeGhostPacketZeroExtension covector separated.1 +
              separated.2.1) =
            d9GaugeGhostPacketZeroRestriction covector
                (d9GaugeGhostPacketZeroExtension covector separated.1) +
              d9GaugeGhostPacketZeroRestriction covector separated.2.1 := by
              rw [map_add]
        _ = separated.1 + 0 := by
          rw [d9GaugeGhostPacketZeroRestriction_extension,
            hRegularRestriction]
        _ = separated.1 := add_zero _
    · apply Subtype.ext
      have hExtensionKernel :
          d9GaugeGhostPacketZeroExtension covector separated.1 ∈
            LinearMap.ker
              (d9GaugeGhostFinitePacketRegularProjection covector) := by
        rw [d9GaugeGhostFinitePacketRegularProjection_ker]
        exact d9GaugeGhostPacketZeroExtension_mem_zeroSupported
          covector separated.1
      have hExtensionZero :
          d9GaugeGhostFinitePacketRegularProjection covector
              (d9GaugeGhostPacketZeroExtension covector separated.1) = 0 :=
        LinearMap.mem_ker.mp hExtensionKernel
      have hRegularFixed :
          d9GaugeGhostFinitePacketRegularProjection covector separated.2.1 =
            separated.2.1 :=
        d9GaugeGhostFinitePacketRegularProjection_eq_self_of_mem
          covector separated.2.1 separated.2.2
      calc
        d9GaugeGhostFinitePacketRegularProjection covector
            (d9GaugeGhostPacketZeroExtension covector separated.1 +
              separated.2.1) =
            d9GaugeGhostFinitePacketRegularProjection covector
                (d9GaugeGhostPacketZeroExtension covector separated.1) +
              d9GaugeGhostFinitePacketRegularProjection covector
                separated.2.1 := by
              rw [map_add]
        _ = 0 + separated.2.1 := by rw [hExtensionZero, hRegularFixed]
        _ = separated.2.1 := zero_add _
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  map_smul' scalar packet := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

@[simp] theorem d9GaugeGhostFinitePacketHodgeEquiv_fst
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    (d9GaugeGhostFinitePacketHodgeEquiv covector packet).1 =
      d9GaugeGhostPacketZeroRestriction covector packet := rfl

@[simp] theorem d9GaugeGhostFinitePacketHodgeEquiv_snd_coe
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2.1 =
      d9GaugeGhostFinitePacketRegularProjection covector packet := rfl

@[simp] theorem d9GaugeGhostFinitePacketHodgeEquiv_symm_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (separated : D9GaugeGhostPacketZeroModeData covector ×
      D9GaugeGhostPacketRegularData covector) :
    (d9GaugeGhostFinitePacketHodgeEquiv covector).symm separated =
      d9GaugeGhostPacketZeroExtension covector separated.1 +
        separated.2.1 := rfl

/-- The symbol restricts to an endomorphism of the regular packet component. -/
def d9GaugeGhostFinitePacketRegularSymbol {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostPacketRegularData covector →ₗ[Real]
      D9GaugeGhostPacketRegularData covector where
  toFun packet :=
    ⟨d9GaugeGhostFinitePacketSymbol covector packet.1, by
      intro mode hZero
      simp [d9GaugeGhostFinitePacketSymbol_apply, hZero]⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar packet := by
    apply Subtype.ext
    simp

/-- The generalized inverse also preserves the regular packet component. -/
def d9GaugeGhostFinitePacketRegularGeneralizedInverse {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostPacketRegularData covector →ₗ[Real]
      D9GaugeGhostPacketRegularData covector where
  toFun packet :=
    ⟨d9GaugeGhostFinitePacketGeneralizedInverse covector packet.1, by
      intro mode hZero
      simp [d9GaugeGhostFinitePacketGeneralizedInverse, hZero]⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar packet := by
    apply Subtype.ext
    simp

/-- On the regular component, the symbol after the generalized inverse is the
identity. -/
theorem d9GaugeGhostFinitePacketRegularSymbol_inverse_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostPacketRegularData covector) :
    d9GaugeGhostFinitePacketRegularSymbol covector
        (d9GaugeGhostFinitePacketRegularGeneralizedInverse covector packet) =
      packet := by
  apply Subtype.ext
  change d9GaugeGhostFinitePacketSymbol covector
      (d9GaugeGhostFinitePacketGeneralizedInverse covector packet.1) = packet.1
  rw [d9GaugeGhostFinitePacketSymbol_generalizedInverse]
  exact d9GaugeGhostFinitePacketRegularProjection_eq_self_of_mem
    covector packet.1 packet.2

/-- On the regular component, the generalized inverse after the symbol is also
the identity. -/
theorem d9GaugeGhostFinitePacketRegularSymbol_apply_inverse
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostPacketRegularData covector) :
    d9GaugeGhostFinitePacketRegularGeneralizedInverse covector
        (d9GaugeGhostFinitePacketRegularSymbol covector packet) = packet := by
  apply Subtype.ext
  change d9GaugeGhostFinitePacketGeneralizedInverse covector
      (d9GaugeGhostFinitePacketSymbol covector packet.1) = packet.1
  rw [d9GaugeGhostFinitePacketGeneralizedInverse_symbol]
  exact d9GaugeGhostFinitePacketRegularProjection_eq_self_of_mem
    covector packet.1 packet.2

/-- The restriction of the D9 packet symbol to its regular component is a
linear automorphism. -/
def d9GaugeGhostFinitePacketRegularSymbolEquiv {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostPacketRegularData covector ≃ₗ[Real]
      D9GaugeGhostPacketRegularData covector where
  toFun := d9GaugeGhostFinitePacketRegularSymbol covector
  invFun := d9GaugeGhostFinitePacketRegularGeneralizedInverse covector
  left_inv := d9GaugeGhostFinitePacketRegularSymbol_apply_inverse covector
  right_inv := d9GaugeGhostFinitePacketRegularSymbol_inverse_apply covector
  map_add' first second :=
    (d9GaugeGhostFinitePacketRegularSymbol covector).map_add first second
  map_smul' scalar packet :=
    (d9GaugeGhostFinitePacketRegularSymbol covector).map_smul scalar packet

/-- Under the Hodge splitting, the packet symbol is zero on the zero-mode
factor and invertible on the regular factor. -/
theorem d9GaugeGhostFinitePacketHodgeEquiv_symbol
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketHodgeEquiv covector
        (d9GaugeGhostFinitePacketSymbol covector packet) =
      (0,
        d9GaugeGhostFinitePacketRegularSymbol covector
          (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2) := by
  apply Prod.ext
  · funext mode
    change d9GaugeGhostFinitePacketSymbol covector packet mode.1 = 0
    simp [d9GaugeGhostFinitePacketSymbol_apply, mode.property]
  · apply Subtype.ext
    classical
    funext mode
    by_cases hZero : covector mode = zeroTangent
    · simp [d9GaugeGhostFinitePacketSymbol_apply, hZero]
    · have hNorm : normSquared (covector mode) ≠ 0 :=
        ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hZero)
      simp [d9GaugeGhostFinitePacketSymbol_apply,
        d9GaugeGhostFinitePacketRegularProjection,
        d9GaugeGhostFinitePacketGeneralizedInverse,
        hZero, smul_smul, hNorm]

/-- The packet dimension splits into zero-mode and regular contributions. -/
theorem d9GaugeGhostFinitePacketHodge_finrank
    {ι : Type*} [Fintype ι] (covector : ι → TangentVector3) :
    Module.finrank Real (D9GaugeGhostFinitePacket ι) =
      Module.finrank Real (D9GaugeGhostPacketZeroModeData covector) +
        Module.finrank Real (D9GaugeGhostPacketRegularData covector) := by
  classical
  letI : Fintype (D9GaugeGhostPacketZeroMode covector) := Fintype.ofFinite _
  calc
    Module.finrank Real (D9GaugeGhostFinitePacket ι) =
        Module.finrank Real
          (D9GaugeGhostPacketZeroModeData covector ×
            D9GaugeGhostPacketRegularData covector) :=
      LinearEquiv.finrank_eq (d9GaugeGhostFinitePacketHodgeEquiv covector)
    _ = Module.finrank Real (D9GaugeGhostPacketZeroModeData covector) +
        Module.finrank Real (D9GaugeGhostPacketRegularData covector) :=
      Module.finrank_prod

/-- Reusable Hodge decomposition and regular invertibility certificate. -/
theorem d9GaugeGhostFinitePacketHodge_certificate
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    (d9GaugeGhostFinitePacketHodgeEquiv covector).symm
          (d9GaugeGhostFinitePacketHodgeEquiv covector packet) = packet ∧
      d9GaugeGhostFinitePacketZeroProjection covector packet +
          d9GaugeGhostFinitePacketRegularProjection covector packet = packet ∧
      d9GaugeGhostFinitePacketRegularSymbol covector
          (d9GaugeGhostFinitePacketRegularGeneralizedInverse covector
            (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2) =
        (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2 ∧
      d9GaugeGhostFinitePacketRegularGeneralizedInverse covector
          (d9GaugeGhostFinitePacketRegularSymbol covector
            (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2) =
        (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2 := by
  exact ⟨(d9GaugeGhostFinitePacketHodgeEquiv covector).left_inv packet,
    d9GaugeGhostFinitePacket_zero_add_regular covector packet,
    d9GaugeGhostFinitePacketRegularSymbol_inverse_apply covector
      (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2,
    d9GaugeGhostFinitePacketRegularSymbol_apply_inverse covector
      (d9GaugeGhostFinitePacketHodgeEquiv covector packet).2⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketHodgeDecomposition4D
end JanusFormal
