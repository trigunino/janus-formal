import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketGeneralizedInverse4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- The reciprocal packet operator away from the zero-symbol support, extended
by zero on the zero modes.  It is the canonical algebraic generalized inverse
of the finite block-diagonal D9 symbol. -/
def d9GaugeGhostFinitePacketGeneralizedInverse {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real] D9GaugeGhostFinitePacket ι := by
  classical
  exact
    { toFun := fun packet mode =>
        if hZero : covector mode = zeroTangent then
          0
        else
          (normSquared (covector mode))⁻¹ • packet mode
      map_add' := by
        intro first second
        funext mode
        by_cases hZero : covector mode = zeroTangent
        · simp [hZero]
        · simp [hZero, smul_add]
      map_smul' := by
        intro scalar packet
        funext mode
        by_cases hZero : covector mode = zeroTangent
        · simp [hZero]
        · simp [hZero, smul_smul, mul_comm] }

@[simp] theorem d9GaugeGhostFinitePacketGeneralizedInverse_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) (mode : ι) :
    d9GaugeGhostFinitePacketGeneralizedInverse covector packet mode =
      if hZero : covector mode = zeroTangent then
        0
      else
        (normSquared (covector mode))⁻¹ • packet mode := rfl

/-- Projection onto the zero-symbol packet component. -/
def d9GaugeGhostFinitePacketZeroProjection {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real] D9GaugeGhostFinitePacket ι :=
  (d9GaugeGhostPacketZeroExtension covector).comp
    (d9GaugeGhostPacketZeroRestriction covector)

/-- Projection onto the nonzero-symbol/range component. -/
def d9GaugeGhostFinitePacketRegularProjection {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real] D9GaugeGhostFinitePacket ι :=
  (d9GaugeGhostFinitePacketSymbol covector).comp
    (d9GaugeGhostFinitePacketGeneralizedInverse covector)

@[simp] theorem d9GaugeGhostFinitePacketZeroProjection_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) (mode : ι) :
    d9GaugeGhostFinitePacketZeroProjection covector packet mode =
      if hZero : covector mode = zeroTangent then packet mode else 0 := by
  classical
  by_cases hZero : covector mode = zeroTangent
  · simp [d9GaugeGhostFinitePacketZeroProjection,
      d9GaugeGhostPacketZeroRestriction,
      d9GaugeGhostPacketZeroExtension, hZero]
  · simp [d9GaugeGhostFinitePacketZeroProjection,
      d9GaugeGhostPacketZeroRestriction,
      d9GaugeGhostPacketZeroExtension, hZero]

@[simp] theorem d9GaugeGhostFinitePacketRegularProjection_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) (mode : ι) :
    d9GaugeGhostFinitePacketRegularProjection covector packet mode =
      if hZero : covector mode = zeroTangent then 0 else packet mode := by
  classical
  by_cases hZero : covector mode = zeroTangent
  · simp [d9GaugeGhostFinitePacketRegularProjection,
      d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketSymbol_apply, hZero]
  · have hNorm : normSquared (covector mode) ≠ 0 :=
      ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hZero)
    simp [d9GaugeGhostFinitePacketRegularProjection,
      d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketSymbol_apply, hZero, smul_smul, hNorm]

/-- Applying the symbol after the generalized inverse is exactly the regular
projection. -/
theorem d9GaugeGhostFinitePacketSymbol_generalizedInverse
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketSymbol covector
        (d9GaugeGhostFinitePacketGeneralizedInverse covector packet) =
      d9GaugeGhostFinitePacketRegularProjection covector packet := rfl

/-- The generalized inverse followed by the symbol yields the same regular
projection. -/
theorem d9GaugeGhostFinitePacketGeneralizedInverse_symbol
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketGeneralizedInverse covector
        (d9GaugeGhostFinitePacketSymbol covector packet) =
      d9GaugeGhostFinitePacketRegularProjection covector packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketRegularProjection,
      d9GaugeGhostFinitePacketSymbol_apply, hZero]
  · have hNorm : normSquared (covector mode) ≠ 0 :=
      ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hZero)
    simp [d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketRegularProjection,
      d9GaugeGhostFinitePacketSymbol_apply, hZero, smul_smul, hNorm]

/-- Zero and regular components reconstruct every packet. -/
theorem d9GaugeGhostFinitePacket_zero_add_regular
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketZeroProjection covector packet +
        d9GaugeGhostFinitePacketRegularProjection covector packet = packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [hZero]
  · simp [hZero]

/-- The zero projection is idempotent. -/
theorem d9GaugeGhostFinitePacketZeroProjection_idempotent
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketZeroProjection covector
        (d9GaugeGhostFinitePacketZeroProjection covector packet) =
      d9GaugeGhostFinitePacketZeroProjection covector packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [hZero]
  · simp [hZero]

/-- The regular projection is idempotent. -/
theorem d9GaugeGhostFinitePacketRegularProjection_idempotent
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketRegularProjection covector
        (d9GaugeGhostFinitePacketRegularProjection covector packet) =
      d9GaugeGhostFinitePacketRegularProjection covector packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [hZero]
  · simp [hZero]

/-- The two packet projections annihilate one another. -/
theorem d9GaugeGhostFinitePacketZeroProjection_regularProjection
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketZeroProjection covector
        (d9GaugeGhostFinitePacketRegularProjection covector packet) = 0 := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [hZero]
  · simp [hZero]

/-- The reverse composite of the two projections also vanishes. -/
theorem d9GaugeGhostFinitePacketRegularProjection_zeroProjection
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketRegularProjection covector
        (d9GaugeGhostFinitePacketZeroProjection covector packet) = 0 := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [hZero]
  · simp [hZero]

/-- First von Neumann generalized-inverse identity: `A G A = A`. -/
theorem d9GaugeGhostFinitePacketSymbol_generalizedInverse_symbol
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketSymbol covector
        (d9GaugeGhostFinitePacketGeneralizedInverse covector
          (d9GaugeGhostFinitePacketSymbol covector packet)) =
      d9GaugeGhostFinitePacketSymbol covector packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketSymbol_apply, hZero]
  · have hNorm : normSquared (covector mode) ≠ 0 :=
      ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hZero)
    simp [d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketSymbol_apply, hZero, smul_smul, hNorm]

/-- Second von Neumann generalized-inverse identity: `G A G = G`. -/
theorem d9GaugeGhostFinitePacketGeneralizedInverse_symbol_generalizedInverse
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketGeneralizedInverse covector
        (d9GaugeGhostFinitePacketSymbol covector
          (d9GaugeGhostFinitePacketGeneralizedInverse covector packet)) =
      d9GaugeGhostFinitePacketGeneralizedInverse covector packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketSymbol_apply, hZero]
  · have hNorm : normSquared (covector mode) ≠ 0 :=
      ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hZero)
    simp [d9GaugeGhostFinitePacketGeneralizedInverse,
      d9GaugeGhostFinitePacketSymbol_apply, hZero, smul_smul, hNorm]

/-- The zero projection always lands in the exact kernel support. -/
theorem d9GaugeGhostFinitePacketZeroProjection_mem_zeroSupported
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketZeroProjection covector packet ∈
      d9GaugeGhostPacketZeroSupportedSubmodule covector := by
  simpa [d9GaugeGhostFinitePacketZeroProjection] using
    d9GaugeGhostPacketZeroExtension_mem_zeroSupported covector
      (d9GaugeGhostPacketZeroRestriction covector packet)

/-- The regular projection always lands in the exact range support. -/
theorem d9GaugeGhostFinitePacketRegularProjection_mem_zeroVanishing
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketRegularProjection covector packet ∈
      d9GaugeGhostPacketZeroVanishingSubmodule covector := by
  intro mode hZero
  simp [hZero]

/-- Zero-supported packets are fixed by the zero projection. -/
theorem d9GaugeGhostFinitePacketZeroProjection_eq_self_of_mem
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι)
    (hPacket : packet ∈ d9GaugeGhostPacketZeroSupportedSubmodule covector) :
    d9GaugeGhostFinitePacketZeroProjection covector packet = packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · simp [hZero]
  · have hValue := hPacket mode hZero
    simp [hZero, hValue]

/-- Zero-vanishing packets are fixed by the regular projection. -/
theorem d9GaugeGhostFinitePacketRegularProjection_eq_self_of_mem
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι)
    (hPacket : packet ∈ d9GaugeGhostPacketZeroVanishingSubmodule covector) :
    d9GaugeGhostFinitePacketRegularProjection covector packet = packet := by
  classical
  funext mode
  by_cases hZero : covector mode = zeroTangent
  · have hValue := hPacket mode hZero
    simp [hZero, hValue]
  · simp [hZero]

/-- The image of the zero projection is exactly the symbol kernel support. -/
theorem d9GaugeGhostFinitePacketZeroProjection_range
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.range (d9GaugeGhostFinitePacketZeroProjection covector) =
      d9GaugeGhostPacketZeroSupportedSubmodule covector := by
  ext packet
  constructor
  · rintro ⟨preimage, rfl⟩
    exact d9GaugeGhostFinitePacketZeroProjection_mem_zeroSupported covector preimage
  · intro hPacket
    exact ⟨packet,
      d9GaugeGhostFinitePacketZeroProjection_eq_self_of_mem
        covector packet hPacket⟩

/-- The image of the regular projection is exactly the symbol range support. -/
theorem d9GaugeGhostFinitePacketRegularProjection_range
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.range (d9GaugeGhostFinitePacketRegularProjection covector) =
      d9GaugeGhostPacketZeroVanishingSubmodule covector := by
  ext packet
  constructor
  · rintro ⟨preimage, rfl⟩
    exact d9GaugeGhostFinitePacketRegularProjection_mem_zeroVanishing
      covector preimage
  · intro hPacket
    exact ⟨packet,
      d9GaugeGhostFinitePacketRegularProjection_eq_self_of_mem
        covector packet hPacket⟩

/-- The zero projection kernel is exactly the regular/range support. -/
theorem d9GaugeGhostFinitePacketZeroProjection_ker
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostFinitePacketZeroProjection covector) =
      d9GaugeGhostPacketZeroVanishingSubmodule covector := by
  ext packet
  constructor
  · intro hKernel
    rw [LinearMap.mem_ker] at hKernel
    intro mode hZero
    have hApply := congrFun hKernel mode
    simpa [hZero] using hApply
  · intro hPacket
    rw [LinearMap.mem_ker]
    funext mode
    by_cases hZero : covector mode = zeroTangent
    · have hValue := hPacket mode hZero
      simp [hZero, hValue]
    · simp [hZero]

/-- The regular projection kernel is exactly the zero-symbol support. -/
theorem d9GaugeGhostFinitePacketRegularProjection_ker
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostFinitePacketRegularProjection covector) =
      d9GaugeGhostPacketZeroSupportedSubmodule covector := by
  ext packet
  constructor
  · intro hKernel
    rw [LinearMap.mem_ker] at hKernel
    intro mode hNonzero
    have hApply := congrFun hKernel mode
    simpa [hNonzero] using hApply
  · intro hPacket
    rw [LinearMap.mem_ker]
    funext mode
    by_cases hZero : covector mode = zeroTangent
    · simp [hZero]
    · have hValue := hPacket mode hZero
      simp [hZero, hValue]

/-- Projection-level support agrees with the actual operator kernel and range. -/
theorem d9GaugeGhostFinitePacketProjection_support_certificate
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.range (d9GaugeGhostFinitePacketZeroProjection covector) =
        LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) ∧
      LinearMap.ker (d9GaugeGhostFinitePacketZeroProjection covector) =
        LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) ∧
      LinearMap.range (d9GaugeGhostFinitePacketRegularProjection covector) =
        LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) ∧
      LinearMap.ker (d9GaugeGhostFinitePacketRegularProjection covector) =
        LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) := by
  rw [d9GaugeGhostFinitePacketZeroProjection_range,
    d9GaugeGhostFinitePacketZeroProjection_ker,
    d9GaugeGhostFinitePacketRegularProjection_range,
    d9GaugeGhostFinitePacketRegularProjection_ker,
    d9GaugeGhostFinitePacketSymbol_ker_eq_zeroSupported,
    d9GaugeGhostFinitePacketSymbol_range_eq_zeroVanishing]

/-- Reusable generalized-inverse and complementary-projection certificate. -/
theorem d9GaugeGhostFinitePacketGeneralizedInverse_certificate
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketSymbol covector
          (d9GaugeGhostFinitePacketGeneralizedInverse covector
            (d9GaugeGhostFinitePacketSymbol covector packet)) =
        d9GaugeGhostFinitePacketSymbol covector packet ∧
      d9GaugeGhostFinitePacketGeneralizedInverse covector
          (d9GaugeGhostFinitePacketSymbol covector
            (d9GaugeGhostFinitePacketGeneralizedInverse covector packet)) =
        d9GaugeGhostFinitePacketGeneralizedInverse covector packet ∧
      d9GaugeGhostFinitePacketZeroProjection covector packet +
          d9GaugeGhostFinitePacketRegularProjection covector packet = packet ∧
      d9GaugeGhostFinitePacketZeroProjection covector
          (d9GaugeGhostFinitePacketRegularProjection covector packet) = 0 ∧
      d9GaugeGhostFinitePacketRegularProjection covector
          (d9GaugeGhostFinitePacketZeroProjection covector packet) = 0 := by
  exact ⟨d9GaugeGhostFinitePacketSymbol_generalizedInverse_symbol
      covector packet,
    d9GaugeGhostFinitePacketGeneralizedInverse_symbol_generalizedInverse
      covector packet,
    d9GaugeGhostFinitePacket_zero_add_regular covector packet,
    d9GaugeGhostFinitePacketZeroProjection_regularProjection covector packet,
    d9GaugeGhostFinitePacketRegularProjection_zeroProjection covector packet⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketGeneralizedInverse4D
end JanusFormal
