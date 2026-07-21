import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
set_option autoImplicit false
noncomputable section

open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- A packet of combined D9 gauge--ghost coordinates indexed by an arbitrary
mode type.  Finiteness is imposed only by the later Fredholm statements. -/
abbrev D9GaugeGhostFinitePacket (ι : Type*) :=
  ι → D9GaugeGhostLinearCoordinate

/-- The genuine block-diagonal D9 symbol on a packet.  Unlike the earlier
numerical sums, this is one linear endomorphism of the full packet space. -/
def d9GaugeGhostFinitePacketSymbol {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real] D9GaugeGhostFinitePacket ι where
  toFun packet mode :=
    d9GaugeGhostBlockLinearSymbol (covector mode) (packet mode)
  map_add' first second := by
    funext mode
    simp
  map_smul' scalar packet := by
    funext mode
    simp

@[simp] theorem d9GaugeGhostFinitePacketSymbol_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) (mode : ι) :
    d9GaugeGhostFinitePacketSymbol covector packet mode =
      normSquared (covector mode) • packet mode := rfl

/-- The subtype of modes at which the block symbol actually vanishes. -/
abbrev D9GaugeGhostPacketZeroMode {ι : Type*}
    (covector : ι → TangentVector3) :=
  {mode : ι // covector mode = zeroTangent}

/-- Coordinates carried only by the genuine zero-symbol modes. -/
abbrev D9GaugeGhostPacketZeroModeData {ι : Type*}
    (covector : ι → TangentVector3) :=
  D9GaugeGhostPacketZeroMode covector → D9GaugeGhostLinearCoordinate

/-- Restrict a full packet to the zero-symbol modes. -/
def d9GaugeGhostPacketZeroRestriction {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real]
      D9GaugeGhostPacketZeroModeData covector where
  toFun packet mode := packet mode.1
  map_add' first second := by
    funext mode
    rfl
  map_smul' scalar packet := by
    funext mode
    rfl

/-- Extend zero-mode data by zero away from the zero-symbol support. -/
def d9GaugeGhostPacketZeroExtension {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostPacketZeroModeData covector →ₗ[Real]
      D9GaugeGhostFinitePacket ι := by
  classical
  exact
    { toFun := fun packet mode =>
        if hZero : covector mode = zeroTangent then
          packet ⟨mode, hZero⟩
        else
          0
      map_add' := by
        intro first second
        funext mode
        by_cases hZero : covector mode = zeroTangent
        · simp [hZero]
        · simp [hZero]
      map_smul' := by
        intro scalar packet
        funext mode
        by_cases hZero : covector mode = zeroTangent
        · simp [hZero]
        · simp [hZero] }

@[simp] theorem d9GaugeGhostPacketZeroRestriction_extension
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostPacketZeroModeData covector) :
    d9GaugeGhostPacketZeroRestriction covector
        (d9GaugeGhostPacketZeroExtension covector packet) = packet := by
  funext mode
  simp [d9GaugeGhostPacketZeroRestriction,
    d9GaugeGhostPacketZeroExtension, mode.property]

/-- Packets supported only on zero-symbol modes.  This is the expected kernel
of the block-diagonal operator. -/
def d9GaugeGhostPacketZeroSupportedSubmodule {ι : Type*}
    (covector : ι → TangentVector3) :
    Submodule Real (D9GaugeGhostFinitePacket ι) where
  carrier := {packet | ∀ mode, covector mode ≠ zeroTangent → packet mode = 0}
  zero_mem' := by
    intro mode _
    rfl
  add_mem' := by
    intro first second hFirst hSecond mode hNonzero
    simp [hFirst mode hNonzero, hSecond mode hNonzero]
  smul_mem' := by
    intro scalar packet hPacket mode hNonzero
    simp [hPacket mode hNonzero]

@[simp] theorem mem_d9GaugeGhostPacketZeroSupportedSubmodule
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    packet ∈ d9GaugeGhostPacketZeroSupportedSubmodule covector ↔
      ∀ mode, covector mode ≠ zeroTangent → packet mode = 0 :=
  Iff.rfl

/-- Packets vanishing on zero-symbol modes.  This is the expected range of the
block-diagonal operator. -/
def d9GaugeGhostPacketZeroVanishingSubmodule {ι : Type*}
    (covector : ι → TangentVector3) :
    Submodule Real (D9GaugeGhostFinitePacket ι) where
  carrier := {packet | ∀ mode, covector mode = zeroTangent → packet mode = 0}
  zero_mem' := by
    intro mode _
    rfl
  add_mem' := by
    intro first second hFirst hSecond mode hZero
    simp [hFirst mode hZero, hSecond mode hZero]
  smul_mem' := by
    intro scalar packet hPacket mode hZero
    simp [hPacket mode hZero]

@[simp] theorem mem_d9GaugeGhostPacketZeroVanishingSubmodule
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostFinitePacket ι) :
    packet ∈ d9GaugeGhostPacketZeroVanishingSubmodule covector ↔
      ∀ mode, covector mode = zeroTangent → packet mode = 0 :=
  Iff.rfl

theorem d9GaugeGhostPacketZeroExtension_mem_zeroSupported
    {ι : Type*} (covector : ι → TangentVector3)
    (packet : D9GaugeGhostPacketZeroModeData covector) :
    d9GaugeGhostPacketZeroExtension covector packet ∈
      d9GaugeGhostPacketZeroSupportedSubmodule covector := by
  intro mode hNonzero
  simp [d9GaugeGhostPacketZeroExtension, hNonzero]

/-- Restriction has precisely the packets vanishing on zero modes as kernel. -/
theorem d9GaugeGhostPacketZeroRestriction_ker
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostPacketZeroRestriction covector) =
      d9GaugeGhostPacketZeroVanishingSubmodule covector := by
  ext packet
  constructor
  · intro hKernel mode hZero
    rw [LinearMap.mem_ker] at hKernel
    have hApply := congrFun hKernel ⟨mode, hZero⟩
    exact hApply
  · intro hPacket
    rw [LinearMap.mem_ker]
    funext mode
    exact hPacket mode.1 mode.property

/-- Exact kernel classification of the genuine finite-packet operator. -/
theorem d9GaugeGhostFinitePacketSymbol_ker_eq_zeroSupported
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) =
      d9GaugeGhostPacketZeroSupportedSubmodule covector := by
  ext packet
  constructor
  · intro hKernel mode hNonzero
    rw [LinearMap.mem_ker] at hKernel
    have hApply : normSquared (covector mode) • packet mode = 0 := by
      simpa using congrFun hKernel mode
    have hNorm : normSquared (covector mode) ≠ 0 :=
      ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hNonzero)
    have hScaled := congrArg
      (fun value : D9GaugeGhostLinearCoordinate =>
        (normSquared (covector mode))⁻¹ • value) hApply
    simpa [smul_smul, hNorm] using hScaled
  · intro hSupport
    rw [LinearMap.mem_ker]
    funext mode
    by_cases hZero : covector mode = zeroTangent
    · simp [d9GaugeGhostFinitePacketSymbol_apply, hZero,
        normSquared, tangentDot, zeroTangent]
    · have hPacket := hSupport mode hZero
      simp [d9GaugeGhostFinitePacketSymbol, hPacket]

/-- Exact range classification: nonzero blocks are invertible and zero blocks
force the output to vanish at precisely the zero-symbol modes. -/
theorem d9GaugeGhostFinitePacketSymbol_range_eq_zeroVanishing
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) =
      d9GaugeGhostPacketZeroVanishingSubmodule covector := by
  ext packet
  constructor
  · rintro ⟨preimage, rfl⟩
    intro mode hZero
    simp [d9GaugeGhostFinitePacketSymbol_apply, hZero,
      normSquared, tangentDot, zeroTangent]
  · intro hPacket
    classical
    let preimage : D9GaugeGhostFinitePacket ι := fun mode =>
      if hZero : covector mode = zeroTangent then
        0
      else
        (normSquared (covector mode))⁻¹ • packet mode
    refine ⟨preimage, ?_⟩
    funext mode
    by_cases hZero : covector mode = zeroTangent
    · have hValue := hPacket mode hZero
      simp [preimage, hZero, hValue, d9GaugeGhostFinitePacketSymbol,
        d9GaugeGhostBlockLinearSymbol, normSquared, tangentDot, zeroTangent]
    · have hNorm : normSquared (covector mode) ≠ 0 :=
        ne_of_gt (norm_squared_positive_of_nonzero (covector mode) hZero)
      simp [preimage, hZero, d9GaugeGhostFinitePacketSymbol,
        d9GaugeGhostBlockLinearSymbol, smul_smul, hNorm]

/-- The operator kernel is canonically the packet of data on its zero-symbol
support. -/
def d9GaugeGhostFinitePacketKernelEquivZeroModeData
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) ≃ₗ[Real]
      D9GaugeGhostPacketZeroModeData covector where
  toFun kernel mode := kernel.1 mode.1
  invFun packet :=
    ⟨d9GaugeGhostPacketZeroExtension covector packet, by
      rw [d9GaugeGhostFinitePacketSymbol_ker_eq_zeroSupported]
      exact d9GaugeGhostPacketZeroExtension_mem_zeroSupported covector packet⟩
  left_inv kernel := by
    apply Subtype.ext
    funext mode
    by_cases hZero : covector mode = zeroTangent
    · simp [d9GaugeGhostPacketZeroExtension, hZero]
    · have hSupport : kernel.1 ∈
          d9GaugeGhostPacketZeroSupportedSubmodule covector := by
        rw [← d9GaugeGhostFinitePacketSymbol_ker_eq_zeroSupported]
        exact kernel.2
      have hValue := hSupport mode hZero
      simp [d9GaugeGhostPacketZeroExtension, hZero, hValue]
  right_inv packet := by
    funext mode
    simp [d9GaugeGhostPacketZeroExtension, mode.property]
  map_add' first second := by
    funext mode
    rfl
  map_smul' scalar packet := by
    funext mode
    rfl

/-- Pointwise reciprocal used as the inverse of the packet symbol when no mode
lies at the zero covector. -/
def d9GaugeGhostFinitePacketSymbolInverse {ι : Type*}
    (covector : ι → TangentVector3) :
    D9GaugeGhostFinitePacket ι →ₗ[Real] D9GaugeGhostFinitePacket ι where
  toFun packet mode := (normSquared (covector mode))⁻¹ • packet mode
  map_add' first second := by
    funext mode
    simp [smul_add]
  map_smul' scalar packet := by
    funext mode
    simp [smul_smul, mul_comm]

theorem d9GaugeGhostFinitePacketSymbol_inverse_apply
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketSymbol covector
        (d9GaugeGhostFinitePacketSymbolInverse covector packet) = packet := by
  funext mode
  have hNorm : normSquared (covector mode) ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      (covector mode) (hNonzero mode))
  simp [d9GaugeGhostFinitePacketSymbol,
    d9GaugeGhostFinitePacketSymbolInverse,
    d9GaugeGhostBlockLinearSymbol, smul_smul, hNorm]

theorem d9GaugeGhostFinitePacketSymbol_apply_inverse
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent)
    (packet : D9GaugeGhostFinitePacket ι) :
    d9GaugeGhostFinitePacketSymbolInverse covector
        (d9GaugeGhostFinitePacketSymbol covector packet) = packet := by
  funext mode
  have hNorm : normSquared (covector mode) ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      (covector mode) (hNonzero mode))
  simp [d9GaugeGhostFinitePacketSymbol,
    d9GaugeGhostFinitePacketSymbolInverse,
    d9GaugeGhostBlockLinearSymbol, smul_smul, hNorm]

theorem d9GaugeGhostFinitePacketSymbol_bijective_of_nonzero
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent) :
    Function.Bijective (d9GaugeGhostFinitePacketSymbol covector) := by
  constructor
  · intro first second hEqual
    calc
      first = d9GaugeGhostFinitePacketSymbolInverse covector
          (d9GaugeGhostFinitePacketSymbol covector first) :=
        (d9GaugeGhostFinitePacketSymbol_apply_inverse
          covector hNonzero first).symm
      _ = d9GaugeGhostFinitePacketSymbolInverse covector
          (d9GaugeGhostFinitePacketSymbol covector second) := by
        rw [hEqual]
      _ = second :=
        d9GaugeGhostFinitePacketSymbol_apply_inverse
          covector hNonzero second
  · intro packet
    exact ⟨d9GaugeGhostFinitePacketSymbolInverse covector packet,
      d9GaugeGhostFinitePacketSymbol_inverse_apply
        covector hNonzero packet⟩

/-- If every selected covector is nonzero, the finite packet operator is a
linear automorphism. -/
def d9GaugeGhostFinitePacketSymbolEquivOfNonzero
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent) :
    D9GaugeGhostFinitePacket ι ≃ₗ[Real] D9GaugeGhostFinitePacket ι :=
  LinearEquiv.ofBijective (d9GaugeGhostFinitePacketSymbol covector)
    (d9GaugeGhostFinitePacketSymbol_bijective_of_nonzero covector hNonzero)

theorem d9GaugeGhostFinitePacketSymbol_ker_eq_bot_of_nonzero
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent) :
    LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (d9GaugeGhostFinitePacketSymbol_bijective_of_nonzero covector hNonzero).1

theorem d9GaugeGhostFinitePacketSymbol_range_eq_top_of_nonzero
    {ι : Type*} (covector : ι → TangentVector3)
    (hNonzero : ∀ mode, covector mode ≠ zeroTangent) :
    LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (d9GaugeGhostFinitePacketSymbol_bijective_of_nonzero covector hNonzero).2

/-- Reusable operator-level certificate.  It upgrades the previous sum of
pointwise dimensions to one actual block-diagonal linear endomorphism. -/
theorem d9GaugeGhostFinitePacketOperator_certificate
    {ι : Type*} (covector : ι → TangentVector3) :
    LinearMap.ker (d9GaugeGhostFinitePacketSymbol covector) =
        d9GaugeGhostPacketZeroSupportedSubmodule covector ∧
      LinearMap.range (d9GaugeGhostFinitePacketSymbol covector) =
        d9GaugeGhostPacketZeroVanishingSubmodule covector ∧
      Function.RightInverse
        (d9GaugeGhostPacketZeroExtension covector)
        (d9GaugeGhostPacketZeroRestriction covector) := by
  exact ⟨d9GaugeGhostFinitePacketSymbol_ker_eq_zeroSupported covector,
    d9GaugeGhostFinitePacketSymbol_range_eq_zeroVanishing covector,
    d9GaugeGhostPacketZeroRestriction_extension covector⟩

end
end P0EFTJanusGaugeGhostBlockD9FinitePacketOperator4D
end JanusFormal
