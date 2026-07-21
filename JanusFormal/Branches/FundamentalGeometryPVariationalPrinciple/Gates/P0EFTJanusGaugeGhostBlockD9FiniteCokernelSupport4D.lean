import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9FiniteZeroModePacket4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9PointwiseFinrank4D
open P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

/-- Numerical size of the combined D9 cokernel at the zero covector. -/
def d9GaugeGhostZeroCokernelFinrank : Nat :=
  Module.finrank Real (D9GaugeGhostBlockCokernel zeroTangent)

/-- Total combined-cokernel dimension of a finite packet of pointwise D9
symbols. -/
def d9GaugeGhostFiniteCokernelFinrank {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) : Nat :=
  modes.sum fun mode =>
    Module.finrank Real (D9GaugeGhostBlockCokernel (covector mode))

/-- The same finite total computed after separating gauge and ghost
cokernels. -/
def d9SeparatedFiniteCokernelFinrank {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) : Nat :=
  modes.sum fun mode =>
    Module.finrank Real (D9GaugeCokernel (covector mode)) +
      Module.finrank Real (D9GhostCokernel (covector mode))

/-- Modes whose principal covector is zero. -/
def d9ZeroCovectorModes {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) : Finset ι := by
  classical
  exact modes.filter fun mode => covector mode = zeroTangent

/-- Number of genuine zero-covector modes in a finite packet. -/
def d9ZeroCovectorMultiplicity {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) : Nat :=
  (d9ZeroCovectorModes modes covector).card

/-- Gauge--ghost cokernel additivity commutes with every finite mode sum. -/
theorem d9GaugeGhostFiniteCokernelFinrank_additive {ι : Type*}
    (modes : Finset ι) (covector : ι → TangentVector3) :
    d9GaugeGhostFiniteCokernelFinrank modes covector =
      d9SeparatedFiniteCokernelFinrank modes covector := by
  classical
  unfold d9GaugeGhostFiniteCokernelFinrank d9SeparatedFiniteCokernelFinrank
  apply Finset.sum_congr rfl
  intro mode _
  exact combinedCokernel_finrank_additive (covector mode)

private theorem d9ZeroCovectorModes_insert_of_zero
    {ι : Type*} [DecidableEq ι] (mode : ι) (modes : Finset ι)
    (covector : ι → TangentVector3)
    (hZero : covector mode = zeroTangent) :
    d9ZeroCovectorModes (insert mode modes) covector =
      insert mode (d9ZeroCovectorModes modes covector) := by
  ext x
  simp [d9ZeroCovectorModes, hZero]

private theorem d9ZeroCovectorModes_insert_of_nonzero
    {ι : Type*} [DecidableEq ι] (mode : ι) (modes : Finset ι)
    (covector : ι → TangentVector3)
    (hZero : covector mode ≠ zeroTangent) :
    d9ZeroCovectorModes (insert mode modes) covector =
      d9ZeroCovectorModes modes covector := by
  ext x
  simp [d9ZeroCovectorModes, hZero]

private theorem d9ZeroCovectorMultiplicity_insert_of_zero
    {ι : Type*} [DecidableEq ι] (mode : ι) (modes : Finset ι)
    (covector : ι → TangentVector3)
    (hMode : mode ∉ modes)
    (hZero : covector mode = zeroTangent) :
    d9ZeroCovectorMultiplicity (insert mode modes) covector =
      d9ZeroCovectorMultiplicity modes covector + 1 := by
  rw [d9ZeroCovectorMultiplicity, d9ZeroCovectorMultiplicity,
    d9ZeroCovectorModes_insert_of_zero mode modes covector hZero]
  have hNotMem : mode ∉ d9ZeroCovectorModes modes covector := by
    intro hMembership
    exact hMode (Finset.mem_of_mem_filter hMembership)
  simp [hNotMem, Nat.add_comm]

private theorem d9ZeroCovectorMultiplicity_insert_of_nonzero
    {ι : Type*} [DecidableEq ι] (mode : ι) (modes : Finset ι)
    (covector : ι → TangentVector3)
    (hZero : covector mode ≠ zeroTangent) :
    d9ZeroCovectorMultiplicity (insert mode modes) covector =
      d9ZeroCovectorMultiplicity modes covector := by
  rw [d9ZeroCovectorMultiplicity, d9ZeroCovectorMultiplicity,
    d9ZeroCovectorModes_insert_of_nonzero mode modes covector hZero]

/-- Exact finite-support classification: every nonzero-covector cokernel
vanishes, hence the total cokernel dimension is supported precisely on the
zero-covector modes. -/
theorem d9GaugeGhostFiniteCokernelFinrank_eq_zeroMultiplicity_mul
    {ι : Type*} (modes : Finset ι) (covector : ι → TangentVector3) :
    d9GaugeGhostFiniteCokernelFinrank modes covector =
      d9ZeroCovectorMultiplicity modes covector *
        d9GaugeGhostZeroCokernelFinrank := by
  classical
  induction modes using Finset.induction_on with
  | empty =>
      simp [d9GaugeGhostFiniteCokernelFinrank,
        d9ZeroCovectorMultiplicity, d9ZeroCovectorModes]
  | @insert mode modes hMode ih =>
      by_cases hZero : covector mode = zeroTangent
      · calc
          d9GaugeGhostFiniteCokernelFinrank (insert mode modes) covector =
              Module.finrank Real
                  (D9GaugeGhostBlockCokernel (covector mode)) +
                d9GaugeGhostFiniteCokernelFinrank modes covector := by
            simp [d9GaugeGhostFiniteCokernelFinrank, hMode]
          _ = d9GaugeGhostZeroCokernelFinrank +
                d9GaugeGhostFiniteCokernelFinrank modes covector := by
            rw [hZero]
            rfl
          _ = d9GaugeGhostZeroCokernelFinrank +
                d9ZeroCovectorMultiplicity modes covector *
                  d9GaugeGhostZeroCokernelFinrank := by
            rw [ih]
          _ = (d9ZeroCovectorMultiplicity modes covector + 1) *
                d9GaugeGhostZeroCokernelFinrank := by
            simp [Nat.add_mul, Nat.add_comm]
          _ = d9ZeroCovectorMultiplicity (insert mode modes) covector *
                d9GaugeGhostZeroCokernelFinrank := by
            rw [d9ZeroCovectorMultiplicity_insert_of_zero
              mode modes covector hMode hZero]
      · have hNonzeroFinrank :=
          d9GaugeGhostBlock_nonzero_cokernel_finrank (covector mode) hZero
        calc
          d9GaugeGhostFiniteCokernelFinrank (insert mode modes) covector =
              Module.finrank Real
                  (D9GaugeGhostBlockCokernel (covector mode)) +
                d9GaugeGhostFiniteCokernelFinrank modes covector := by
            simp [d9GaugeGhostFiniteCokernelFinrank, hMode]
          _ = d9GaugeGhostFiniteCokernelFinrank modes covector := by
            rw [hNonzeroFinrank, zero_add]
          _ = d9ZeroCovectorMultiplicity modes covector *
                d9GaugeGhostZeroCokernelFinrank := ih
          _ = d9ZeroCovectorMultiplicity (insert mode modes) covector *
                d9GaugeGhostZeroCokernelFinrank := by
            rw [d9ZeroCovectorMultiplicity_insert_of_nonzero
              mode modes covector hZero]

/-- The separated gauge-plus-ghost computation has the same exact support. -/
theorem d9SeparatedFiniteCokernelFinrank_eq_zeroMultiplicity_mul
    {ι : Type*} (modes : Finset ι) (covector : ι → TangentVector3) :
    d9SeparatedFiniteCokernelFinrank modes covector =
      d9ZeroCovectorMultiplicity modes covector *
        d9GaugeGhostZeroCokernelFinrank := by
  calc
    d9SeparatedFiniteCokernelFinrank modes covector =
        d9GaugeGhostFiniteCokernelFinrank modes covector :=
      (d9GaugeGhostFiniteCokernelFinrank_additive modes covector).symm
    _ = d9ZeroCovectorMultiplicity modes covector *
        d9GaugeGhostZeroCokernelFinrank :=
      d9GaugeGhostFiniteCokernelFinrank_eq_zeroMultiplicity_mul modes covector

/-- A packet containing only nonzero covectors has no pointwise D9 cokernel. -/
theorem d9GaugeGhostFiniteCokernelFinrank_eq_zero_of_nonzero
    {ι : Type*} (modes : Finset ι) (covector : ι → TangentVector3)
    (hNonzero : ∀ mode ∈ modes, covector mode ≠ zeroTangent) :
    d9GaugeGhostFiniteCokernelFinrank modes covector = 0 := by
  classical
  unfold d9GaugeGhostFiniteCokernelFinrank
  apply Finset.sum_eq_zero
  intro mode hMode
  exact d9GaugeGhostBlock_nonzero_cokernel_finrank
    (covector mode) (hNonzero mode hMode)

/-- When every selected mode is a zero mode, the zero-covector multiplicity
is exactly the cardinality of the selected finite packet. -/
theorem d9ZeroCovectorMultiplicity_eq_card_of_zero
    {ι : Type*} (modes : Finset ι) (covector : ι → TangentVector3)
    (hZero : ∀ mode ∈ modes, covector mode = zeroTangent) :
    d9ZeroCovectorMultiplicity modes covector = modes.card := by
  classical
  have hSupport : d9ZeroCovectorModes modes covector = modes := by
    ext mode
    simp only [d9ZeroCovectorModes, Finset.mem_filter]
    constructor
    · intro hMode
      exact hMode.1
    · intro hMode
      exact ⟨hMode, hZero mode hMode⟩
  simp [d9ZeroCovectorMultiplicity, hSupport]

/-- Constant zero-covector packets have dimension equal to multiplicity times
the one-block zero-mode dimension. -/
theorem d9GaugeGhostFiniteCokernelFinrank_eq_card_mul_of_zero
    {ι : Type*} (modes : Finset ι) (covector : ι → TangentVector3)
    (hZero : ∀ mode ∈ modes, covector mode = zeroTangent) :
    d9GaugeGhostFiniteCokernelFinrank modes covector =
      modes.card * d9GaugeGhostZeroCokernelFinrank := by
  calc
    d9GaugeGhostFiniteCokernelFinrank modes covector =
        d9ZeroCovectorMultiplicity modes covector *
          d9GaugeGhostZeroCokernelFinrank :=
      d9GaugeGhostFiniteCokernelFinrank_eq_zeroMultiplicity_mul modes covector
    _ = modes.card * d9GaugeGhostZeroCokernelFinrank := by
      rw [d9ZeroCovectorMultiplicity_eq_card_of_zero modes covector hZero]

/-- Reusable finite-cokernel support certificate for mixed zero and nonzero
D9 symbol packets. -/
theorem d9GaugeGhostFiniteCokernelSupport_certificate
    {ι : Type*} (modes : Finset ι) (covector : ι → TangentVector3) :
    d9GaugeGhostFiniteCokernelFinrank modes covector =
        d9SeparatedFiniteCokernelFinrank modes covector ∧
      d9GaugeGhostFiniteCokernelFinrank modes covector =
        d9ZeroCovectorMultiplicity modes covector *
          d9GaugeGhostZeroCokernelFinrank ∧
      d9SeparatedFiniteCokernelFinrank modes covector =
        d9ZeroCovectorMultiplicity modes covector *
          d9GaugeGhostZeroCokernelFinrank := by
  exact ⟨d9GaugeGhostFiniteCokernelFinrank_additive modes covector,
    d9GaugeGhostFiniteCokernelFinrank_eq_zeroMultiplicity_mul modes covector,
    d9SeparatedFiniteCokernelFinrank_eq_zeroMultiplicity_mul modes covector⟩

end
end P0EFTJanusGaugeGhostBlockD9FiniteCokernelSupport4D
end JanusFormal
