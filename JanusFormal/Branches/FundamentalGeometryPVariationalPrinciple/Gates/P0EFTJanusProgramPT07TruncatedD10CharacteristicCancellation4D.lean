import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT07QuantizedPTFamiliesIndexConstraint4D

/-!
# T07 characteristic cancellation on the literal D10 cutoffs

The exact finite D10 packets retain the sphere-degeneracy label, the signed
circle mode and both normal-root choices.  Their concrete `truncatedPT`
involution reverses the root characteristic sign.  Consequently every finite
cutoff has zero total integral characteristic number and zero total continuous
families-index representative, with no mode or multiplicity discarded.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT07TruncatedD10CharacteristicCancellation4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Filter Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPT07QuantizedPTFamiliesIndexConstraint4D

/-- Reindexing a finite sum by an involution shows that every odd contribution
sums to zero over a characteristic-zero ring. -/
theorem fintype_sum_eq_zero_of_involutive_odd
    {Mode R : Type*} [Fintype Mode] [CommRing R] [NoZeroDivisors R] [CharZero R]
    (pt : Mode → Mode) (hPT : Function.Involutive pt)
    (contribution : Mode → R)
    (hOdd : ∀ mode, contribution (pt mode) = -contribution mode) :
    ∑ mode, contribution mode = 0 := by
  have hReindex :
      (∑ mode, contribution (pt mode)) = ∑ mode, contribution mode :=
    hPT.bijective.sum_comp contribution
  have hSelfNeg :
      (∑ mode, contribution mode) = -(∑ mode, contribution mode) := by
    calc
      _ = ∑ mode, contribution (pt mode) := hReindex.symm
      _ = ∑ mode, -contribution mode := by
        apply Finset.sum_congr rfl
        intro mode _
        exact hOdd mode
      _ = -(∑ mode, contribution mode) := by
        simpa only using
          (Finset.sum_neg_distrib (s := Finset.univ) contribution)
  exact CharZero.eq_neg_self_iff.mp hSelfNeg

/-- Integral sign of the two normal-root branches. -/
def rootCharacteristicSign : NormalRootChoice → ℤ
  | .positiveQuarter => 1
  | .negativeQuarter => -1

@[simp] theorem rootCharacteristicSign_opposite (root : NormalRootChoice) :
    rootCharacteristicSign (oppositeRoot root) =
      -rootCharacteristicSign root := by
  cases root <;> rfl

/-- Integral characteristic contribution of one literal truncated D10 mode. -/
def truncatedD10CharacteristicContribution
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    {spectral : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ}
    (base : Base) (first second : Tangent)
    (mode : TruncatedD10Mode spectral sphereCutoff circleCutoff) : ℤ :=
  rootCharacteristicSign mode.2.2.2 *
    quantized.characteristicNumber base first second

@[simp] theorem truncatedD10CharacteristicContribution_pt
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    {spectral : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ}
    (base : Base) (first second : Tangent)
    (mode : TruncatedD10Mode spectral sphereCutoff circleCutoff) :
    truncatedD10CharacteristicContribution quantized base first second
        (truncatedPT mode) =
      -truncatedD10CharacteristicContribution quantized base first second mode := by
  simp [truncatedD10CharacteristicContribution, truncatedPT]

/-- Continuous families-index contribution of one literal truncated mode. -/
def truncatedD10LocalFamiliesIndexContribution
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    {spectral : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ}
    (base : Base) (first second : Tangent)
    (mode : TruncatedD10Mode spectral sphereCutoff circleCutoff) : Complex :=
  (rootCharacteristicSign mode.2.2.2 : Complex) *
    quantized.geometry.localFamiliesIndexCurvature base first second

@[simp] theorem truncatedD10LocalFamiliesIndexContribution_pt
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    {spectral : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ}
    (base : Base) (first second : Tangent)
    (mode : TruncatedD10Mode spectral sphereCutoff circleCutoff) :
    truncatedD10LocalFamiliesIndexContribution quantized base first second
        (truncatedPT mode) =
      -truncatedD10LocalFamiliesIndexContribution quantized base first second mode := by
  simp [truncatedD10LocalFamiliesIndexContribution, truncatedPT]

/-- Modewise quantization: the continuous representative is the complex cast
of the integral characteristic contribution. -/
theorem truncatedD10_localFamiliesIndex_eq_characteristic_cast
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    {spectral : ProductThroatSpectralData}
    {sphereCutoff circleCutoff : ℕ}
    (base : Base) (first second : Tangent)
    (mode : TruncatedD10Mode spectral sphereCutoff circleCutoff) :
    truncatedD10LocalFamiliesIndexContribution quantized base first second mode =
      (truncatedD10CharacteristicContribution quantized base first second mode :
        Complex) := by
  rw [truncatedD10LocalFamiliesIndexContribution,
    truncatedD10CharacteristicContribution,
    quantized.localFamiliesIndex_eq_characteristic]
  norm_cast

/-- Exact cancellation of the integral characteristic class on every literal
D10 cutoff, including all sphere multiplicities. -/
theorem truncatedD10_characteristic_sum_eq_zero
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (sphereCutoff circleCutoff : ℕ)
    (base : Base) (first second : Tangent) :
    (∑ mode : TruncatedD10Mode spectral sphereCutoff circleCutoff,
      truncatedD10CharacteristicContribution quantized base first second mode) = 0 := by
  exact fintype_sum_eq_zero_of_involutive_odd truncatedPT
    truncatedPT_involutive
    (truncatedD10CharacteristicContribution quantized base first second)
    (truncatedD10CharacteristicContribution_pt quantized base first second)

/-- Exact cancellation of the continuous families-index representative on
the same literal D10 cutoff. -/
theorem truncatedD10_localFamiliesIndex_sum_eq_zero
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (sphereCutoff circleCutoff : ℕ)
    (base : Base) (first second : Tangent) :
    (∑ mode : TruncatedD10Mode spectral sphereCutoff circleCutoff,
      truncatedD10LocalFamiliesIndexContribution quantized base first second mode) = 0 := by
  exact fintype_sum_eq_zero_of_involutive_odd truncatedPT
    truncatedPT_involutive
    (truncatedD10LocalFamiliesIndexContribution quantized base first second)
    (truncatedD10LocalFamiliesIndexContribution_pt quantized base first second)

/-- Integral total indexed by the two cutoff parameters. -/
def truncatedD10CharacteristicCutoffTotal
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (base : Base) (first second : Tangent)
    (cutoff : ℕ × ℕ) : ℤ :=
  ∑ mode : TruncatedD10Mode spectral cutoff.1 cutoff.2,
    truncatedD10CharacteristicContribution quantized base first second mode

/-- Continuous total indexed by the same two cutoff parameters. -/
def truncatedD10LocalFamiliesIndexCutoffTotal
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (base : Base) (first second : Tangent)
    (cutoff : ℕ × ℕ) : Complex :=
  ∑ mode : TruncatedD10Mode spectral cutoff.1 cutoff.2,
    truncatedD10LocalFamiliesIndexContribution quantized base first second mode

@[simp] theorem truncatedD10CharacteristicCutoffTotal_eq_zero
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (base : Base) (first second : Tangent) (cutoff : ℕ × ℕ) :
    truncatedD10CharacteristicCutoffTotal quantized spectral base first second
      cutoff = 0 :=
  truncatedD10_characteristic_sum_eq_zero quantized spectral cutoff.1 cutoff.2
    base first second

@[simp] theorem truncatedD10LocalFamiliesIndexCutoffTotal_eq_zero
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (base : Base) (first second : Tangent) (cutoff : ℕ × ℕ) :
    truncatedD10LocalFamiliesIndexCutoffTotal quantized spectral base first second
      cutoff = 0 :=
  truncatedD10_localFamiliesIndex_sum_eq_zero quantized spectral cutoff.1 cutoff.2
    base first second

/-- The full directed net of integral cutoff anomalies converges to zero. -/
theorem truncatedD10_characteristic_cutoff_tendsto_zero
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (base : Base) (first second : Tangent) :
    Tendsto
      (truncatedD10CharacteristicCutoffTotal quantized spectral base first second)
      atTop (nhds 0) := by
  have hFunction :
      truncatedD10CharacteristicCutoffTotal quantized spectral base first second =
        fun _ : ℕ × ℕ => (0 : ℤ) := by
    funext cutoff
    exact truncatedD10CharacteristicCutoffTotal_eq_zero
      quantized spectral base first second cutoff
  rw [hFunction]
  exact tendsto_const_nhds

/-- The continuous local families-index cutoff net has the same zero limit. -/
theorem truncatedD10_localFamiliesIndex_cutoff_tendsto_zero
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData)
    (base : Base) (first second : Tangent) :
    Tendsto
      (truncatedD10LocalFamiliesIndexCutoffTotal quantized spectral base first second)
      atTop (nhds 0) := by
  have hFunction :
      truncatedD10LocalFamiliesIndexCutoffTotal quantized spectral base first second =
        fun _ : ℕ × ℕ => (0 : Complex) := by
    funext cutoff
    exact truncatedD10LocalFamiliesIndexCutoffTotal_eq_zero
      quantized spectral base first second cutoff
  rw [hFunction]
  exact tendsto_const_nhds

/-- All-cutoff T07 support certificate for the exact multiplicity-aware D10
field packet. -/
structure ProgramPT07TruncatedD10CharacteristicCancellationCertificate4D
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData) where
  pointwiseQuantization : ∀ sphereCutoff circleCutoff base first second mode,
    truncatedD10LocalFamiliesIndexContribution
        (spectral := spectral) (sphereCutoff := sphereCutoff)
        (circleCutoff := circleCutoff) quantized base first second mode =
      (truncatedD10CharacteristicContribution quantized base first second mode :
        Complex)
  integralCancellation : ∀ sphereCutoff circleCutoff base first second,
    (∑ mode : TruncatedD10Mode spectral sphereCutoff circleCutoff,
      truncatedD10CharacteristicContribution quantized base first second mode) = 0
  continuousCancellation : ∀ sphereCutoff circleCutoff base first second,
    (∑ mode : TruncatedD10Mode spectral sphereCutoff circleCutoff,
      truncatedD10LocalFamiliesIndexContribution quantized base first second mode) = 0
  integralCutoffConvergence : ∀ base first second,
    Tendsto
      (truncatedD10CharacteristicCutoffTotal quantized spectral base first second)
      atTop (nhds 0)
  continuousCutoffConvergence : ∀ base first second,
    Tendsto
      (truncatedD10LocalFamiliesIndexCutoffTotal quantized spectral base first second)
      atTop (nhds 0)

def programPT07TruncatedD10CharacteristicCancellationCertificate4D
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData) :
    ProgramPT07TruncatedD10CharacteristicCancellationCertificate4D
      quantized spectral where
  pointwiseQuantization :=
    fun _ _ base first second mode =>
      truncatedD10_localFamiliesIndex_eq_characteristic_cast
        quantized base first second mode
  integralCancellation :=
    truncatedD10_characteristic_sum_eq_zero quantized spectral
  continuousCancellation :=
    truncatedD10_localFamiliesIndex_sum_eq_zero quantized spectral
  integralCutoffConvergence :=
    truncatedD10_characteristic_cutoff_tendsto_zero quantized spectral
  continuousCutoffConvergence :=
    truncatedD10_localFamiliesIndex_cutoff_tendsto_zero quantized spectral

/-- Public exact-cutoff T07 checkpoint. -/
theorem t07_truncated_d10_characteristic_cancellation_gate
    {Base Tangent : Type*}
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent)
    (spectral : ProductThroatSpectralData) :
    Nonempty (ProgramPT07TruncatedD10CharacteristicCancellationCertificate4D
      quantized spectral) :=
  ⟨programPT07TruncatedD10CharacteristicCancellationCertificate4D
    quantized spectral⟩

end
end P0EFTJanusProgramPT07TruncatedD10CharacteristicCancellation4D
end JanusFormal
