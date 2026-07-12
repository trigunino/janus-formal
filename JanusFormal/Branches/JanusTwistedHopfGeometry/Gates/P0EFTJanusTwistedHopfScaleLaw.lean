import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedHopfScaleLaw

set_option autoImplicit false

/--
Scale data of the PT-twisted real Hopf quotient.

In logarithmic radial coordinate `u = log |x|`, the quotient generator is

`(omega,u) ↦ (rho omega, u - T)`

with contraction `lambda = exp(-T)`.  The orientation double cover has period
`2T`.
-/
structure TwistedHopfScaleData where
  uvLength : ℝ
  alphaSquaredLength : ℝ
  tunnelPeriod : ℝ
  contraction : ℝ
  uvLengthPositive : 0 < uvLength
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  tunnelPeriodPositive : 0 < tunnelPeriod
  contractionPositive : 0 < contraction
  contractionPeriodLaw :
    contraction * Real.exp tunnelPeriod = 1
  hierarchyLaw :
    2 * alphaSquaredLength = uvLength * Real.exp tunnelPeriod

/-- The quotient contraction is the UV-to-Janus length ratio. -/
theorem contraction_times_double_alpha_is_uv
    (s : TwistedHopfScaleData) :
    s.contraction * (2 * s.alphaSquaredLength) = s.uvLength := by
  rw [s.hierarchyLaw]
  calc
    s.contraction *
        (s.uvLength * Real.exp s.tunnelPeriod) =
      s.uvLength *
        (s.contraction * Real.exp s.tunnelPeriod) := by ring
    _ = s.uvLength := by rw [s.contractionPeriodLaw]; ring

/-- Cleared geometric hierarchy relation. -/
theorem two_alpha_times_contraction_eq_uv
    (s : TwistedHopfScaleData) :
    2 * s.alphaSquaredLength * s.contraction = s.uvLength := by
  nlinarith [contraction_times_double_alpha_is_uv s]

/-- The orientation cover doubles the logarithmic tunnel period. -/
def orientationCoverPeriod (s : TwistedHopfScaleData) : ℝ :=
  2 * s.tunnelPeriod

/-- The square monodromy contracts by `lambda^2`. -/
def orientationCoverContraction (s : TwistedHopfScaleData) : ℝ :=
  s.contraction ^ 2

@[simp] theorem orientation_cover_period_positive
    (s : TwistedHopfScaleData) :
    0 < orientationCoverPeriod s := by
  unfold orientationCoverPeriod
  nlinarith [s.tunnelPeriodPositive]

@[simp] theorem orientation_cover_contraction_positive
    (s : TwistedHopfScaleData) :
    0 < orientationCoverContraction s := by
  unfold orientationCoverContraction
  exact sq_pos_of_pos s.contractionPositive

/-- Same UV anchor and same monodromy period fix the same Janus length. -/
theorem same_uv_and_period_fix_alpha
    (s₁ s₂ : TwistedHopfScaleData)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hPeriod : s₁.tunnelPeriod = s₂.tunnelPeriod) :
    s₁.alphaSquaredLength = s₂.alphaSquaredLength := by
  have h₁ := s₁.hierarchyLaw
  have h₂ := s₂.hierarchyLaw
  rw [hUV, hPeriod] at h₁
  linarith

/-- Larger tunnel period produces a larger Janus length at fixed UV anchor. -/
theorem larger_period_gives_larger_alpha
    (s₁ s₂ : TwistedHopfScaleData)
    (hUV : s₁.uvLength = s₂.uvLength)
    (hPeriod : s₁.tunnelPeriod < s₂.tunnelPeriod) :
    s₁.alphaSquaredLength < s₂.alphaSquaredLength := by
  have hExp :
      Real.exp s₁.tunnelPeriod < Real.exp s₂.tunnelPeriod :=
    Real.exp_lt_exp.mpr hPeriod
  have hScaled :
      s₁.uvLength * Real.exp s₁.tunnelPeriod <
        s₁.uvLength * Real.exp s₂.tunnelPeriod :=
    mul_lt_mul_of_pos_left hExp s₁.uvLengthPositive
  have h₁ := s₁.hierarchyLaw
  have h₂ := s₂.hierarchyLaw
  rw [← hUV] at h₂
  linarith

/--
The geometric proposal identifies the RG hierarchy exponent with the compact
logarithmic tunnel period.  This is an identification theorem to be justified
by the quantum effective action, not merely by matching numbers.
-/
structure GeometryRGCompatibility where
  hopfScale : TwistedHopfScaleData
  worldvolumeRGExponent : ℝ
  exponentEqualsTunnelPeriod :
    worldvolumeRGExponent = hopfScale.tunnelPeriod
  uvAnchorIsSamePhysicalLength : Prop
  chargeNormalizationCompatible : Prop
  noObservedScaleImported : Prop

end P0EFTJanusTwistedHopfScaleLaw
end JanusFormal
