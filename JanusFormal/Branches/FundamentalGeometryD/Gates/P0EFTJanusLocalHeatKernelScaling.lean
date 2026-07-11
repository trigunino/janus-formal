import Mathlib

namespace JanusFormal
namespace P0EFTJanusLocalHeatKernelScaling

set_option autoImplicit false

/--
Dimensionless scaling skeleton for local integrated invariants on
`S2_L x S1_(L*T)`.

The exact numerical coefficients depend on the Laplace-type operator and field
content.  The powers of `L` and the common linear factor `T` follow from the
product volume and the dimensions of the local invariant.
-/
structure ProductThroatLocalScales where
  geometricLength : ℝ
  circleModulus : ℝ
  geometricLengthPositive : 0 < geometricLength
  circleModulusPositive : 0 < circleModulus

/-- Volume scaling, up to the fixed angular factor. -/
def volumeScale (s : ProductThroatLocalScales) : ℝ :=
  s.geometricLength ^ 3 * s.circleModulus

/-- Integrated scalar-curvature scaling. -/
def curvatureScale (s : ProductThroatLocalScales) : ℝ :=
  s.geometricLength * s.circleModulus

/-- Integrated curvature-squared or monopole-field-squared scaling. -/
def quadraticInvariantScale (s : ProductThroatLocalScales) : ℝ :=
  s.geometricLength⁻¹ * s.circleModulus

/-- Each of the three leading local scales is linear in the circle modulus. -/
theorem leading_local_scales_factor_circle_modulus
    (s : ProductThroatLocalScales) :
    volumeScale s = s.circleModulus * s.geometricLength ^ 3 /\
    curvatureScale s = s.circleModulus * s.geometricLength /\
    quadraticInvariantScale s =
      s.circleModulus * s.geometricLength⁻¹ := by
  constructor
  · unfold volumeScale
    ring
  · constructor
    · unfold curvatureScale
      ring
    · unfold quadraticInvariantScale
      ring

/-- Generic finite truncation of the local heat-kernel/spectral action. -/
def localHeatKernelDensity
    (cosmological curvature quadratic : ℝ)
    (geometricLength : ℝ) : ℝ :=
  cosmological * geometricLength ^ 3 +
    curvature * geometricLength +
    quadratic * geometricLength⁻¹

/-- The integrated local action is the circle modulus times a local density. -/
def localHeatKernelAction
    (cosmological curvature quadratic : ℝ)
    (geometricLength circleModulus : ℝ) : ℝ :=
  circleModulus *
    localHeatKernelDensity cosmological curvature quadratic geometricLength

/-- Exact finite-difference law: all local terms are affine in the circle modulus. -/
theorem local_action_difference
    (cosmological curvature quadratic geometricLength
      firstModulus secondModulus : ℝ) :
    localHeatKernelAction cosmological curvature quadratic
        geometricLength secondModulus -
      localHeatKernelAction cosmological curvature quadratic
        geometricLength firstModulus =
      (secondModulus - firstModulus) *
        localHeatKernelDensity cosmological curvature quadratic
          geometricLength := by
  unfold localHeatKernelAction
  ring

/-- Midpoint identity for the local action. -/
theorem local_action_midpoint_identity
    (cosmological curvature quadratic geometricLength
      center displacement : ℝ) :
    2 * localHeatKernelAction cosmological curvature quadratic
        geometricLength center =
      localHeatKernelAction cosmological curvature quadratic
          geometricLength (center - displacement) +
        localHeatKernelAction cosmological curvature quadratic
          geometricLength (center + displacement) := by
  unfold localHeatKernelAction
  ring

/-- A purely local product-throat action cannot have a strict symmetric interior minimum. -/
theorem local_heat_kernel_terms_do_not_strictly_stabilize_circle
    (cosmological curvature quadratic geometricLength
      center displacement : ℝ)
    (hDisplacement : 0 < displacement) :
    Not (
      localHeatKernelAction cosmological curvature quadratic
          geometricLength center <
        localHeatKernelAction cosmological curvature quadratic
          geometricLength (center - displacement) /\
      localHeatKernelAction cosmological curvature quadratic
          geometricLength center <
        localHeatKernelAction cosmological curvature quadratic
          geometricLength (center + displacement)) := by
  intro hStrict
  have hMidpoint := local_action_midpoint_identity
    cosmological curvature quadratic geometricLength center displacement
  linarith

/-- General version for any finite list of local integrated densities. -/
def finiteLocalAction (densities : List ℝ) (circleModulus : ℝ) : ℝ :=
  circleModulus * densities.sum

/-- Any finite local truncation obeys the same midpoint identity. -/
theorem finite_local_action_midpoint_identity
    (densities : List ℝ)
    (center displacement : ℝ) :
    2 * finiteLocalAction densities center =
      finiteLocalAction densities (center - displacement) +
        finiteLocalAction densities (center + displacement) := by
  unfold finiteLocalAction
  ring

/-- No finite sum of local heat-kernel coefficients can by itself produce a strict interior circle minimum. -/
theorem finite_local_heat_kernel_action_no_strict_minimum
    (densities : List ℝ)
    (center displacement : ℝ)
    (hDisplacement : 0 < displacement) :
    Not (
      finiteLocalAction densities center <
        finiteLocalAction densities (center - displacement) /\
      finiteLocalAction densities center <
        finiteLocalAction densities (center + displacement)) := by
  intro hStrict
  have hMidpoint := finite_local_action_midpoint_identity
    densities center displacement
  linarith

/--
The local coefficients determine counterterms and UV divergences, but circle
stabilization requires a nonlocal winding/holonomy term, an interaction, a
boundary contribution, or competition with another sector.
-/
structure LocalHeatKernelClosureStatus where
  laplaceTypeOperatorConstructed : Prop
  localCoefficientsComputed : Prop
  productScalingProved : Prop
  finiteCountertermsFixed : Prop
  nonlocalEffectiveActionComputed : Prop
  stableCircleMinimumDerived : Prop


def localHeatKernelClosure
    (s : LocalHeatKernelClosureStatus) : Prop :=
  s.laplaceTypeOperatorConstructed /\
  s.localCoefficientsComputed /\
  s.productScalingProved /\
  s.finiteCountertermsFixed /\
  s.nonlocalEffectiveActionComputed /\
  s.stableCircleMinimumDerived

end P0EFTJanusLocalHeatKernelScaling
end JanusFormal
