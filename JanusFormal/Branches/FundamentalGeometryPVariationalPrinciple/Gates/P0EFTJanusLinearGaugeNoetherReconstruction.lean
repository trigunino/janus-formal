import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction

namespace JanusFormal
namespace P0EFTJanusLinearGaugeNoetherReconstruction

set_option autoImplicit false

open P0EFTJanusConvexHelmholtzReconstruction

/-- Translation by the image of a linear gauge parameter.  This is only an
additive action on an entire real normed vector space. -/
def linearGaugeTranslate
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (x : Configuration) (parameter : Gauge) : Configuration :=
  x + generator parameter

@[simp]
theorem linearGaugeTranslate_zero
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration) (x : Configuration) :
    linearGaugeTranslate generator x 0 = x := by
  simp [linearGaugeTranslate]

theorem linearGaugeTranslate_add
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (x : Configuration) (first second : Gauge) :
    linearGaugeTranslate generator
        (linearGaugeTranslate generator x first) second =
      linearGaugeTranslate generator x (first + second) := by
  simp [linearGaugeTranslate, add_assoc]

/-- Invariance of an action under every additive linear gauge translation. -/
def TranslationGaugeInvariant
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (action : Configuration → ℝ) : Prop :=
  ∀ x parameter,
    action (linearGaugeTranslate generator x parameter) = action x

/-- The Euler one-form annihilates every linear gauge direction.  This is the
linear horizontal/Noether identity used by this conditional model. -/
def EulerHorizontal
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (euler : EulerOneForm Configuration) : Prop :=
  ∀ x parameter, euler x (generator parameter) = 0

/-- If an action has a horizontal Euler one-form as its actual Fréchet
derivative everywhere, then it is invariant along every affine linear gauge
orbit. -/
theorem translation_gauge_invariant_of_hasFDerivAt_horizontal
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (euler : EulerOneForm Configuration)
    (action : Configuration → ℝ)
    (hGradient : ∀ x, HasFDerivAt action (euler x) x)
    (hHorizontal : EulerHorizontal generator euler) :
    TranslationGaugeInvariant generator action := by
  intro x parameter
  let endpoint := linearGaugeTranslate generator x parameter
  let curve : ℝ → ℝ :=
    fun t => action (AffineMap.lineMap x endpoint t)
  have hCurveDeriv (t : ℝ) : HasDerivAt curve 0 t := by
    have hLine :
        HasDerivAt (AffineMap.lineMap x endpoint) (endpoint - x) t :=
      AffineMap.hasDerivAt_lineMap
    have hComp :=
      (hGradient (AffineMap.lineMap x endpoint t)).comp_hasDerivAt t hLine
    have hDirection : endpoint - x = generator parameter := by
      simp [endpoint, linearGaugeTranslate]
    have hZero :
        euler (AffineMap.lineMap x endpoint t) (endpoint - x) = 0 := by
      rw [hDirection]
      exact hHorizontal _ parameter
    simpa [curve, Function.comp_def] using hComp.congr_deriv hZero
  have hCurveDifferentiable : Differentiable ℝ curve :=
    fun t => (hCurveDeriv t).differentiableAt
  have hCurveDerivZero (t : ℝ) : deriv curve t = 0 :=
    (hCurveDeriv t).deriv
  have hConstant :=
    is_const_of_deriv_eq_zero hCurveDifferentiable hCurveDerivZero 1 0
  simpa [curve, endpoint, linearGaugeTranslate] using hConstant

/-- Under whole-space differentiability, Helmholtz symmetry and gauge
horizontality, the radial primitive is gauge invariant. -/
theorem radial_action_translation_gauge_invariant
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (euler : EulerOneForm Configuration)
    (hDifferentiable : Differentiable ℝ euler)
    (hHelmholtz : ∀ x, HelmholtzJacobianAt euler x)
    (hHorizontal : EulerHorizontal generator euler)
    (base : Configuration) :
    TranslationGaugeInvariant generator (radialAction base euler) := by
  exact translation_gauge_invariant_of_hasFDerivAt_horizontal
    generator euler (radialAction base euler)
    (radial_action_hasFDerivAt euler hDifferentiable hHelmholtz base)
    hHorizontal

/-- Conditional normalized reconstruction on the whole configuration space:
the supplied differentiable Helmholtz one-form has a primitive vanishing at
the chosen base and invariant under the supplied additive linear gauge
translations.  This does not construct a Janus gauge group or PDE action. -/
theorem normalized_gauge_invariant_radial_reconstruction
    {Configuration Gauge : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    [NormedAddCommGroup Gauge] [NormedSpace ℝ Gauge]
    (generator : Gauge →L[ℝ] Configuration)
    (euler : EulerOneForm Configuration)
    (hDifferentiable : Differentiable ℝ euler)
    (hHelmholtz : ∀ x, HelmholtzJacobianAt euler x)
    (hHorizontal : EulerHorizontal generator euler)
    (base : Configuration) :
    ∃ action : Configuration → ℝ,
      (∀ x, HasFDerivAt action (euler x) x) ∧
      TranslationGaugeInvariant generator action ∧
      action base = 0 := by
  refine ⟨radialAction base euler,
    radial_action_hasFDerivAt euler hDifferentiable hHelmholtz base,
    radial_action_translation_gauge_invariant
      generator euler hDifferentiable hHelmholtz hHorizontal base, ?_⟩
  exact radial_action_at_base base euler

end P0EFTJanusLinearGaugeNoetherReconstruction
end JanusFormal
