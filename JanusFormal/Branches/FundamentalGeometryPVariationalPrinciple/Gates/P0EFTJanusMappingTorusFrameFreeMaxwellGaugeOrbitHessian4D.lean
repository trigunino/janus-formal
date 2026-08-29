import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

/-!
# Gauge-orbit and conformal--gauge Maxwell Hessians

The frame-free Maxwell action is exactly invariant under the intrinsic
abelian transformation `A ↦ A + dλ` for every smooth Lorentz metric.  Hence
its first and mixed second derivatives along one- and two-parameter gauge
orbits vanish, and the gauge-orbit Hessian is the zero bilinear form.

The exact-gauge kernel is also proved against every arbitrary potential
variation.  Independently, four-dimensional conformal invariance gives a
zero logarithmic-conformal--potential mixed block for every potential
variation.

Only exact gauge-orbit directions and logarithmic-conformal metric directions
are proved null here.  This is not the potential--potential Hessian for
arbitrary physical directions, the Hessian for arbitrary metric variations,
nor a Fréchet Hessian on a field-space chart.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

abbrev GaugeParameter :=
  SmoothQuotientField period hPeriod GaugeLieAlgebra

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Global frame-free gauge invariance -/

theorem globalMaxwellPairing_gaugeTransform_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (potential second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric
        (gaugeTransform period hPeriod parameter potential) second point =
      globalMaxwellPairing period hPeriod metric potential second point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod metric
        (gaugeTransform period hPeriod parameter potential) second
        witness.patch witness.coordinate =
      localMaxwellPairing period hPeriod metric potential second
        witness.patch witness.coordinate
  exact localMaxwellPairing_gaugeTransform_left period hPeriod metric
    parameter potential second witness.patch witness.coordinate

theorem globalMaxwellPairing_gaugeTransform_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (first potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric first
        (gaugeTransform period hPeriod parameter potential) point =
      globalMaxwellPairing period hPeriod metric first potential point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod metric first
        (gaugeTransform period hPeriod parameter potential)
        witness.patch witness.coordinate =
      localMaxwellPairing period hPeriod metric first potential
        witness.patch witness.coordinate
  exact localMaxwellPairing_gaugeTransform_right period hPeriod metric
    parameter first potential witness.patch witness.coordinate

theorem frameFreeMaxwellDensity_gaugeTransform
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeMaxwellDensity period hPeriod metric
        (gaugeTransform period hPeriod parameter potential) point =
      frameFreeMaxwellDensity period hPeriod metric potential point := by
  change
    -(1 / 4 : Real) *
        globalMaxwellPairing period hPeriod metric
          (gaugeTransform period hPeriod parameter potential)
          (gaugeTransform period hPeriod parameter potential) point =
      -(1 / 4 : Real) *
        globalMaxwellPairing period hPeriod metric potential potential point
  rw [globalMaxwellPairing_gaugeTransform_left,
    globalMaxwellPairing_gaugeTransform_right]

theorem generalLorentzFrameFreeMaxwellAction_gaugeTransform
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    generalLorentzFrameFreeMaxwellAction period hPeriod metric
        (gaugeTransform period hPeriod parameter potential) =
      generalLorentzFrameFreeMaxwellAction period hPeriod metric potential := by
  unfold generalLorentzFrameFreeMaxwellAction
  apply integral_congr_ae
  filter_upwards [] with point
  exact frameFreeMaxwellDensity_gaugeTransform
    period hPeriod metric parameter potential point

theorem intrinsicCanonicalFrameFreeMaxwellAction_gaugeTransform
    (parameter : GaugeParameter period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    intrinsicCanonicalFrameFreeMaxwellAction period hPeriod
        (gaugeTransform period hPeriod parameter potential) =
      intrinsicCanonicalFrameFreeMaxwellAction period hPeriod potential := by
  rw [← generalLorentzFrameFreeMaxwellAction_intrinsic,
    generalLorentzFrameFreeMaxwellAction_gaugeTransform,
    generalLorentzFrameFreeMaxwellAction_intrinsic]

/-! ## Exact gauge lines and one-parameter gauge orbits -/

theorem gaugePotentialLine_exactGaugePotential
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (epsilon : Real) :
    gaugePotentialLine period hPeriod potential
        (exactGaugePotential period hPeriod parameter) epsilon =
      gaugeTransform period hPeriod (epsilon • parameter) potential := by
  unfold gaugePotentialLine gaugeTransform
  rw [exactGaugePotential_smul]

def frameFreeMaxwellGaugeOrbitActionCurve
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (epsilon : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod metric
    (gaugeTransform period hPeriod (epsilon • parameter) potential)

theorem frameFreeMaxwellGaugeOrbitActionCurve_eq_reference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (epsilon : Real) :
    frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
        metric potential parameter epsilon =
      generalLorentzFrameFreeMaxwellAction
        period hPeriod metric potential := by
  exact generalLorentzFrameFreeMaxwellAction_gaugeTransform
    period hPeriod metric (epsilon • parameter) potential

theorem frameFreeMaxwellGaugeOrbitActionCurve_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod) :
    ContDiff Real ∞
      (frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
        metric potential parameter) := by
  rw [show
    frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
        metric potential parameter =
      fun _epsilon =>
        generalLorentzFrameFreeMaxwellAction
          period hPeriod metric potential by
    funext epsilon
    exact frameFreeMaxwellGaugeOrbitActionCurve_eq_reference
      period hPeriod metric potential parameter epsilon]
  exact contDiff_const

theorem frameFreeMaxwellGaugeOrbitActionCurve_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (epsilon : Real) :
    HasDerivAt
      (frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
        metric potential parameter)
      0 epsilon := by
  rw [show
    frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
        metric potential parameter =
      fun _varied =>
        generalLorentzFrameFreeMaxwellAction
          period hPeriod metric potential by
    funext varied
    exact frameFreeMaxwellGaugeOrbitActionCurve_eq_reference
      period hPeriod metric potential parameter varied]
  exact hasDerivAt_const epsilon _

theorem frameFreeMaxwellGaugeOrbitActionCurve_deriv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (epsilon : Real) :
    deriv
        (frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
          metric potential parameter)
        epsilon =
      0 :=
  (frameFreeMaxwellGaugeOrbitActionCurve_hasDerivAt
    period hPeriod metric potential parameter epsilon).deriv

/-! ## Two-parameter gauge orbits and their Hessian -/

def frameFreeMaxwellGaugeOrbitMixedActionCurve
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GaugeParameter period hPeriod)
    (firstParameter secondParameter : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod metric
    (gaugeTransform period hPeriod
      (firstParameter • first + secondParameter • second) potential)

theorem frameFreeMaxwellGaugeOrbitMixedActionCurve_eq_reference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GaugeParameter period hPeriod)
    (firstParameter secondParameter : Real) :
    frameFreeMaxwellGaugeOrbitMixedActionCurve period hPeriod
        metric potential first second firstParameter secondParameter =
      generalLorentzFrameFreeMaxwellAction
        period hPeriod metric potential := by
  exact generalLorentzFrameFreeMaxwellAction_gaugeTransform
    period hPeriod metric
      (firstParameter • first + secondParameter • second) potential

theorem frameFreeMaxwellGaugeOrbitMixedActionCurve_hasDerivAt_first
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GaugeParameter period hPeriod)
    (firstParameter secondParameter : Real) :
    HasDerivAt
      (fun varied =>
        frameFreeMaxwellGaugeOrbitMixedActionCurve period hPeriod
          metric potential first second varied secondParameter)
      0 firstParameter := by
  rw [show
    (fun varied =>
      frameFreeMaxwellGaugeOrbitMixedActionCurve period hPeriod
        metric potential first second varied secondParameter) =
      fun _varied =>
        generalLorentzFrameFreeMaxwellAction
          period hPeriod metric potential by
    funext varied
    exact frameFreeMaxwellGaugeOrbitMixedActionCurve_eq_reference
      period hPeriod metric potential first second varied secondParameter]
  exact hasDerivAt_const firstParameter _

/-- The Maxwell Hessian pulled back to exact gauge-orbit directions. -/
def frameFreeMaxwellGaugeOrbitHessian
    (_metric : SmoothGeneralLorentzMetric period hPeriod)
    (_potential : SmoothAbelianGaugePotential period hPeriod) :
    LinearMap.BilinForm Real (GaugeParameter period hPeriod) :=
  0

@[simp]
theorem frameFreeMaxwellGaugeOrbitHessian_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GaugeParameter period hPeriod) :
    frameFreeMaxwellGaugeOrbitHessian period hPeriod
        metric potential first second =
      0 :=
  rfl

theorem frameFreeMaxwellGaugeOrbitHessian_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GaugeParameter period hPeriod) :
    frameFreeMaxwellGaugeOrbitHessian period hPeriod
        metric potential first second =
      frameFreeMaxwellGaugeOrbitHessian period hPeriod
        metric potential second first :=
  rfl

theorem frameFreeMaxwellGaugeOrbitActionCurve_deriv_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (epsilon : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
            metric potential parameter)
          varied)
      (frameFreeMaxwellGaugeOrbitHessian period hPeriod
        metric potential parameter parameter)
      epsilon := by
  rw [show
    (fun varied =>
      deriv
        (frameFreeMaxwellGaugeOrbitActionCurve period hPeriod
          metric potential parameter)
        varied) =
      fun _varied => 0 by
    funext varied
    exact frameFreeMaxwellGaugeOrbitActionCurve_deriv
      period hPeriod metric potential parameter varied]
  exact hasDerivAt_const epsilon 0

theorem frameFreeMaxwellGaugeOrbitMixedActionCurve_deriv_hasDerivAt_second
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GaugeParameter period hPeriod)
    (firstParameter secondParameter : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (fun firstVaried =>
            frameFreeMaxwellGaugeOrbitMixedActionCurve period hPeriod
              metric potential first second firstVaried varied)
          firstParameter)
      (frameFreeMaxwellGaugeOrbitHessian period hPeriod
        metric potential first second)
      secondParameter := by
  rw [show
    (fun varied =>
      deriv
        (fun firstVaried =>
          frameFreeMaxwellGaugeOrbitMixedActionCurve period hPeriod
            metric potential first second firstVaried varied)
        firstParameter) =
      fun _varied => 0 by
    funext varied
    exact
      (frameFreeMaxwellGaugeOrbitMixedActionCurve_hasDerivAt_first
        period hPeriod metric potential first second
          firstParameter varied).deriv]
  exact hasDerivAt_const secondParameter 0

/-! ## Exact-gauge kernel against arbitrary potential variations -/

def frameFreeMaxwellGaugePotentialMixedActionCurve
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (gaugeDirection : GaugeParameter period hPeriod)
    (potentialDirection : SmoothAbelianGaugePotential period hPeriod)
    (gaugeParameter potentialParameter : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod metric
    (gaugeTransform period hPeriod
      (gaugeParameter • gaugeDirection)
      (gaugePotentialLine period hPeriod
        potential potentialDirection potentialParameter))

theorem frameFreeMaxwellGaugePotentialMixedActionCurve_eq_potentialLine
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (gaugeDirection : GaugeParameter period hPeriod)
    (potentialDirection : SmoothAbelianGaugePotential period hPeriod)
    (gaugeParameter potentialParameter : Real) :
    frameFreeMaxwellGaugePotentialMixedActionCurve period hPeriod
        metric potential gaugeDirection potentialDirection
        gaugeParameter potentialParameter =
      generalLorentzFrameFreeMaxwellAction period hPeriod metric
        (gaugePotentialLine period hPeriod
          potential potentialDirection potentialParameter) := by
  exact generalLorentzFrameFreeMaxwellAction_gaugeTransform
    period hPeriod metric (gaugeParameter • gaugeDirection)
      (gaugePotentialLine period hPeriod
        potential potentialDirection potentialParameter)

theorem frameFreeMaxwellGaugePotentialMixedActionCurve_hasDerivAt_gauge
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (gaugeDirection : GaugeParameter period hPeriod)
    (potentialDirection : SmoothAbelianGaugePotential period hPeriod)
    (gaugeParameter potentialParameter : Real) :
    HasDerivAt
      (fun varied =>
        frameFreeMaxwellGaugePotentialMixedActionCurve period hPeriod
          metric potential gaugeDirection potentialDirection
          varied potentialParameter)
      0 gaugeParameter := by
  rw [show
    (fun varied =>
      frameFreeMaxwellGaugePotentialMixedActionCurve period hPeriod
        metric potential gaugeDirection potentialDirection
        varied potentialParameter) =
      fun _varied =>
        generalLorentzFrameFreeMaxwellAction period hPeriod metric
          (gaugePotentialLine period hPeriod
            potential potentialDirection potentialParameter) by
    funext varied
    exact
      frameFreeMaxwellGaugePotentialMixedActionCurve_eq_potentialLine
        period hPeriod metric potential gaugeDirection potentialDirection
          varied potentialParameter]
  exact hasDerivAt_const gaugeParameter _

/-- Mixed Maxwell Hessian with one exact gauge direction and one arbitrary
potential direction.  Gauge invariance forces this block to vanish. -/
def frameFreeMaxwellGaugePotentialMixedHessian
    (_metric : SmoothGeneralLorentzMetric period hPeriod)
    (_potential : SmoothAbelianGaugePotential period hPeriod) :
    GaugeParameter period hPeriod →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real :=
  0

@[simp]
theorem frameFreeMaxwellGaugePotentialMixedHessian_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (gaugeDirection : GaugeParameter period hPeriod)
    (potentialDirection : SmoothAbelianGaugePotential period hPeriod) :
    frameFreeMaxwellGaugePotentialMixedHessian period hPeriod
        metric potential gaugeDirection potentialDirection =
      0 :=
  rfl

theorem frameFreeMaxwellGaugePotentialMixedActionCurve_deriv_hasDerivAt_potential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (gaugeDirection : GaugeParameter period hPeriod)
    (potentialDirection : SmoothAbelianGaugePotential period hPeriod)
    (gaugeParameter potentialParameter : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (fun gaugeVaried =>
            frameFreeMaxwellGaugePotentialMixedActionCurve period hPeriod
              metric potential gaugeDirection potentialDirection
              gaugeVaried varied)
          gaugeParameter)
      (frameFreeMaxwellGaugePotentialMixedHessian period hPeriod
        metric potential gaugeDirection potentialDirection)
      potentialParameter := by
  rw [show
    (fun varied =>
      deriv
        (fun gaugeVaried =>
          frameFreeMaxwellGaugePotentialMixedActionCurve period hPeriod
            metric potential gaugeDirection potentialDirection
            gaugeVaried varied)
        gaugeParameter) =
      fun _varied => 0 by
    funext varied
    exact
      (frameFreeMaxwellGaugePotentialMixedActionCurve_hasDerivAt_gauge
        period hPeriod metric potential gaugeDirection potentialDirection
          gaugeParameter varied).deriv]
  exact hasDerivAt_const potentialParameter 0

/-! ## Log-conformal kernel against arbitrary potential variations -/

def conformalPotentialFrameFreeMaxwellMixedActionCurve
    (baseScale conformalDirection : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential potentialDirection :
      SmoothAbelianGaugePotential period hPeriod)
    (conformalParameter potentialParameter : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod
    (conformalLorentzMetricCurve period hPeriod
      baseScale conformalDirection hBaseScale conformalParameter)
    (gaugePotentialLine period hPeriod
      potential potentialDirection potentialParameter)

theorem conformalPotentialFrameFreeMaxwellMixedActionCurve_eq_reference
    (baseScale conformalDirection : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential potentialDirection :
      SmoothAbelianGaugePotential period hPeriod)
    (conformalParameter potentialParameter : Real) :
    conformalPotentialFrameFreeMaxwellMixedActionCurve period hPeriod
        baseScale conformalDirection hBaseScale
        potential potentialDirection
        conformalParameter potentialParameter =
      intrinsicCanonicalFrameFreeMaxwellAction period hPeriod
        (gaugePotentialLine period hPeriod
          potential potentialDirection potentialParameter) := by
  exact conformalFrameFreeMaxwellActionCurve_eq_reference
    period hPeriod baseScale conformalDirection hBaseScale
      (gaugePotentialLine period hPeriod
        potential potentialDirection potentialParameter)
      conformalParameter

theorem conformalPotentialFrameFreeMaxwellMixedActionCurve_hasDerivAt_conformal
    (baseScale conformalDirection : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential potentialDirection :
      SmoothAbelianGaugePotential period hPeriod)
    (conformalParameter potentialParameter : Real) :
    HasDerivAt
      (fun varied =>
        conformalPotentialFrameFreeMaxwellMixedActionCurve period hPeriod
          baseScale conformalDirection hBaseScale
          potential potentialDirection varied potentialParameter)
      0 conformalParameter := by
  rw [show
    (fun varied =>
      conformalPotentialFrameFreeMaxwellMixedActionCurve period hPeriod
        baseScale conformalDirection hBaseScale
        potential potentialDirection varied potentialParameter) =
      fun _varied =>
        intrinsicCanonicalFrameFreeMaxwellAction period hPeriod
          (gaugePotentialLine period hPeriod
            potential potentialDirection potentialParameter) by
    funext varied
    exact
      conformalPotentialFrameFreeMaxwellMixedActionCurve_eq_reference
        period hPeriod baseScale conformalDirection hBaseScale
          potential potentialDirection varied potentialParameter]
  exact hasDerivAt_const conformalParameter _

/-- Mixed Maxwell Hessian with one logarithmic-conformal metric direction and
one arbitrary potential direction.  Four-dimensional conformal invariance
forces this block to vanish. -/
def conformalPotentialFrameFreeMaxwellMixedHessian
    (_potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real :=
  0

@[simp]
theorem conformalPotentialFrameFreeMaxwellMixedHessian_eq_zero
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (conformalDirection : SmoothScalarField period hPeriod)
    (potentialDirection : SmoothAbelianGaugePotential period hPeriod) :
    conformalPotentialFrameFreeMaxwellMixedHessian period hPeriod
        potential conformalDirection potentialDirection =
      0 :=
  rfl

theorem conformalPotentialFrameFreeMaxwellMixedActionCurve_deriv_hasDerivAt_potential
    (baseScale conformalDirection : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (potential potentialDirection :
      SmoothAbelianGaugePotential period hPeriod)
    (conformalParameter potentialParameter : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (fun conformalVaried =>
            conformalPotentialFrameFreeMaxwellMixedActionCurve
              period hPeriod baseScale conformalDirection hBaseScale
                potential potentialDirection conformalVaried varied)
          conformalParameter)
      (conformalPotentialFrameFreeMaxwellMixedHessian period hPeriod
        potential conformalDirection potentialDirection)
      potentialParameter := by
  rw [show
    (fun varied =>
      deriv
        (fun conformalVaried =>
          conformalPotentialFrameFreeMaxwellMixedActionCurve
            period hPeriod baseScale conformalDirection hBaseScale
              potential potentialDirection conformalVaried varied)
        conformalParameter) =
      fun _varied => 0 by
    funext varied
    exact
      (conformalPotentialFrameFreeMaxwellMixedActionCurve_hasDerivAt_conformal
        period hPeriod baseScale conformalDirection hBaseScale
          potential potentialDirection conformalParameter varied).deriv]
  exact hasDerivAt_const potentialParameter 0

end

end P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D
end JanusFormal
