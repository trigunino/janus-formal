import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D

/-!
# Frame-free Maxwell potential Hessian

At fixed smooth Lorentz metric, the frame-free Maxwell action is an exact
quadratic polynomial in the intrinsic abelian gauge potential.  The
polarization of its global curvature pairing therefore defines a genuine
symmetric bilinear Hessian on arbitrary smooth potential directions.

The affine-line and two-parameter mixed derivatives are identified with this
Hessian.  Exact gauge directions lie in its left and right kernels by the
already proved global gauge invariance.

The metric is fixed throughout.  No arbitrary metric--potential block,
field-space Fréchet structure, gauge quotient topology, or coupled
Einstein--Maxwell Jacobi operator is constructed here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D

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
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-! ## Bilinearity of the global curvature pairing -/

theorem globalMaxwellPairing_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric (first + second) third point =
      globalMaxwellPairing period hPeriod metric first third point +
        globalMaxwellPairing period hPeriod metric second third point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod metric (first + second) third
        witness.patch witness.coordinate =
      localMaxwellPairing period hPeriod metric first third
          witness.patch witness.coordinate +
        localMaxwellPairing period hPeriod metric second third
          witness.patch witness.coordinate
  exact localMaxwellPairing_add_left period hPeriod metric
    first second third witness.patch witness.coordinate

theorem globalMaxwellPairing_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric first (second + third) point =
      globalMaxwellPairing period hPeriod metric first second point +
        globalMaxwellPairing period hPeriod metric first third point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod metric first (second + third)
        witness.patch witness.coordinate =
      localMaxwellPairing period hPeriod metric first second
          witness.patch witness.coordinate +
        localMaxwellPairing period hPeriod metric first third
          witness.patch witness.coordinate
  exact localMaxwellPairing_add_right period hPeriod metric
    first second third witness.patch witness.coordinate

theorem globalMaxwellPairing_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric (scalar • first) second point =
      scalar *
        globalMaxwellPairing period hPeriod metric first second point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod metric (scalar • first) second
        witness.patch witness.coordinate =
      scalar *
        localMaxwellPairing period hPeriod metric first second
          witness.patch witness.coordinate
  exact localMaxwellPairing_smul_left period hPeriod metric scalar
    first second witness.patch witness.coordinate

theorem globalMaxwellPairing_smul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric first (scalar • second) point =
      scalar *
        globalMaxwellPairing period hPeriod metric first second point := by
  let witness := selectedMaxwellPairingChart period hPeriod point
  change
    localMaxwellPairing period hPeriod metric first (scalar • second)
        witness.patch witness.coordinate =
      scalar *
        localMaxwellPairing period hPeriod metric first second
          witness.patch witness.coordinate
  exact localMaxwellPairing_smul_right period hPeriod metric scalar
    first second witness.patch witness.coordinate

/-! ## Polarized density and integrated bilinear Hessian -/

def frameFreeMaxwellPotentialHessianDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    -(1 / 4 : Real) *
      (globalMaxwellPairing period hPeriod metric first second point +
        globalMaxwellPairing period hPeriod metric second first point)
  contMDiff_toFun :=
    contMDiff_const.mul
      ((globalMaxwellPairing_contMDiff period hPeriod metric first second).add
        (globalMaxwellPairing_contMDiff
          period hPeriod metric second first))

theorem frameFreeMaxwellPotentialHessianDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    Integrable
      (frameFreeMaxwellPotentialHessianDensity period hPeriod
        metric first second)
      (generalLorentzVolumeMeasure period hPeriod metric) := by
  letI := generalLorentzVolumeMeasure_isFinite period hPeriod metric
  exact
    (frameFreeMaxwellPotentialHessianDensity period hPeriod
      metric first second)
      |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

def frameFreeMaxwellPotentialHessianValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) : Real :=
  ∫ point,
    frameFreeMaxwellPotentialHessianDensity period hPeriod
      metric first second point
    ∂generalLorentzVolumeMeasure period hPeriod metric

/-- The exact Maxwell Hessian at fixed metric, packaged as a bilinear form on
arbitrary smooth intrinsic gauge-potential directions. -/
def frameFreeMaxwellPotentialHessian
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    LinearMap.BilinForm Real
      (SmoothAbelianGaugePotential period hPeriod) :=
  LinearMap.mk₂ Real
    (frameFreeMaxwellPotentialHessianValue period hPeriod metric)
    (fun first second third => by
      unfold frameFreeMaxwellPotentialHessianValue
      rw [show
        frameFreeMaxwellPotentialHessianDensity period hPeriod metric
            (first + second) third =
          frameFreeMaxwellPotentialHessianDensity period hPeriod metric
              first third +
            frameFreeMaxwellPotentialHessianDensity period hPeriod metric
              second third by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change
          -(1 / 4 : Real) *
              (globalMaxwellPairing period hPeriod metric
                  (first + second) third point +
                globalMaxwellPairing period hPeriod metric
                  third (first + second) point) =
            -(1 / 4 : Real) *
                (globalMaxwellPairing period hPeriod metric first third point +
                  globalMaxwellPairing period hPeriod metric third first point) +
              -(1 / 4 : Real) *
                (globalMaxwellPairing period hPeriod metric second third point +
                  globalMaxwellPairing period hPeriod metric third second point)
        rw [globalMaxwellPairing_add_left,
          globalMaxwellPairing_add_right]
        ring]
      exact integral_add
        (frameFreeMaxwellPotentialHessianDensity_integrable
          period hPeriod metric first third)
        (frameFreeMaxwellPotentialHessianDensity_integrable
          period hPeriod metric second third))
    (fun scalar first second => by
      unfold frameFreeMaxwellPotentialHessianValue
      rw [show
        frameFreeMaxwellPotentialHessianDensity period hPeriod metric
            (scalar • first) second =
          scalar •
            frameFreeMaxwellPotentialHessianDensity period hPeriod metric
              first second by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change
          -(1 / 4 : Real) *
              (globalMaxwellPairing period hPeriod metric
                  (scalar • first) second point +
                globalMaxwellPairing period hPeriod metric
                  second (scalar • first) point) =
            scalar *
              (-(1 / 4 : Real) *
                (globalMaxwellPairing period hPeriod metric first second point +
                  globalMaxwellPairing period hPeriod metric second first point))
        rw [globalMaxwellPairing_smul_left,
          globalMaxwellPairing_smul_right]
        ring]
      change
        (∫ point, scalar *
          frameFreeMaxwellPotentialHessianDensity period hPeriod
            metric first second point
          ∂generalLorentzVolumeMeasure period hPeriod metric) =
        scalar *
          ∫ point,
            frameFreeMaxwellPotentialHessianDensity period hPeriod
              metric first second point
            ∂generalLorentzVolumeMeasure period hPeriod metric
      simp only [integral_const_mul])
    (fun first second third => by
      unfold frameFreeMaxwellPotentialHessianValue
      rw [show
        frameFreeMaxwellPotentialHessianDensity period hPeriod metric
            first (second + third) =
          frameFreeMaxwellPotentialHessianDensity period hPeriod metric
              first second +
            frameFreeMaxwellPotentialHessianDensity period hPeriod metric
              first third by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change
          -(1 / 4 : Real) *
              (globalMaxwellPairing period hPeriod metric
                  first (second + third) point +
                globalMaxwellPairing period hPeriod metric
                  (second + third) first point) =
            -(1 / 4 : Real) *
                (globalMaxwellPairing period hPeriod metric first second point +
                  globalMaxwellPairing period hPeriod metric second first point) +
              -(1 / 4 : Real) *
                (globalMaxwellPairing period hPeriod metric first third point +
                  globalMaxwellPairing period hPeriod metric third first point)
        rw [globalMaxwellPairing_add_right,
          globalMaxwellPairing_add_left]
        ring]
      exact integral_add
        (frameFreeMaxwellPotentialHessianDensity_integrable
          period hPeriod metric first second)
        (frameFreeMaxwellPotentialHessianDensity_integrable
          period hPeriod metric first third))
    (fun scalar first second => by
      unfold frameFreeMaxwellPotentialHessianValue
      rw [show
        frameFreeMaxwellPotentialHessianDensity period hPeriod metric
            first (scalar • second) =
          scalar •
            frameFreeMaxwellPotentialHessianDensity period hPeriod metric
              first second by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change
          -(1 / 4 : Real) *
              (globalMaxwellPairing period hPeriod metric
                  first (scalar • second) point +
                globalMaxwellPairing period hPeriod metric
                  (scalar • second) first point) =
            scalar *
              (-(1 / 4 : Real) *
                (globalMaxwellPairing period hPeriod metric first second point +
                  globalMaxwellPairing period hPeriod metric second first point))
        rw [globalMaxwellPairing_smul_right,
          globalMaxwellPairing_smul_left]
        ring]
      change
        (∫ point, scalar *
          frameFreeMaxwellPotentialHessianDensity period hPeriod
            metric first second point
          ∂generalLorentzVolumeMeasure period hPeriod metric) =
        scalar *
          ∫ point,
            frameFreeMaxwellPotentialHessianDensity period hPeriod
              metric first second point
            ∂generalLorentzVolumeMeasure period hPeriod metric
      simp only [integral_const_mul])

@[simp]
theorem frameFreeMaxwellPotentialHessian_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    frameFreeMaxwellPotentialHessian period hPeriod metric first second =
      frameFreeMaxwellPotentialHessianValue
        period hPeriod metric first second :=
  rfl

theorem frameFreeMaxwellPotentialHessian_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    frameFreeMaxwellPotentialHessian period hPeriod metric first second =
      frameFreeMaxwellPotentialHessian period hPeriod metric second first := by
  unfold frameFreeMaxwellPotentialHessian
    frameFreeMaxwellPotentialHessianValue
    frameFreeMaxwellPotentialHessianDensity
  apply integral_congr_ae
  filter_upwards [] with point
  ring

/-! ## Exact affine-line expansion -/

theorem frameFreeMaxwellDensity_line_expansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeMaxwellDensity period hPeriod metric
        (gaugePotentialLine period hPeriod potential direction epsilon) point =
      frameFreeMaxwellDensity period hPeriod metric potential point +
        epsilon *
          frameFreeMaxwellPotentialHessianDensity period hPeriod
            metric potential direction point +
        (epsilon ^ 2 / 2) *
          frameFreeMaxwellPotentialHessianDensity period hPeriod
            metric direction direction point := by
  change
    -(1 / 4 : Real) *
        globalMaxwellPairing period hPeriod metric
          (potential + epsilon • direction)
          (potential + epsilon • direction) point =
      -(1 / 4 : Real) *
          globalMaxwellPairing period hPeriod metric
            potential potential point +
        epsilon *
          (-(1 / 4 : Real) *
            (globalMaxwellPairing period hPeriod metric
                potential direction point +
              globalMaxwellPairing period hPeriod metric
                direction potential point)) +
        (epsilon ^ 2 / 2) *
          (-(1 / 4 : Real) *
            (globalMaxwellPairing period hPeriod metric
                direction direction point +
              globalMaxwellPairing period hPeriod metric
                direction direction point))
  rw [globalMaxwellPairing_add_left,
    globalMaxwellPairing_add_right,
    globalMaxwellPairing_add_right,
    globalMaxwellPairing_smul_right,
    globalMaxwellPairing_smul_left,
    globalMaxwellPairing_smul_right,
    globalMaxwellPairing_smul_left]
  ring

def frameFreeMaxwellPotentialActionCurve
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real) : Real :=
  generalLorentzFrameFreeMaxwellAction period hPeriod metric
    (gaugePotentialLine period hPeriod potential direction epsilon)

theorem frameFreeMaxwellPotentialActionCurve_eq_quadratic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real) :
    frameFreeMaxwellPotentialActionCurve period hPeriod
        metric potential direction epsilon =
      generalLorentzFrameFreeMaxwellAction
          period hPeriod metric potential +
        epsilon *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric potential direction +
        (epsilon ^ 2 / 2) *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric direction direction := by
  let measure := generalLorentzVolumeMeasure period hPeriod metric
  have hBase :=
    frameFreeMaxwellDensity_integrable period hPeriod metric potential
  have hFirst :=
    (frameFreeMaxwellPotentialHessianDensity_integrable
      period hPeriod metric potential direction).const_mul epsilon
  have hSecond :=
    (frameFreeMaxwellPotentialHessianDensity_integrable
      period hPeriod metric direction direction).const_mul
        (epsilon ^ 2 / 2)
  unfold frameFreeMaxwellPotentialActionCurve
    generalLorentzFrameFreeMaxwellAction
  calc
    (∫ point,
        frameFreeMaxwellDensity period hPeriod metric
          (gaugePotentialLine period hPeriod potential direction epsilon) point
        ∂measure) =
        ∫ point,
          frameFreeMaxwellDensity period hPeriod metric potential point +
            epsilon *
              frameFreeMaxwellPotentialHessianDensity period hPeriod
                metric potential direction point +
            (epsilon ^ 2 / 2) *
              frameFreeMaxwellPotentialHessianDensity period hPeriod
                metric direction direction point
          ∂measure := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact frameFreeMaxwellDensity_line_expansion
        period hPeriod metric potential direction epsilon point
    _ =
        (∫ point,
          frameFreeMaxwellDensity period hPeriod metric potential point
          ∂measure) +
          epsilon *
            (∫ point,
              frameFreeMaxwellPotentialHessianDensity period hPeriod
                metric potential direction point
              ∂measure) +
          (epsilon ^ 2 / 2) *
            (∫ point,
              frameFreeMaxwellPotentialHessianDensity period hPeriod
                metric direction direction point
              ∂measure) := by
      calc
        _ =
            (∫ point,
              frameFreeMaxwellDensity period hPeriod metric potential point +
                epsilon *
                  frameFreeMaxwellPotentialHessianDensity period hPeriod
                    metric potential direction point
              ∂measure) +
              ∫ point,
                (epsilon ^ 2 / 2) *
                  frameFreeMaxwellPotentialHessianDensity period hPeriod
                    metric direction direction point
                ∂measure := by
          exact integral_add (hBase.add hFirst) hSecond
        _ = _ := by
          rw [integral_add hBase hFirst,
            integral_const_mul, integral_const_mul]
    _ = _ := rfl

theorem frameFreeMaxwellPotentialActionCurve_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real) :
    HasDerivAt
      (frameFreeMaxwellPotentialActionCurve period hPeriod
        metric potential direction)
      (frameFreeMaxwellPotentialHessian period hPeriod
          metric potential direction +
        epsilon *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric direction direction)
      epsilon := by
  rw [show
    frameFreeMaxwellPotentialActionCurve period hPeriod
        metric potential direction =
      (fun varied =>
        generalLorentzFrameFreeMaxwellAction
            period hPeriod metric potential +
          varied *
            frameFreeMaxwellPotentialHessian period hPeriod
              metric potential direction) +
      fun varied =>
        varied ^ 2 *
          ((1 / 2 : Real) *
            frameFreeMaxwellPotentialHessian period hPeriod
              metric direction direction) by
    funext varied
    rw [frameFreeMaxwellPotentialActionCurve_eq_quadratic]
    simp only [Pi.add_apply]
    ring]
  have hAffine :=
    ((hasDerivAt_id (𝕜 := Real) epsilon).mul_const
      (frameFreeMaxwellPotentialHessian period hPeriod
        metric potential direction)).const_add
      (generalLorentzFrameFreeMaxwellAction
        period hPeriod metric potential)
  have hQuadratic :=
    ((hasDerivAt_id (𝕜 := Real) epsilon).pow 2).mul_const
      ((1 / 2 : Real) *
        frameFreeMaxwellPotentialHessian period hPeriod
          metric direction direction)
  exact (hAffine.add hQuadratic).congr_deriv (by
    simp only [id_eq, one_mul]
    ring)

theorem frameFreeMaxwellPotentialActionCurve_deriv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real) :
    deriv
        (frameFreeMaxwellPotentialActionCurve period hPeriod
          metric potential direction)
        epsilon =
      frameFreeMaxwellPotentialHessian period hPeriod
          metric potential direction +
        epsilon *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric direction direction :=
  (frameFreeMaxwellPotentialActionCurve_hasDerivAt
    period hPeriod metric potential direction epsilon).deriv

theorem frameFreeMaxwellPotentialActionCurve_deriv_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (epsilon : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (frameFreeMaxwellPotentialActionCurve period hPeriod
            metric potential direction)
          varied)
      (frameFreeMaxwellPotentialHessian period hPeriod
        metric direction direction)
      epsilon := by
  rw [show
    (fun varied =>
      deriv
        (frameFreeMaxwellPotentialActionCurve period hPeriod
          metric potential direction)
        varied) =
      fun varied =>
        frameFreeMaxwellPotentialHessian period hPeriod
            metric potential direction +
          varied *
            frameFreeMaxwellPotentialHessian period hPeriod
              metric direction direction by
    funext varied
    exact frameFreeMaxwellPotentialActionCurve_deriv
      period hPeriod metric potential direction varied]
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id (𝕜 := Real) epsilon).mul_const
      (frameFreeMaxwellPotentialHessian period hPeriod
        metric direction direction)).const_add
      (frameFreeMaxwellPotentialHessian period hPeriod
        metric potential direction)

/-! ## Two-parameter mixed derivative -/

def frameFreeMaxwellPotentialMixedActionSurface
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential first second : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) : Real :=
  frameFreeMaxwellPotentialActionCurve period hPeriod metric
    (gaugePotentialLine period hPeriod
      potential second secondParameter)
    first firstParameter

theorem frameFreeMaxwellPotentialMixedActionSurface_hasDerivAt_first
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential first second : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) :
    HasDerivAt
      (fun varied =>
        frameFreeMaxwellPotentialMixedActionSurface period hPeriod
          metric potential first second varied secondParameter)
      (frameFreeMaxwellPotentialHessian period hPeriod metric
          (gaugePotentialLine period hPeriod
            potential second secondParameter)
          first +
        firstParameter *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric first first)
      firstParameter := by
  exact frameFreeMaxwellPotentialActionCurve_hasDerivAt
    period hPeriod metric
      (gaugePotentialLine period hPeriod
        potential second secondParameter)
      first firstParameter

theorem frameFreeMaxwellPotentialMixedActionSurface_deriv_hasDerivAt_second
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential first second : SmoothAbelianGaugePotential period hPeriod)
    (firstParameter secondParameter : Real) :
    HasDerivAt
      (fun varied =>
        deriv
          (fun firstVaried =>
            frameFreeMaxwellPotentialMixedActionSurface period hPeriod
              metric potential first second firstVaried varied)
          firstParameter)
      (frameFreeMaxwellPotentialHessian period hPeriod
        metric first second)
      secondParameter := by
  rw [show
    (fun varied =>
      deriv
        (fun firstVaried =>
          frameFreeMaxwellPotentialMixedActionSurface period hPeriod
            metric potential first second firstVaried varied)
        firstParameter) =
      fun varied =>
        frameFreeMaxwellPotentialHessian period hPeriod metric
            (gaugePotentialLine period hPeriod potential second varied)
            first +
          firstParameter *
            frameFreeMaxwellPotentialHessian period hPeriod
              metric first first by
    funext varied
    exact
      (frameFreeMaxwellPotentialMixedActionSurface_hasDerivAt_first
        period hPeriod metric potential first second
          firstParameter varied).deriv]
  rw [show
    (fun varied =>
      frameFreeMaxwellPotentialHessian period hPeriod metric
          (gaugePotentialLine period hPeriod potential second varied)
          first +
        firstParameter *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric first first) =
      fun varied =>
        (frameFreeMaxwellPotentialHessian period hPeriod
            metric potential first +
          firstParameter *
            frameFreeMaxwellPotentialHessian period hPeriod
              metric first first) +
        varied *
          frameFreeMaxwellPotentialHessian period hPeriod
            metric second first by
    funext varied
    simp only [gaugePotentialLine, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring]
  rw [frameFreeMaxwellPotentialHessian_symmetric
    period hPeriod metric first second]
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id (𝕜 := Real) secondParameter).mul_const
      (frameFreeMaxwellPotentialHessian period hPeriod
        metric second first)).const_add
      (frameFreeMaxwellPotentialHessian period hPeriod
          metric potential first +
        firstParameter *
          frameFreeMaxwellPotentialHessian period hPeriod
          metric first first)

/-! ## Exact gauge kernel -/

theorem globalMaxwellPairing_zero_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric 0 second point = 0 := by
  have hAdd := globalMaxwellPairing_add_left period hPeriod metric
    0 0 second point
  simp only [zero_add] at hAdd
  linarith

theorem globalMaxwellPairing_zero_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric first 0 point = 0 := by
  have hAdd := globalMaxwellPairing_add_right period hPeriod metric
    first 0 0 point
  simp only [zero_add] at hAdd
  linarith

theorem globalMaxwellPairing_exact_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (second : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric
        (exactGaugePotential period hPeriod parameter) second point =
      0 := by
  have hGauge :=
    globalMaxwellPairing_gaugeTransform_left
      period hPeriod metric parameter 0 second point
  rw [globalMaxwellPairing_zero_left] at hGauge
  simpa [gaugeTransform] using hGauge

theorem globalMaxwellPairing_exact_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (first : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalMaxwellPairing period hPeriod metric first
        (exactGaugePotential period hPeriod parameter) point =
      0 := by
  have hGauge :=
    globalMaxwellPairing_gaugeTransform_right
      period hPeriod metric parameter first 0 point
  rw [globalMaxwellPairing_zero_right] at hGauge
  simpa [gaugeTransform] using hGauge

theorem frameFreeMaxwellPotentialHessian_exact_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (second : SmoothAbelianGaugePotential period hPeriod) :
    frameFreeMaxwellPotentialHessian period hPeriod metric
        (exactGaugePotential period hPeriod parameter) second =
      0 := by
  rw [frameFreeMaxwellPotentialHessian_apply]
  have hDensity :
      frameFreeMaxwellPotentialHessianDensity period hPeriod metric
          (exactGaugePotential period hPeriod parameter) second =
        0 := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change
      -(1 / 4 : Real) *
          (globalMaxwellPairing period hPeriod metric
              (exactGaugePotential period hPeriod parameter) second point +
            globalMaxwellPairing period hPeriod metric
              second (exactGaugePotential period hPeriod parameter) point) =
        0
    rw [globalMaxwellPairing_exact_left,
      globalMaxwellPairing_exact_right]
    ring
  unfold frameFreeMaxwellPotentialHessianValue
  rw [hDensity]
  change
    (∫ _point : EffectiveQuotient period hPeriod, (0 : Real)
      ∂generalLorentzVolumeMeasure period hPeriod metric) =
      0
  simp only [integral_zero]

theorem frameFreeMaxwellPotentialHessian_exact_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (parameter : GaugeParameter period hPeriod)
    (first : SmoothAbelianGaugePotential period hPeriod) :
    frameFreeMaxwellPotentialHessian period hPeriod metric first
        (exactGaugePotential period hPeriod parameter) =
      0 := by
  rw [frameFreeMaxwellPotentialHessian_symmetric
    period hPeriod metric first
      (exactGaugePotential period hPeriod parameter)]
  exact frameFreeMaxwellPotentialHessian_exact_left
    period hPeriod metric parameter first

end

end P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D
end JanusFormal
