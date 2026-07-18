import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D

/-!
# Exact scalar integration by parts on the canonical D8 collar

Mathlib has no general Stokes theorem on manifolds.  The explicit canonical
latitude collar nevertheless reduces the scalar normal integration by parts
to the proved one-dimensional interval theorem.  This file records the exact
fiber identity, its measured form, and the concrete normal boundary term.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D

private abbrev sphereData (period : Real) (hPeriod : period ≠ 0) :=
  reflectedSphereData period hPeriod
private abbrev throatData (period : Real) (hPeriod : period ≠ 0) :=
  fixedEquatorData period hPeriod
private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (throatData period hPeriod)
private abbrev EffectiveCover (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorusCover (sphereData period hPeriod)

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Second normal derivative along one canonical latitude fiber. -/
def canonicalLatitudeSecondDerivative
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real → Real :=
  deriv (canonicalLatitudeDerivative period hPeriod field base)

theorem canonicalLatitudeDerivative_contDiff
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    ContDiff Real ∞ (canonicalLatitudeDerivative period hPeriod field base) := by
  change ContDiff Real ∞
    (deriv (canonicalNormalSlice period hPeriod field
      (canonicalLatitudeAnchor period hPeriod base)))
  exact (contDiff_infty_iff_deriv.mp
    (canonicalNormalSlice_contDiff period hPeriod field
      (canonicalLatitudeAnchor period hPeriod base))).2

theorem canonicalLatitudeDerivative_hasDerivAt
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    HasDerivAt (canonicalLatitudeDerivative period hPeriod field base)
      (canonicalLatitudeSecondDerivative period hPeriod field base normal)
      normal :=
  ((canonicalLatitudeDerivative_contDiff period hPeriod field base).differentiable
    (by simp)).differentiableAt.hasDerivAt

theorem canonicalLatitudeSecondDerivative_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    Continuous (canonicalLatitudeSecondDerivative period hPeriod field base) := by
  unfold canonicalLatitudeSecondDerivative
  exact (canonicalLatitudeDerivative_contDiff period hPeriod field base).continuous_deriv
    (by simp)

/-- Normal kinetic pairing on one closed collar fiber. -/
def canonicalLatitudeScalarKineticFiber
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  ∫ normal in (0 : Real)..1,
    canonicalLatitudeDerivative period hPeriod field base normal *
      canonicalLatitudeDerivative period hPeriod variation base normal

/-- Euler contribution produced by twice differentiating the field normally. -/
def canonicalLatitudeScalarEulerFiber
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  -(∫ normal in (0 : Real)..1,
    canonicalLatitudeSecondDerivative period hPeriod field base normal *
      canonicalLatitudeValue period hPeriod variation base normal)

/-- Oriented endpoint flux on one collar fiber. -/
def canonicalLatitudeScalarBoundaryFiber
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeDerivative period hPeriod field base 1 *
      canonicalLatitudeValue period hPeriod variation base 1 -
    canonicalLatitudeDerivative period hPeriod field base 0 *
      canonicalLatitudeValue period hPeriod variation base 0

/-- Exact interval Stokes/IPP identity on every canonical latitude fiber. -/
theorem canonicalLatitudeScalarKineticFiber_eq_euler_add_boundary
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarKineticFiber period hPeriod field variation base =
      canonicalLatitudeScalarEulerFiber period hPeriod field variation base +
        canonicalLatitudeScalarBoundaryFiber period hPeriod field variation base := by
  have hIPP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : Real)) (b := 1)
    (u := canonicalLatitudeDerivative period hPeriod field base)
    (v := canonicalLatitudeValue period hPeriod variation base)
    (u' := canonicalLatitudeSecondDerivative period hPeriod field base)
    (v' := canonicalLatitudeDerivative period hPeriod variation base)
    (fun normal _ =>
      canonicalLatitudeDerivative_hasDerivAt period hPeriod field base normal)
    (fun normal _ =>
      canonicalLatitudeValue_hasDerivAt period hPeriod variation base normal)
    ((canonicalLatitudeSecondDerivative_continuous period hPeriod field base).intervalIntegrable
      0 1)
    ((canonicalLatitudeDerivative_continuous period hPeriod variation base).intervalIntegrable
      0 1)
  unfold canonicalLatitudeScalarKineticFiber canonicalLatitudeScalarEulerFiber
    canonicalLatitudeScalarBoundaryFiber
  rw [hIPP]
  ring

/-- Measured collar kinetic pairing over the actual canonical throat base. -/
def canonicalLatitudeMeasuredScalarKinetic
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base,
    canonicalLatitudeScalarKineticFiber period hPeriod field variation base
    ∂(canonicalLatitudeBaseMeasure period)

def canonicalLatitudeMeasuredScalarEuler
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base,
    canonicalLatitudeScalarEulerFiber period hPeriod field variation base
    ∂(canonicalLatitudeBaseMeasure period)

def canonicalLatitudeMeasuredScalarBoundary
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base,
    canonicalLatitudeScalarBoundaryFiber period hPeriod field variation base
    ∂(canonicalLatitudeBaseMeasure period)

/-- Unconditional measured IPP, with the Euler and flux terms kept in the
same integrand so no artificial integrability premise is needed. -/
theorem canonicalLatitudeMeasuredScalarKinetic_eq_integral_euler_add_boundary
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real) :
    canonicalLatitudeMeasuredScalarKinetic period hPeriod field variation =
      ∫ base,
        (canonicalLatitudeScalarEulerFiber period hPeriod field variation base +
          canonicalLatitudeScalarBoundaryFiber period hPeriod field variation base)
        ∂(canonicalLatitudeBaseMeasure period) := by
  unfold canonicalLatitudeMeasuredScalarKinetic
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarKineticFiber_eq_euler_add_boundary
      period hPeriod field variation base

/-- Honest hypotheses needed only to split the measured sum into two
independent Bochner integrals. -/
structure CanonicalLatitudeScalarIPPIntegrable
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real) : Prop where
  euler : Integrable
    (canonicalLatitudeScalarEulerFiber period hPeriod field variation)
    (canonicalLatitudeBaseMeasure period)
  boundary : Integrable
    (canonicalLatitudeScalarBoundaryFiber period hPeriod field variation)
    (canonicalLatitudeBaseMeasure period)

theorem canonicalLatitudeMeasuredScalarKinetic_eq_euler_add_boundary
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (hIntegrable : CanonicalLatitudeScalarIPPIntegrable period hPeriod field variation) :
    canonicalLatitudeMeasuredScalarKinetic period hPeriod field variation =
      canonicalLatitudeMeasuredScalarEuler period hPeriod field variation +
        canonicalLatitudeMeasuredScalarBoundary period hPeriod field variation := by
  rw [canonicalLatitudeMeasuredScalarKinetic_eq_integral_euler_add_boundary]
  unfold canonicalLatitudeMeasuredScalarEuler canonicalLatitudeMeasuredScalarBoundary
  exact integral_add hIntegrable.euler hIntegrable.boundary

/-- Inner physical flux of a fiber, before applying the inward orientation
sign from the interval endpoint formula. -/
def canonicalLatitudeScalarInnerBoundaryFiber
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeDerivative period hPeriod field base 0 *
    canonicalLatitudeValue period hPeriod variation base 0

/-- The inner term is the actual manifold directional differential paired
with the variation trace, not an abstract boundary-functional hypothesis. -/
theorem canonicalLatitudeScalarInnerBoundaryFiber_eq_mvfderiv
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarInnerBoundaryFiber period hPeriod field variation base =
      mvfderiv coverModelWithCorners field.toFun
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) 0)
          (canonicalLatitudeNormalVector period hPeriod base 0) *
        variation (fixedThroatQuotientInclusion period hPeriod
          (canonicalLatitudeThroatMap period hPeriod base)) := by
  unfold canonicalLatitudeScalarInnerBoundaryFiber
  rw [canonicalLatitudeDerivative_eq_mvfderiv_normal,
    canonicalLatitudeValue_zero]

theorem canonicalLatitudeValue_zero_eq_zero_of_homogeneousDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (variation : SmoothQuotientField period hPeriod Real)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeValue period hPeriod variation base 0 = 0 := by
  rw [canonicalLatitudeValue_zero]
  simpa only [throatTrace_apply] using
    (throatTrace_apply_eq_zero_of_homogeneousDirichlet period hPeriod variation
      hDirichlet (canonicalLatitudeThroatMap period hPeriod base))

theorem canonicalLatitudeScalarInnerBoundaryFiber_eq_zero_of_homogeneousDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarInnerBoundaryFiber period hPeriod field variation base = 0 := by
  unfold canonicalLatitudeScalarInnerBoundaryFiber
  rw [canonicalLatitudeValue_zero_eq_zero_of_homogeneousDirichlet
    period hPeriod variation hDirichlet base]
  ring

def canonicalLatitudeMeasuredScalarInnerBoundary
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base,
    canonicalLatitudeScalarInnerBoundaryFiber period hPeriod field variation base
    ∂(canonicalLatitudeBaseMeasure period)

theorem canonicalLatitudeMeasuredScalarInnerBoundary_eq_zero_of_homogeneousDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    canonicalLatitudeMeasuredScalarInnerBoundary period hPeriod field variation = 0 := by
  unfold canonicalLatitudeMeasuredScalarInnerBoundary
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarInnerBoundaryFiber_eq_zero_of_homogeneousDirichlet
      period hPeriod field variation hDirichlet base

/-- Explicit Dirichlet condition on the outer endpoint of the unit collar. -/
def CanonicalLatitudeOuterHomogeneousDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (variation : SmoothQuotientField period hPeriod Real) : Prop :=
  ∀ base : CanonicalLatitudeBase,
    canonicalLatitudeValue period hPeriod variation base 1 = 0

theorem canonicalLatitudeScalarBoundaryFiber_eq_zero_of_endpointDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet
      period hPeriod variation)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarBoundaryFiber period hPeriod field variation base = 0 := by
  unfold canonicalLatitudeScalarBoundaryFiber
  rw [hOuter base,
    canonicalLatitudeValue_zero_eq_zero_of_homogeneousDirichlet
      period hPeriod variation hInner base]
  ring

/-- Nonconditional collar Euler identity for the explicit class of smooth
variations vanishing at both collar endpoints. -/
theorem canonicalLatitudeScalarKineticFiber_eq_euler_of_endpointDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet
      period hPeriod variation)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarKineticFiber period hPeriod field variation base =
      canonicalLatitudeScalarEulerFiber period hPeriod field variation base := by
  rw [canonicalLatitudeScalarKineticFiber_eq_euler_add_boundary,
    canonicalLatitudeScalarBoundaryFiber_eq_zero_of_endpointDirichlet
      period hPeriod field variation hInner hOuter base, add_zero]

/-- The corresponding measured weak Euler identity; no separate
integrability assumption is required. -/
theorem canonicalLatitudeMeasuredScalarKinetic_eq_euler_of_endpointDirichlet
    (period : Real) (hPeriod : period ≠ 0)
    (field variation : SmoothQuotientField period hPeriod Real)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet
      period hPeriod variation) :
    canonicalLatitudeMeasuredScalarKinetic period hPeriod field variation =
      canonicalLatitudeMeasuredScalarEuler period hPeriod field variation := by
  unfold canonicalLatitudeMeasuredScalarKinetic canonicalLatitudeMeasuredScalarEuler
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarKineticFiber_eq_euler_of_endpointDirichlet
      period hPeriod field variation hInner hOuter base

end

end P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
end JanusFormal
