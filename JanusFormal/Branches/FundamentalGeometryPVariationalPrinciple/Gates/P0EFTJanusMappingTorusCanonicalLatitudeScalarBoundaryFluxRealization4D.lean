import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D

/-!
# Concrete D8 scalar boundary flux on the canonical collar

The global divergence interface and the proved latitude integration by parts
have different domains.  This gate therefore constructs the exact fiberwise
collar specialization.  Its boundary functional is the oriented difference
of the intrinsic metric-gradient flux through the two latitude endpoints.

An explicit predicate records when a global divergence interface restricts to
this collar interface.  No global manifold Stokes theorem is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeScalarBoundaryFluxRealization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D
open P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeometricNormalJunction4D
open P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Intrinsic D8 metric-gradient flux density through one canonical latitude
normal.  This is defined along the explicit collar, not as a global normal
section of the one-sided throat. -/
def canonicalLatitudeIntrinsicD8NormalFluxDensity
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeValue period hPeriod variation base normal *
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal)
      (generalLorentzScalarGradient period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal))
      (canonicalLatitudeNormalVector period hPeriod base normal)

/-- The intrinsic metric pairing with the unit collar normal is the genuine
manifold directional derivative. -/
theorem intrinsicD8Gradient_pair_canonicalLatitudeNormal_eq_derivative
    (field : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal)
        (generalLorentzScalarGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal))
        (canonicalLatitudeNormalVector period hPeriod base normal) =
      canonicalLatitudeDerivative period hPeriod field base normal := by
  let point := quotientNormalLatitude period hPeriod
    (canonicalLatitudeAnchor period hPeriod base) normal
  let gradient := generalLorentzScalarGradient period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) field point
  let normalVector := canonicalLatitudeNormalVector period hPeriod base normal
  have hFlat := metric_flat_generalLorentzScalarGradient period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) field point
  have hFlatApply := congrArg (fun covector => covector normalVector) hFlat
  have hMusical := congrArg
    (fun current => current gradient normalVector)
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor
      point)
  calc
    _ = (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point
        gradient normalVector := by
      simpa [point, gradient, normalVector] using hMusical.symm
    _ = scalarDifferential period hPeriod field point normalVector :=
      hFlatApply
    _ = mvfderiv coverModelWithCorners field.toFun point normalVector := rfl
    _ = canonicalLatitudeDerivative period hPeriod field base normal := by
      simpa [point, normalVector] using
        (canonicalLatitudeDerivative_eq_mvfderiv_normal period hPeriod field
          base normal).symm

theorem canonicalLatitudeIntrinsicD8NormalFluxDensity_eq_derivative_mul_value
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeIntrinsicD8NormalFluxDensity period hPeriod field
        variation base normal =
      canonicalLatitudeDerivative period hPeriod field base normal *
        canonicalLatitudeValue period hPeriod variation base normal := by
  unfold canonicalLatitudeIntrinsicD8NormalFluxDensity
  rw [intrinsicD8Gradient_pair_canonicalLatitudeNormal_eq_derivative]
  ring

/-- Oriented concrete D8 flux through the two boundary components of one
closed latitude fiber. -/
def canonicalLatitudeIntrinsicD8OrientedBoundaryFiber
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeIntrinsicD8NormalFluxDensity period hPeriod field
      variation base 1 -
    canonicalLatitudeIntrinsicD8NormalFluxDensity period hPeriod field
      variation base 0

theorem canonicalLatitudeIntrinsicD8OrientedBoundaryFiber_eq_boundaryFiber
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeIntrinsicD8OrientedBoundaryFiber period hPeriod field
        variation base =
      canonicalLatitudeScalarBoundaryFiber period hPeriod field variation
        base := by
  unfold canonicalLatitudeIntrinsicD8OrientedBoundaryFiber
  rw [canonicalLatitudeIntrinsicD8NormalFluxDensity_eq_derivative_mul_value,
    canonicalLatitudeIntrinsicD8NormalFluxDensity_eq_derivative_mul_value]
  rfl

/-- Minimal divergence/boundary interface on one canonical latitude fiber.
It is the precise collar analogue of
`GeneralLorentzScalarDivergenceBoundaryInterface`. -/
structure CanonicalLatitudeScalarDivergenceBoundaryInterface where
  divergence : SmoothScalarField period hPeriod →
    CanonicalLatitudeBase → Real → Real
  boundaryFlux : SmoothScalarField period hPeriod →
    SmoothScalarField period hPeriod → CanonicalLatitudeBase → Real
  integrationByParts : ∀ (field variation : SmoothScalarField period hPeriod)
      (base : CanonicalLatitudeBase),
    canonicalLatitudeScalarKineticFiber period hPeriod field variation base =
      -(∫ normal in (0 : Real)..1,
          divergence field base normal *
            canonicalLatitudeValue period hPeriod variation base normal) +
        boundaryFlux field variation base

/-- Exact intrinsic D8 collar interface supplied by the proved interval IPP. -/
def canonicalLatitudeIntrinsicD8DivergenceBoundaryInterface :
    CanonicalLatitudeScalarDivergenceBoundaryInterface period hPeriod where
  divergence := canonicalLatitudeSecondDerivative period hPeriod
  boundaryFlux :=
    canonicalLatitudeIntrinsicD8OrientedBoundaryFiber period hPeriod
  integrationByParts := by
    intro field variation base
    rw [canonicalLatitudeIntrinsicD8OrientedBoundaryFiber_eq_boundaryFiber]
    exact canonicalLatitudeScalarKineticFiber_eq_euler_add_boundary
      period hPeriod field variation base

/-- Fiberwise scalar first variation, including the mass contribution. -/
def canonicalLatitudeScalarCollarFirstVariationFiber
    (_interface : CanonicalLatitudeScalarDivergenceBoundaryInterface period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeScalarKineticFiber period hPeriod field variation base -
    ∫ normal in (0 : Real)..1,
      massSquared * canonicalLatitudeValue period hPeriod field base normal *
        canonicalLatitudeValue period hPeriod variation base normal

/-- Weak Euler pairing on one latitude fiber. -/
def canonicalLatitudeScalarCollarWeakEulerFiber
    (interface : CanonicalLatitudeScalarDivergenceBoundaryInterface period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) : Real :=
  -(∫ normal in (0 : Real)..1,
      interface.divergence field base normal *
        canonicalLatitudeValue period hPeriod variation base normal) -
    ∫ normal in (0 : Real)..1,
      massSquared * canonicalLatitudeValue period hPeriod field base normal *
        canonicalLatitudeValue period hPeriod variation base normal

theorem canonicalLatitudeScalarCollarFirstVariationFiber_eq_weakEuler_add_boundary
    (interface : CanonicalLatitudeScalarDivergenceBoundaryInterface period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarCollarFirstVariationFiber period hPeriod interface
        massSquared field variation base =
      canonicalLatitudeScalarCollarWeakEulerFiber period hPeriod interface
          massSquared field variation base +
        interface.boundaryFlux field variation base := by
  unfold canonicalLatitudeScalarCollarFirstVariationFiber
    canonicalLatitudeScalarCollarWeakEulerFiber
  rw [interface.integrationByParts field variation base]
  ring

theorem canonicalLatitudeIntrinsicD8WeakEulerFiber_eq_zero_of_euler
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      field)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarCollarWeakEulerFiber period hPeriod
        (canonicalLatitudeIntrinsicD8DivergenceBoundaryInterface period hPeriod)
        massSquared field variation base = 0 := by
  unfold canonicalLatitudeScalarCollarWeakEulerFiber
    canonicalLatitudeIntrinsicD8DivergenceBoundaryInterface
  have hIntegral :
      (∫ normal in (0 : Real)..1,
          canonicalLatitudeSecondDerivative period hPeriod field base normal *
            canonicalLatitudeValue period hPeriod variation base normal) =
        -(∫ normal in (0 : Real)..1,
          massSquared * canonicalLatitudeValue period hPeriod field base normal *
            canonicalLatitudeValue period hPeriod variation base normal) := by
    calc
      _ = ∫ normal in (0 : Real)..1,
          -(massSquared * canonicalLatitudeValue period hPeriod field base normal *
            canonicalLatitudeValue period hPeriod variation base normal) := by
        apply intervalIntegral.integral_congr
        intro normal _
        dsimp only
        have hResidual := hEuler base normal
        unfold canonicalLatitudeScalarEulerResidual at hResidual
        have hSecond :
            canonicalLatitudeSecondDerivative period hPeriod field base normal =
              -(massSquared *
                canonicalLatitudeValue period hPeriod field base normal) := by
          linarith
        rw [hSecond]
        ring
      _ = _ := intervalIntegral.integral_neg
  rw [hIntegral]
  ring

theorem canonicalLatitudeIntrinsicD8BoundaryFlux_eq_zero_of_endpointDirichlet
    (field variation : SmoothScalarField period hPeriod)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod
      variation)
    (base : CanonicalLatitudeBase) :
    (canonicalLatitudeIntrinsicD8DivergenceBoundaryInterface period hPeriod).boundaryFlux
        field variation base = 0 := by
  change canonicalLatitudeIntrinsicD8OrientedBoundaryFiber period hPeriod
    field variation base = 0
  rw [canonicalLatitudeIntrinsicD8OrientedBoundaryFiber_eq_boundaryFiber]
  exact canonicalLatitudeScalarBoundaryFiber_eq_zero_of_endpointDirichlet
    period hPeriod field variation hInner hOuter base

/-- Exact collar stationarity for Euler fields and test variations vanishing
at both collar endpoints. -/
theorem canonicalLatitudeIntrinsicD8CollarFirstVariationFiber_eq_zero
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      field)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod
      variation)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarCollarFirstVariationFiber period hPeriod
        (canonicalLatitudeIntrinsicD8DivergenceBoundaryInterface period hPeriod)
        massSquared field variation base = 0 := by
  rw [canonicalLatitudeScalarCollarFirstVariationFiber_eq_weakEuler_add_boundary,
    canonicalLatitudeIntrinsicD8WeakEulerFiber_eq_zero_of_euler period hPeriod
      massSquared field variation hEuler base,
    canonicalLatitudeIntrinsicD8BoundaryFlux_eq_zero_of_endpointDirichlet
      period hPeriod field variation hInner hOuter base,
    add_zero]

/-- Measured oriented flux of the concrete collar interface. -/
def canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux
    (field variation : SmoothScalarField period hPeriod) : Real :=
  ∫ base,
    canonicalLatitudeIntrinsicD8OrientedBoundaryFiber period hPeriod field
      variation base
    ∂(canonicalLatitudeBaseMeasure period)

theorem canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux_eq_measuredBoundary
    (field variation : SmoothScalarField period hPeriod) :
    canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux period hPeriod field
        variation =
      canonicalLatitudeMeasuredScalarBoundary period hPeriod field variation := by
  unfold canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux
    canonicalLatitudeMeasuredScalarBoundary
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeIntrinsicD8OrientedBoundaryFiber_eq_boundaryFiber
      period hPeriod field variation base

theorem canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux_eq_zero_of_endpointDirichlet
    (field variation : SmoothScalarField period hPeriod)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod
      variation) :
    canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux period hPeriod field
      variation = 0 := by
  unfold canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeIntrinsicD8BoundaryFlux_eq_zero_of_endpointDirichlet
      period hPeriod field variation hInner hOuter base

/-- Measured collar first variation. -/
def canonicalLatitudeMeasuredIntrinsicD8FirstVariation
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod) : Real :=
  ∫ base,
    canonicalLatitudeScalarCollarFirstVariationFiber period hPeriod
      (canonicalLatitudeIntrinsicD8DivergenceBoundaryInterface period hPeriod)
      massSquared field variation base
    ∂(canonicalLatitudeBaseMeasure period)

theorem canonicalLatitudeMeasuredIntrinsicD8FirstVariation_eq_zero
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared
      field)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod
      variation) :
    canonicalLatitudeMeasuredIntrinsicD8FirstVariation period hPeriod
      massSquared field variation = 0 := by
  unfold canonicalLatitudeMeasuredIntrinsicD8FirstVariation
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeIntrinsicD8CollarFirstVariationFiber_eq_zero
      period hPeriod massSquared field variation hEuler hInner hOuter base

/-- Exact statement that a global D8 divergence interface restricts to the
proved canonical collar boundary functional.  Supplying this predicate is
strictly weaker than claiming a global Stokes theorem. -/
def GeneralLorentzScalarBoundaryFluxSpecializesToCanonicalLatitudeCollar
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod) :
    Prop :=
  ∀ field variation : SmoothScalarField period hPeriod,
    generalLorentzScalarBoundaryFlux period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface field
        variation =
      canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux period hPeriod field
        variation

theorem generalLorentzScalarBoundaryFlux_eq_zero_of_canonicalCollarDirichlet
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (hSpecializes :
      GeneralLorentzScalarBoundaryFluxSpecializesToCanonicalLatitudeCollar
        period hPeriod interface)
    (field variation : SmoothScalarField period hPeriod)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod
      variation) :
    generalLorentzScalarBoundaryFlux period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface field
      variation = 0 := by
  rw [hSpecializes field variation]
  exact
    canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux_eq_zero_of_endpointDirichlet
      period hPeriod field variation hInner hOuter

/-- Existing global action stationarity follows whenever its interface is
certified to specialize to the exact collar flux. -/
theorem canonicalIntrinsicD8HolonomicScalarAction_line_hasDerivAt_zero_of_canonicalCollar
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (hSpecializes :
      GeneralLorentzScalarBoundaryFluxSpecializesToCanonicalLatitudeCollar
        period hPeriod interface)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hAction : CanonicalGeneralLorentzScalarVariationIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared field
      variation (intrinsicPointwiseFrame period hPeriod))
    (hWeakIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface massSquared
      field variation)
    (hWeak : GeneralLorentzScalarWeakEulerEquation period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface massSquared
      field variation)
    (hInner : SatisfiesDirichlet period hPeriod Real 0 variation)
    (hOuter : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod
      variation) :
    HasDerivAt
      (fun epsilon : Real =>
        canonicalGeneralLorentzHolonomicScalarAction period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared
          (scalarFieldLine period hPeriod field variation epsilon)
          (intrinsicPointwiseFrame period hPeriod))
      0 0 := by
  apply canonicalGeneralLorentzHolonomicScalarAction_line_hasDerivAt_zero
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      interface massSquared field variation hAction hWeakIntegrable hWeak
  exact generalLorentzScalarBoundaryFlux_eq_zero_of_canonicalCollarDirichlet
    period hPeriod interface hSpecializes field variation hInner hOuter

/-- Compatibility needed to compare the two-sided collar flux with the
previous global throat-flux packaging. -/
def IntrinsicD8NormalBoundaryFluxAgreesWithCanonicalLatitudeCollar
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod) : Prop :=
  ∀ field variation : SmoothScalarField period hPeriod,
    canonicalLatitudeMeasuredIntrinsicD8BoundaryFlux period hPeriod field
        variation =
      canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting
        field variation normal

/-- Exact adapter to the pre-existing global realization predicate. -/
theorem intrinsicD8ScalarNormalBoundaryFluxRealization_of_canonicalCollar
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hSpecializes :
      GeneralLorentzScalarBoundaryFluxSpecializesToCanonicalLatitudeCollar
        period hPeriod interface)
    (hAgrees : IntrinsicD8NormalBoundaryFluxAgreesWithCanonicalLatitudeCollar
      period hPeriod splitting normal) :
    IntrinsicD8ScalarNormalBoundaryFluxRealization period hPeriod interface
      splitting normal := by
  intro field variation
  exact (hSpecializes field variation).trans (hAgrees field variation)

end

end P0EFTJanusMappingTorusCanonicalLatitudeScalarBoundaryFluxRealization4D
end JanusFormal
