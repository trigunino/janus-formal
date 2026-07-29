import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaGerm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionThirdJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicRiemannEndomorphismBridge4D

/-!
# Differentiated fixed-transition Levi--Civita law

The fixed-germ Christoffel law is differentiated before curvature
antisymmetrization.  The third transition jet is then shown to cancel in the
two outer directions, and the existing Riemann endomorphism bridge is extended
from basis vectors to an arbitrary input vector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaDerivative4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaGerm4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionThirdJet4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D
open P0EFTJanusMappingTorusIntrinsicRiemannEndomorphismBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Exact derivative identity obtained from the fixed transition germ before
any antisymmetrization.  Its rightmost summand is the varying Hessian of the
transition; differentiating it produces the third transition jet. -/
theorem fixedHolonomicTransition_leviCivitaDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real
        (fun current =>
          fderiv Real transition current
            (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
              current (Pi.single first 1) (Pi.single second 1)))
        firstCoordinate =
      fderiv Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
              (transition current)
              (fderiv Real transition current (Pi.single first 1))
              (fderiv Real transition current (Pi.single second 1)) +
            fderiv Real (fderiv Real transition) current
              (Pi.single first 1) (Pi.single second 1))
        firstCoordinate :=
  (fixedHolonomicTransition_leviCivita_eventuallyEq period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint first
    second).fderiv_eq

/-- Directional form of the differentiated fixed-germ Christoffel law. -/
theorem fixedHolonomicTransition_leviCivitaDerivative_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate direction : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second : Index4) :
    let transition :=
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
    fderiv Real
        (fun current =>
          fderiv Real transition current
            (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
              current (Pi.single first 1) (Pi.single second 1)))
        firstCoordinate direction =
      fderiv Real
        (fun current =>
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
              (transition current)
              (fderiv Real transition current (Pi.single first 1))
              (fderiv Real transition current (Pi.single second 1)) +
            fderiv Real (fderiv Real transition) current
              (Pi.single first 1) (Pi.single second 1))
        firstCoordinate direction := by
  exact congrArg
    (fun derivative : Vector4 →L[Real] Vector4 => derivative direction)
    (fixedHolonomicTransition_leviCivitaDerivative period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate samePoint first
      second)

/-- The third-jet contribution vanishes in the outer antisymmetrization used
to form Riemann curvature. -/
theorem fixedHolonomicTransition_thirdDerivative_antisymmetrization
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (first second third : Vector4) :
    holonomicCoordinateTransitionThirdDerivativeAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate samePoint
          first second third -
        holonomicCoordinateTransitionThirdDerivativeAt period hPeriod
          firstPatch secondPatch firstCoordinate secondCoordinate samePoint
          second first third =
      0 := by
  rw [holonomicCoordinateTransitionThirdDerivativeAt_swap_outer period hPeriod
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint first
    second third]
  exact sub_self _

/-- The Riemann endomorphism bridge on an arbitrary input vector, obtained by
linearity from its coordinate-basis component theorem. -/
theorem localLeviCivitaRiemannEndomorphism_vector_component
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4)
    (upper first second : Index4) :
    localLeviCivitaRiemannEndomorphism period hPeriod metric patch coordinate
        first second vector upper =
      ∑ lower : Index4,
        vector lower *
          localRiemannCurvature period hPeriod metric patch coordinate
            upper lower first second := by
  classical
  have vectorExpansion :
      vector = ∑ lower : Index4, vector lower • Pi.single lower 1 := by
    ext current
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single current]
    · simp
    · intro lower _ hLower
      simp [hLower]
    · simp
  let curvature :=
    localLeviCivitaRiemannEndomorphism period hPeriod metric patch coordinate
      first second
  calc
    curvature vector upper =
        curvature
          (∑ lower : Index4, vector lower • Pi.single lower 1) upper := by
      rw [← vectorExpansion]
    _ = ∑ lower : Index4,
        vector lower * curvature (Pi.single lower 1) upper := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro lower _
      rw [localLeviCivitaRiemannEndomorphism_basis_component period hPeriod
        metric patch coordinate upper lower first second]

end

end P0EFTJanusMappingTorusCanonicalHolonomicFixedTransitionLeviCivitaDerivative4D
end JanusFormal
