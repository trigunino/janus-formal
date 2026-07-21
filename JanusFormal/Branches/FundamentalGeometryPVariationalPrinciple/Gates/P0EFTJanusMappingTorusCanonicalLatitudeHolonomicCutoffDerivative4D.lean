import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCollarHolonomicCoordinateEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

/-!
# Canonical latitude cutoff in normal-first holonomic coordinates
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeHolonomicCutoffDerivative4D

set_option autoImplicit false
noncomputable section

open scoped ContDiff
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D

abbrev Vector4 := Fin 4 → Real

def holonomicNormalCoordinate : Vector4 →L[Real] Real :=
  ContinuousLinearMap.proj 0

/-- The collar cutoff expressed in a normal-first `R⁴` coordinate system. -/
def canonicalLatitudeHolonomicCollarCutoff (coordinate : Vector4) : Real :=
  canonicalLatitudeCollarCutoff (holonomicNormalCoordinate coordinate)

theorem canonicalLatitudeHolonomicCollarCutoff_contDiff :
    ContDiff Real ∞ canonicalLatitudeHolonomicCollarCutoff :=
  canonicalLatitudeCollarCutoff_contDiff.comp
    holonomicNormalCoordinate.contDiff

theorem canonicalLatitudeHolonomicCollarCutoff_fderiv_basis
    (coordinate : Vector4) (index : Fin 4) :
    fderiv Real canonicalLatitudeHolonomicCollarCutoff coordinate
        (Pi.single index 1) =
      if index = 0 then deriv canonicalLatitudeCollarCutoff (coordinate 0)
      else 0 := by
  have hDerivative : HasDerivAt canonicalLatitudeCollarCutoff
      (deriv canonicalLatitudeCollarCutoff (coordinate 0)) (coordinate 0) :=
    (canonicalLatitudeCollarCutoff_contDiff.differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hComp := hDerivative.comp_hasFDerivAt coordinate
    holonomicNormalCoordinate.hasFDerivAt
  rw [show canonicalLatitudeHolonomicCollarCutoff =
      canonicalLatitudeCollarCutoff ∘ holonomicNormalCoordinate by rfl,
    hComp.fderiv]
  by_cases hIndex : index = 0
  · subst index
    simp [holonomicNormalCoordinate]
  · simp [holonomicNormalCoordinate, hIndex]

theorem canonicalLatitudeHolonomicCollarCutoff_fderiv_normal
    (coordinate : Vector4) :
    fderiv Real canonicalLatitudeHolonomicCollarCutoff coordinate
        (Pi.single (0 : Fin 4) 1) =
      deriv canonicalLatitudeCollarCutoff (coordinate 0) := by
  rw [canonicalLatitudeHolonomicCollarCutoff_fderiv_basis]
  simp

theorem canonicalLatitudeHolonomicCollarCutoff_normalOnlyAt
    (coordinate : Vector4) :
    LocalCutoffNormalOnlyAt canonicalLatitudeHolonomicCollarCutoff coordinate := by
  intro tangent
  rw [canonicalLatitudeHolonomicCollarCutoff_fderiv_basis]
  simp

theorem canonicalLatitudeHolonomicCollarCutoff_differentiableAt
    (coordinate : Vector4) :
    DifferentiableAt Real canonicalLatitudeHolonomicCollarCutoff coordinate :=
  (canonicalLatitudeHolonomicCollarCutoff_contDiff.differentiable
    (by simp)).differentiableAt

/-- The local covariant Leibniz rule is now fully instantiated by the
normal-first canonical cutoff. For a conserved Green current, only its
coordinate-`0` normal flux remains. -/
theorem localActualCanonicalLatitudeCutoffGreenCoordinateDivergence_eq_normalFlux_of_free
    (period : Real) (hPeriod : period ≠ 0)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4)
    (hFree : localActualScalarGreenCoordinateDivergence period hPeriod metric patch
      field test coordinate = 0) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod metric patch
        field test canonicalLatitudeHolonomicCollarCutoff coordinate =
      deriv canonicalLatitudeCollarCutoff (coordinate 0) *
        localActualScalarGreenCurrent period hPeriod metric patch field test
          coordinate 0 := by
  rw [localActualCutoffScalarGreenCoordinateDivergence_eq_normalGradientFlux_of_free
    period hPeriod metric patch field test canonicalLatitudeHolonomicCollarCutoff
      coordinate (canonicalLatitudeHolonomicCollarCutoff_differentiableAt coordinate)
      hFree (canonicalLatitudeHolonomicCollarCutoff_normalOnlyAt coordinate),
    canonicalLatitudeHolonomicCollarCutoff_fderiv_normal]

end
end P0EFTJanusMappingTorusCanonicalLatitudeHolonomicCutoffDerivative4D
end JanusFormal
