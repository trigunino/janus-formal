import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D

/-!
# Normal/tangential split of the local cutoff Green divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

def localActualCutoffScalarGreenCoordinateDivergenceTerm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4)
    (derivative : Index4) : Real :=
  fderiv Real
      (fun current ↦
        localActualCutoffScalarGreenCurrent period hPeriod metric patch field test
          cutoff current derivative)
      coordinate (Pi.single derivative 1) +
    ∑ lower : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          derivative derivative lower *
        localActualCutoffScalarGreenCurrent period hPeriod metric patch field test
          cutoff coordinate lower

def localActualCutoffScalarGreenCoordinateNormalDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4) : Real :=
  localActualCutoffScalarGreenCoordinateDivergenceTerm period hPeriod metric patch
    field test cutoff coordinate 0

def localActualCutoffScalarGreenCoordinateTangentialDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4) : Real :=
  ∑ tangent : Fin 3,
    localActualCutoffScalarGreenCoordinateDivergenceTerm period hPeriod metric patch
      field test cutoff coordinate tangent.succ

theorem localActualCutoffScalarGreenCoordinateDivergence_eq_normal_add_tangential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod metric patch
        field test cutoff coordinate =
      localActualCutoffScalarGreenCoordinateNormalDivergence period hPeriod metric
          patch field test cutoff coordinate +
        localActualCutoffScalarGreenCoordinateTangentialDivergence period hPeriod
          metric patch field test cutoff coordinate := by
  unfold localActualCutoffScalarGreenCoordinateDivergence
    localActualCutoffScalarGreenCoordinateNormalDivergence
    localActualCutoffScalarGreenCoordinateTangentialDivergence
    localActualCutoffScalarGreenCoordinateDivergenceTerm
  exact Fin.sum_univ_succ _

/-- The cutoff has only a normal first derivative in the selected holonomic
coordinates. -/
def LocalCutoffNormalOnlyAt (cutoff : Vector4 → Real) (coordinate : Vector4) : Prop :=
  ∀ tangent : Fin 3,
    fderiv Real cutoff coordinate (Pi.single tangent.succ 1) = 0

/-- For a divergence-free Green current and a normal-only cutoff, the genuine
four-dimensional cutoff divergence reduces exactly to its normal flux term. -/
theorem localActualCutoffScalarGreenCoordinateDivergence_eq_normalGradientFlux_of_free
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4)
    (hCutoff : DifferentiableAt Real cutoff coordinate)
    (hFree : localActualScalarGreenCoordinateDivergence period hPeriod metric patch
      field test coordinate = 0)
    (hNormalOnly : LocalCutoffNormalOnlyAt cutoff coordinate) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod metric patch
        field test cutoff coordinate =
      fderiv Real cutoff coordinate (Pi.single (0 : Index4) 1) *
        localActualScalarGreenCurrent period hPeriod metric patch field test
          coordinate 0 := by
  rw [localActualCutoffScalarGreenCoordinateDivergence_eq_gradientFlux_of_free
    period hPeriod metric patch field test cutoff coordinate hCutoff hFree,
    Fin.sum_univ_succ]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro tangent _
  rw [hNormalOnly tangent, zero_mul]

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D
end JanusFormal
