import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalPalatiniLinear4D

/-!
# Closure of the spatial conformal scalar-curvature formula

This gate contracts the exact Palatini/quadratic Ricci split.  The analytic
normal form of the Palatini contraction is supplied by the preceding gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalCurvatureClosure4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusSpatialConformalCurvatureJet4D
open P0EFTJanusMappingTorusSpatialConformalPalatiniLinear4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev Index4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

theorem localConformalRicciQuadratic_eq
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localConformalRicciQuadratic
        period hPeriod scale patch coordinate first second =
      localConformalQuadraticRicciCorrection
        period hPeriod scale patch coordinate first second :=
  rfl

theorem localConformalScalarCurvatureCorrection_split
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localConformalScalarCurvatureCorrection
        period hPeriod scale patch coordinate =
      localConformalPalatiniLinearScalarCorrection
          period hPeriod scale patch coordinate +
        localConformalQuadraticScalarCorrection
          period hPeriod scale patch coordinate := by
  unfold localConformalScalarCurvatureCorrection
    localConformalPalatiniLinearScalarCorrection
    localConformalQuadraticScalarCorrection
  simp only [localConformalRicciCorrection_eq_palatiniLinear_add_quadratic,
    localConformalRicciQuadratic_eq, mul_add, Finset.sum_add_distrib]

theorem localConformalScalarCurvatureCorrection_eq_standard
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localConformalScalarCurvatureCorrection
        period hPeriod scale patch coordinate =
      localStandardConformalScalarCurvatureCorrection
        period hPeriod scale patch coordinate := by
  rw [localConformalScalarCurvatureCorrection_split,
    localConformalPalatiniLinearScalarCorrection_eq_standard
      period hPeriod scale hScale patch coordinate]
  exact
    (localStandardConformalScalarCorrection_eq_linear_add_quadratic
      period hPeriod scale hScale patch coordinate).symm

theorem localScalarCurvature_conformal_standard
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ *
        (localScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate +
          localStandardConformalScalarCurvatureCorrection
            period hPeriod scale patch coordinate) := by
  exact
    (localScalarCurvature_conformal_standard_iff
      period hPeriod scale hScale patch coordinate).2
      (localConformalScalarCurvatureCorrection_eq_standard
        period hPeriod scale hScale patch coordinate)

end

end P0EFTJanusMappingTorusSpatialConformalCurvatureClosure4D
end JanusFormal
