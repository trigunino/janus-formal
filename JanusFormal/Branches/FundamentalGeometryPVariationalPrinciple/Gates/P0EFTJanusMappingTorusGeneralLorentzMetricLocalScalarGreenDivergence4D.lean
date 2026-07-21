import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D

/-!
# Local Levi--Civita divergence of the scalar Green current

This gate realizes the Green current and its covariant divergence from the
genuine smooth scalar jets of a supplied holonomic Levi--Civita patch.  It is
still a patchwise statement; no global divergence or Stokes theorem is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

/-- Green current represented by two covariant scalar jets. -/
def covariantScalarGreenJetCurrent
    (data : FixedSignMetric4) (field test : CovariantScalarJet2) : Vector4 :=
  fun index =>
    field.field * covariantScalarJetRaisedGradient data test index -
      test.field * covariantScalarJetRaisedGradient data field index

/-- Product-rule expansion of the Levi--Civita divergence of the jet current. -/
def covariantScalarGreenJetDivergence
    (data : FixedSignMetric4) (field test : CovariantScalarJet2) : Real :=
  ∑ first : Index4,
    ((field.gradient first * covariantScalarJetRaisedGradient data test first +
        field.field * (∑ second : Index4,
          data.metric⁻¹ first second * test.hessian first second)) -
      (test.gradient first * covariantScalarJetRaisedGradient data field first +
        test.field * (∑ second : Index4,
          data.metric⁻¹ first second * field.hessian first second)))

private theorem greenCrossTerms_commute
    (data : FixedSignMetric4) (field test : CovariantScalarJet2) :
    (∑ first : Index4,
        field.gradient first * covariantScalarJetRaisedGradient data test first) =
      ∑ first : Index4,
        test.gradient first * covariantScalarJetRaisedGradient data field first := by
  unfold covariantScalarJetRaisedGradient Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro first _
  have hSymmetric := congrArg
    (fun matrix : Matrix4 => matrix second first) data.inverse_symmetric
  simp only [Matrix.transpose_apply] at hSymmetric
  rw [hSymmetric]
  ring

/-- Local algebraic Green identity for genuine covariant second jets. -/
theorem covariantScalarGreenJetDivergence_eq_waveDifference
    (data : FixedSignMetric4) (field test : CovariantScalarJet2) :
    covariantScalarGreenJetDivergence data field test =
      field.field * covariantScalarJetWave data test -
        test.field * covariantScalarJetWave data field := by
  unfold covariantScalarGreenJetDivergence covariantScalarJetWave
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [greenCrossTerms_commute]
  simp_rw [← Finset.mul_sum]
  ring

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coordinate components of the smooth Green current in the supplied patch. -/
def localSmoothScalarGreenCurrent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) : Vector4 :=
  covariantScalarGreenJetCurrent
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localCovariantScalarJet period hPeriod metric patch field coordinate)
    (localCovariantScalarJet period hPeriod metric patch test coordinate)

/-- Patchwise Levi--Civita divergence of the smooth Green current. -/
def localSmoothScalarGreenDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) : Real :=
  covariantScalarGreenJetDivergence
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localCovariantScalarJet period hPeriod metric patch field coordinate)
    (localCovariantScalarJet period hPeriod metric patch test coordinate)

/-- Concrete local Green identity for smooth quotient scalars. -/
theorem localSmoothScalarGreenDivergence_eq_waveDifference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localSmoothScalarGreenDivergence period hPeriod metric patch field test coordinate =
      localScalarRepresentative period hPeriod field patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch test coordinate) -
        localScalarRepresentative period hPeriod test patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch field coordinate) := by
  unfold localSmoothScalarGreenDivergence
  rw [covariantScalarGreenJetDivergence_eq_waveDifference]
  rfl

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D
end JanusFormal
