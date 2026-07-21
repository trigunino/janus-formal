import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

/-!
# Pointwise scalar Green divergence on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkPointwiseScalarGreenDivergence4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Coordinate-honest global statement: every quotient point has a genuine
covering holonomic representative where the actual derivative divergence is
both the tensorial jet divergence and the Green wave difference. -/
def QuotientPointwiseActualScalarGreenDivergenceIdentity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod) : Prop :=
  ∀ point : EffectiveQuotient period hPeriod,
    ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4),
      patch.coordinateMap coordinate = point ∧
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
          field test coordinate =
        localSmoothScalarGreenDivergence period hPeriod metric patch
          field test coordinate ∧
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
          field test coordinate =
        localScalarRepresentative period hPeriod field patch coordinate *
            covariantScalarJetWave
              (localFixedSignMetric period hPeriod metric patch coordinate)
              (localCovariantScalarJet period hPeriod metric patch test coordinate) -
          localScalarRepresentative period hPeriod test patch coordinate *
            covariantScalarJetWave
              (localFixedSignMetric period hPeriod metric patch coordinate)
              (localCovariantScalarJet period hPeriod metric patch field coordinate)

theorem quotientPointwiseActualScalarGreenDivergenceIdentity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod) :
    QuotientPointwiseActualScalarGreenDivergenceIdentity period hPeriod
      metric field test := by
  intro point
  rcases canonicalTotalHolonomicAtlasCover_covers period hPeriod point with
    ⟨patch, _hPatch, coordinate, hCoordinate⟩
  exact ⟨patch, coordinate, hCoordinate,
    localActualScalarGreenCoordinateDivergence_eq_localSmooth
      period hPeriod metric patch field test coordinate,
    localActualScalarGreenCoordinateDivergence_eq_waveDifference
      period hPeriod metric patch field test coordinate⟩

/-- The same actual local divergence law is realized above every point of the
global cut bulk through its canonical ambient map. -/
def CutBulkPointwiseActualScalarGreenDivergenceIdentity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod) : Prop :=
  ∀ point : PositiveHemisphereCutBulk period hPeriod,
    ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4),
      patch.coordinateMap coordinate = cutBulkToAmbient period hPeriod point ∧
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
          field test coordinate =
        localSmoothScalarGreenDivergence period hPeriod metric patch
          field test coordinate ∧
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
          field test coordinate =
        localScalarRepresentative period hPeriod field patch coordinate *
            covariantScalarJetWave
              (localFixedSignMetric period hPeriod metric patch coordinate)
              (localCovariantScalarJet period hPeriod metric patch test coordinate) -
          localScalarRepresentative period hPeriod test patch coordinate *
            covariantScalarJetWave
              (localFixedSignMetric period hPeriod metric patch coordinate)
              (localCovariantScalarJet period hPeriod metric patch field coordinate)

theorem cutBulkPointwiseActualScalarGreenDivergenceIdentity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod) :
    CutBulkPointwiseActualScalarGreenDivergenceIdentity period hPeriod
      metric field test := by
  intro point
  exact quotientPointwiseActualScalarGreenDivergenceIdentity
    period hPeriod metric field test (cutBulkToAmbient period hPeriod point)

end
end P0EFTJanusMappingTorusCutBulkPointwiseScalarGreenDivergence4D
end JanusFormal
