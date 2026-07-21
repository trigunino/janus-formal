import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D

/-!
# Holonomic transition compatibility of the actual scalar Green divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicAtlasScalarGreenDivergenceTransition4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private theorem fixedSignMetric_eq_of_metric_orientation_eq
    (first second : FixedSignMetric4)
    (hMetric : first.metric = second.metric)
    (hOrientation : first.orientation = second.orientation) :
    first = second := by
  cases first
  cases second
  simpa only [FixedSignMetric4.mk.injEq] using And.intro hMetric hOrientation

/-- The actual Green divergence is invariant under a common rebased metric
transition and rebased second-jet transitions for both scalar fields. -/
theorem localActualScalarGreenCoordinateDivergence_eq_of_rebasedTransitions
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (fieldAgreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate)
    (testAgreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric test firstPatch secondPatch firstCoordinate secondCoordinate) :
    localActualScalarGreenCoordinateDivergence period hPeriod metric firstPatch
        field test firstCoordinate =
      localActualScalarGreenCoordinateDivergence period hPeriod metric secondPatch
        field test secondCoordinate := by
  have hMetric :
      localFixedSignMetric period hPeriod metric firstPatch firstCoordinate =
        localFixedSignMetric period hPeriod metric secondPatch secondCoordinate := by
    apply fixedSignMetric_eq_of_metric_orientation_eq
    · exact fieldAgreement.metricFirstJet.metricMatrix_eq
    · exact congrArg Matrix.det fieldAgreement.metricFirstJet.metricMatrix_eq
  rw [localActualScalarGreenCoordinateDivergence_eq_waveDifference,
    localActualScalarGreenCoordinateDivergence_eq_waveDifference,
    fieldAgreement.scalarSecondJet.field_eq,
    testAgreement.scalarSecondJet.field_eq,
    hMetric,
    localCovariantScalarJet_eq_of_overlap period hPeriod metric test
      firstPatch secondPatch firstCoordinate secondCoordinate
      fieldAgreement.metricFirstJet testAgreement.scalarSecondJet,
    localCovariantScalarJet_eq_of_overlap period hPeriod metric field
      firstPatch secondPatch firstCoordinate secondCoordinate
      fieldAgreement.metricFirstJet fieldAgreement.scalarSecondJet]

/-- Joint transition contract needed to glue the scalar Green divergence. -/
structure CanonicalRebasedHolonomicAtlasScalarGreenTransitionJetContract
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)) : Prop where
  fieldJets : CanonicalRebasedHolonomicAtlasTransitionJetContract
    period hPeriod metric field atlasPatches
  testJets : CanonicalRebasedHolonomicAtlasTransitionJetContract
    period hPeriod metric test atlasPatches

/-- Exact overlap compatibility required to glue the actual Green divergence
to a quotient scalar. -/
def CanonicalAtlasActualScalarGreenDivergenceCompatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)) : Prop :=
  ∀ (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod),
    firstPatch ∈ atlasPatches → secondPatch ∈ atlasPatches →
    ∀ (firstCoordinate secondCoordinate : Vector4),
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        localActualScalarGreenCoordinateDivergence period hPeriod metric firstPatch
            field test firstCoordinate =
          localActualScalarGreenCoordinateDivergence period hPeriod metric secondPatch
            field test secondCoordinate

theorem CanonicalRebasedHolonomicAtlasScalarGreenTransitionJetContract.compatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod))
    (contract : CanonicalRebasedHolonomicAtlasScalarGreenTransitionJetContract
      period hPeriod metric field test atlasPatches) :
    CanonicalAtlasActualScalarGreenDivergenceCompatible period hPeriod
      metric field test atlasPatches := by
  intro firstPatch secondPatch hFirst hSecond firstCoordinate secondCoordinate
    hSamePoint
  exact localActualScalarGreenCoordinateDivergence_eq_of_rebasedTransitions
    period hPeriod metric field test firstPatch secondPatch
      firstCoordinate secondCoordinate
      (contract.fieldJets.agreement firstPatch secondPatch hFirst hSecond
        firstCoordinate secondCoordinate hSamePoint)
      (contract.testJets.agreement firstPatch secondPatch hFirst hSecond
        firstCoordinate secondCoordinate hSamePoint)

end
end P0EFTJanusMappingTorusCanonicalHolonomicAtlasScalarGreenDivergenceTransition4D
end JanusFormal
