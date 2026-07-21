import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasScalarGreenDivergenceTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

/-!
# Global gluing of the actual scalar Green divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalScalarGreenDivergenceGluing4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasScalarGreenDivergenceTransition4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- A covering holonomic atlas equipped with the exact joint transition jets
needed to glue the actual Green divergence. -/
structure CanonicalHolonomicAtlasScalarGreenDivergenceBridge
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod) where
  atlas : CanonicalHolonomicAtlasCover period hPeriod
  transitionJets :
    CanonicalRebasedHolonomicAtlasScalarGreenTransitionJetContract
      period hPeriod metric field test atlas.atlasPatches

private def chosenPatch
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field test : SmoothScalarField period hPeriod}
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  Classical.choose (bridge.atlas.covers point)

private theorem chosenPatch_mem
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field test : SmoothScalarField period hPeriod}
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod) :
    chosenPatch period hPeriod bridge point ∈ bridge.atlas.atlasPatches :=
  (Classical.choose_spec (bridge.atlas.covers point)).1

private def chosenCoordinate
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field test : SmoothScalarField period hPeriod}
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod) : Vector4 :=
  Classical.choose (Classical.choose_spec (bridge.atlas.covers point)).2

private theorem chosenCoordinate_mapsTo
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field test : SmoothScalarField period hPeriod}
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod) :
    (chosenPatch period hPeriod bridge point).coordinateMap
        (chosenCoordinate period hPeriod bridge point) = point :=
  Classical.choose_spec (Classical.choose_spec (bridge.atlas.covers point)).2

/-- Globally glued actual scalar Green divergence on the effective quotient. -/
def globalActualScalarGreenDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod) : Real :=
  localActualScalarGreenCoordinateDivergence period hPeriod metric
    (chosenPatch period hPeriod bridge point) field test
    (chosenCoordinate period hPeriod bridge point)

/-- The glued scalar equals the actual divergence in every selected
representative, hence is independent of the choice used in its definition. -/
theorem globalActualScalarGreenDivergence_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (hPatch : patch ∈ bridge.atlas.atlasPatches)
    (coordinate : Vector4) (hCoordinate : patch.coordinateMap coordinate = point) :
    globalActualScalarGreenDivergence period hPeriod metric field test bridge point =
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
        field test coordinate := by
  apply CanonicalRebasedHolonomicAtlasScalarGreenTransitionJetContract.compatible
    period hPeriod metric field test bridge.atlas.atlasPatches bridge.transitionJets
    (chosenPatch period hPeriod bridge point) patch
    (chosenPatch_mem period hPeriod bridge point) hPatch
    (chosenCoordinate period hPeriod bridge point) coordinate
  exact (chosenCoordinate_mapsTo period hPeriod bridge point).trans hCoordinate.symm

/-- Every representative computes the global divergence by the genuine Green
wave-difference formula. -/
theorem globalActualScalarGreenDivergence_eq_waveDifference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : EffectiveQuotient period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (hPatch : patch ∈ bridge.atlas.atlasPatches)
    (coordinate : Vector4) (hCoordinate : patch.coordinateMap coordinate = point) :
    globalActualScalarGreenDivergence period hPeriod metric field test bridge point =
      localScalarRepresentative period hPeriod field patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch test coordinate) -
        localScalarRepresentative period hPeriod test patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch field coordinate) := by
  rw [globalActualScalarGreenDivergence_eq_local period hPeriod metric field test
    bridge point patch hPatch coordinate hCoordinate]
  exact localActualScalarGreenCoordinateDivergence_eq_waveDifference
    period hPeriod metric patch field test coordinate

/-- Pullback of the globally glued scalar divergence to the cut bulk. -/
def cutBulkGlobalActualScalarGreenDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasScalarGreenDivergenceBridge
      period hPeriod metric field test)
    (point : PositiveHemisphereCutBulk period hPeriod) : Real :=
  globalActualScalarGreenDivergence period hPeriod metric field test bridge
    (cutBulkToAmbient period hPeriod point)

end
end P0EFTJanusMappingTorusGlobalScalarGreenDivergenceGluing4D
end JanusFormal
