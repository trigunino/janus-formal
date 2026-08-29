import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-!
# Spectator sectors of the global Candidate-A action

The D10 completion is background spectral data, while the historical
ghost/auxiliary coefficients are present in the global coefficient packet.
None of the nine summands of the current covariant Candidate-A action uses
them.  Replacing only those entries therefore transports all boundary and
regular-action witnesses definitionally and leaves the action unchanged.

This field-level identity does not by itself imply that the chartwise Hessian
vanishes on the corresponding tangents.  Such a conclusion additionally
needs faithful chart curves identifying these replacements with the
corresponding chart directions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalActionSpectatorSectors4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Replace only the D10 completion of a global field configuration. -/
def withD10Completion
    (configuration : GlobalFieldConfiguration period hPeriod)
    (completion : D10SpectralCompletion) :
    GlobalFieldConfiguration period hPeriod where
  geometry := configuration.geometry
  coefficientFields := configuration.coefficientFields
  metrics_eq := configuration.metrics_eq
  legacyMatter_eq_zero := configuration.legacyMatter_eq_zero
  spinCMatter := configuration.spinCMatter
  d10Completion := completion

/-- Boundary witnesses transport unchanged across a D10-only replacement. -/
def boundaryDataWithD10Completion
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data :
      GlobalBoundaryVariationData period hPeriod configuration
        NonNullFace NullFace)
    (completion : D10SpectralCompletion) :
    GlobalBoundaryVariationData period hPeriod
      (withD10Completion period hPeriod configuration completion)
      NonNullFace NullFace where
  nonNullWeight := data.nonNullWeight
  nonNullEinsteinScale := data.nonNullEinsteinScale
  nonNullOrientation := data.nonNullOrientation
  nonNullDirichletJet := data.nonNullDirichletJet
  nullFaces := data.nullFaces
  scalarMassSquared := data.scalarMassSquared
  scalarField := data.scalarField
  scalarTest := data.scalarTest
  scalarControl := data.scalarControl

/-- Every regular action witness transports unchanged across a D10-only
replacement. -/
def actionDataWithD10Completion
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data :
      GlobalCandidateAActionData period hPeriod configuration couplings
        NonNullFace NullFace)
    (completion : D10SpectralCompletion) :
    GlobalCandidateAActionData period hPeriod
      (withD10Completion period hPeriod configuration completion) couplings
      NonNullFace NullFace where
  plusGravity := data.plusGravity
  minusGravity := data.minusGravity
  plusMetric_eq := data.plusMetric_eq
  minusMetric_eq := data.minusMetric_eq
  plusMaxwell := data.plusMaxwell
  minusMaxwell := data.minusMaxwell
  plusGauge_eq := data.plusGauge_eq
  minusGauge_eq := data.minusGauge_eq
  interactionDensity := data.interactionDensity
  interactionDensity_eq := data.interactionDensity_eq
  boundary :=
    boundaryDataWithD10Completion period hPeriod data.boundary completion
  nonNullBoundary := data.nonNullBoundary
  nullActionFaces := data.nullActionFaces
  nullActionGenerator_eq := data.nullActionGenerator_eq
  nullActionInterval_eq := data.nullActionInterval_eq

@[simp]
theorem globalCandidateAMatterAction_withD10Completion
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (completion : D10SpectralCompletion) :
    globalCandidateAMatterAction period hPeriod
        (withD10Completion period hPeriod configuration completion) couplings =
      globalCandidateAMatterAction period hPeriod configuration couplings :=
  rfl

/-- The exact assembled Candidate-A action is insensitive to the D10
completion stored in its global configuration. -/
@[simp]
theorem globalCandidateACovariantAction_withD10Completion
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data :
      GlobalCandidateAActionData period hPeriod configuration couplings
        NonNullFace NullFace)
    (completion : D10SpectralCompletion)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    globalCandidateACovariantAction period hPeriod
        (actionDataWithD10Completion period hPeriod data completion) measure =
      globalCandidateACovariantAction period hPeriod data measure :=
  rfl

/-! ## Ghost and auxiliary spectators -/

/-- Replace only the ghost and auxiliary coefficient fields. -/
def withGhostAuxiliaryFields
    (configuration : GlobalFieldConfiguration period hPeriod)
    (ghosts :
      SmoothQuotientField period hPeriod GhostFiber ×
        SmoothQuotientField period hPeriod GhostFiber)
    (auxiliaries :
      SmoothQuotientField period hPeriod AuxiliaryFiber ×
        SmoothQuotientField period hPeriod AuxiliaryFiber) :
    GlobalFieldConfiguration period hPeriod where
  geometry := configuration.geometry
  coefficientFields :=
    { metrics := configuration.coefficientFields.metrics
      matter := configuration.coefficientFields.matter
      gauge := configuration.coefficientFields.gauge
      ghosts := ghosts
      auxiliaries := auxiliaries
      llAuxMetric := configuration.coefficientFields.llAuxMetric
      llMeasure := configuration.coefficientFields.llMeasure
      llField := configuration.coefficientFields.llField }
  metrics_eq := configuration.metrics_eq
  legacyMatter_eq_zero := configuration.legacyMatter_eq_zero
  spinCMatter := configuration.spinCMatter
  d10Completion := configuration.d10Completion

/-- Boundary witnesses transport unchanged when only ghosts and auxiliaries
are replaced. -/
def boundaryDataWithGhostAuxiliaryFields
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data :
      GlobalBoundaryVariationData period hPeriod configuration
        NonNullFace NullFace)
    (ghosts :
      SmoothQuotientField period hPeriod GhostFiber ×
        SmoothQuotientField period hPeriod GhostFiber)
    (auxiliaries :
      SmoothQuotientField period hPeriod AuxiliaryFiber ×
        SmoothQuotientField period hPeriod AuxiliaryFiber) :
    GlobalBoundaryVariationData period hPeriod
      (withGhostAuxiliaryFields period hPeriod configuration ghosts auxiliaries)
      NonNullFace NullFace where
  nonNullWeight := data.nonNullWeight
  nonNullEinsteinScale := data.nonNullEinsteinScale
  nonNullOrientation := data.nonNullOrientation
  nonNullDirichletJet := data.nonNullDirichletJet
  nullFaces := data.nullFaces
  scalarMassSquared := data.scalarMassSquared
  scalarField := data.scalarField
  scalarTest := data.scalarTest
  scalarControl := data.scalarControl

/-- Regular action witnesses transport unchanged when only ghosts and
auxiliaries are replaced. -/
def actionDataWithGhostAuxiliaryFields
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data :
      GlobalCandidateAActionData period hPeriod configuration couplings
        NonNullFace NullFace)
    (ghosts :
      SmoothQuotientField period hPeriod GhostFiber ×
        SmoothQuotientField period hPeriod GhostFiber)
    (auxiliaries :
      SmoothQuotientField period hPeriod AuxiliaryFiber ×
        SmoothQuotientField period hPeriod AuxiliaryFiber) :
    GlobalCandidateAActionData period hPeriod
      (withGhostAuxiliaryFields period hPeriod configuration ghosts auxiliaries)
      couplings NonNullFace NullFace where
  plusGravity := data.plusGravity
  minusGravity := data.minusGravity
  plusMetric_eq := data.plusMetric_eq
  minusMetric_eq := data.minusMetric_eq
  plusMaxwell := data.plusMaxwell
  minusMaxwell := data.minusMaxwell
  plusGauge_eq := data.plusGauge_eq
  minusGauge_eq := data.minusGauge_eq
  interactionDensity := data.interactionDensity
  interactionDensity_eq := data.interactionDensity_eq
  boundary :=
    boundaryDataWithGhostAuxiliaryFields period hPeriod data.boundary
      ghosts auxiliaries
  nonNullBoundary := data.nonNullBoundary
  nullActionFaces := data.nullActionFaces
  nullActionGenerator_eq := data.nullActionGenerator_eq
  nullActionInterval_eq := data.nullActionInterval_eq

/-- Ghost and auxiliary coefficients are spectator fields of the exact
assembled Candidate-A action. -/
@[simp]
theorem globalCandidateACovariantAction_withGhostAuxiliaryFields
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data :
      GlobalCandidateAActionData period hPeriod configuration couplings
        NonNullFace NullFace)
    (ghosts :
      SmoothQuotientField period hPeriod GhostFiber ×
        SmoothQuotientField period hPeriod GhostFiber)
    (auxiliaries :
      SmoothQuotientField period hPeriod AuxiliaryFiber ×
        SmoothQuotientField period hPeriod AuxiliaryFiber)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    globalCandidateACovariantAction period hPeriod
        (actionDataWithGhostAuxiliaryFields period hPeriod data
          ghosts auxiliaries)
        measure =
      globalCandidateACovariantAction period hPeriod data measure :=
  rfl

end
end P0EFTJanusProgramPGlobalActionSpectatorSectors4D
end JanusFormal
