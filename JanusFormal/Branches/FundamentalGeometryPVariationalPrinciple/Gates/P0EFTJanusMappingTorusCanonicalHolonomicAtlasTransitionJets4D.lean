import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold

/-!
# Canonical quotient-atlas transitions and rebased local jets

The actual reflected-sphere quotient atlas is induced by local sections of the
covering projection.  Its transitions are analytic: locally they are genuine
deck transformations.  This gate exposes that exact transition map and its
`contDiffGroupoid` regularity.

`SmoothHolonomicFrameChart4` is still a supplied total coordinate-map/frame
package and is not constructed by the quotient-atlas API.  Moreover raw metric
and scalar coordinate arrays do not agree literally under a nontrivial change
of coordinates.  The equality interface consumed by the existing overlap gate
is therefore valid only after both jets have been rebased into one common
frame.  This gate proves the reflexive, symmetric and transitive laws of those
rebased agreements, propagates them to Levi--Civita/scalar/stress objects, and
packages the exact residual bridge needed by a future global conservation
gate.  No false equality of unre-based coordinate components is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover :=
  MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The genuine quotient chart based at one cover representative. -/
def canonicalQuotientLocalSectionChart
    (anchor : EffectiveCover period hPeriod) :
    OpenPartialHomeomorph (EffectiveQuotient period hPeriod) CoverModel :=
  let hf :=
    (mappingTorusMk_isCoveringMap (sphereData period hPeriod)).isLocalHomeomorph
  (hf.localInverseAt anchor).trans (chartAt CoverModel anchor)

/-- Actual change of coordinates between two local-section charts of the
covering-induced quotient atlas. -/
def canonicalQuotientLocalSectionTransition
    (firstAnchor secondAnchor : EffectiveCover period hPeriod) :
    OpenPartialHomeomorph CoverModel CoverModel :=
  (canonicalQuotientLocalSectionChart
    period hPeriod firstAnchor).symm.trans
      (canonicalQuotientLocalSectionChart period hPeriod secondAnchor)

/-- The raw quotient-atlas transition is analytic.  In particular all first
and second transition jets required by tensorial coordinate laws exist on its
source. -/
theorem canonicalQuotientLocalSectionTransition_mem_contDiffGroupoid
    (firstAnchor secondAnchor : EffectiveCover period hPeriod) :
    canonicalQuotientLocalSectionTransition period hPeriod
        firstAnchor secondAnchor ∈
      contDiffGroupoid ω coverModelWithCorners := by
  exact localSectionChart_transition_mem_groupoid
    coverModelWithCorners ω (sphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)
      firstAnchor secondAnchor

/-- Function-level analytic regularity extracted from the real atlas
transition groupoid certificate. -/
theorem canonicalQuotientLocalSectionTransition_contMDiffOn
    (firstAnchor secondAnchor : EffectiveCover period hPeriod) :
    ContMDiffOn coverModelWithCorners coverModelWithCorners ω
      (canonicalQuotientLocalSectionTransition period hPeriod
        firstAnchor secondAnchor)
      (canonicalQuotientLocalSectionTransition period hPeriod
        firstAnchor secondAnchor).source :=
  contMDiffOn_of_mem_contDiffGroupoid
    (canonicalQuotientLocalSectionTransition_mem_contDiffGroupoid
      period hPeriod firstAnchor secondAnchor)

/-- Reflexive first-jet agreement in one already selected frame. -/
theorem localMetricFirstJetAgreement_refl
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LocalMetricFirstJetAgreement period hPeriod metric
      patch patch coordinate coordinate where
  metricMatrix_eq := rfl
  metricDerivative_eq := rfl

/-- Symmetry of rebased metric first-jet agreement. -/
theorem localMetricFirstJetAgreement_symm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    LocalMetricFirstJetAgreement period hPeriod metric
      secondPatch firstPatch secondCoordinate firstCoordinate where
  metricMatrix_eq := agreement.metricMatrix_eq.symm
  metricDerivative_eq := agreement.metricDerivative_eq.symm

/-- Transitivity of rebased metric first-jet agreement. -/
theorem localMetricFirstJetAgreement_trans
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch thirdPatch :
      SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate thirdCoordinate : Vector4)
    (firstAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (secondAgreement : LocalMetricFirstJetAgreement period hPeriod metric
      secondPatch thirdPatch secondCoordinate thirdCoordinate) :
    LocalMetricFirstJetAgreement period hPeriod metric
      firstPatch thirdPatch firstCoordinate thirdCoordinate where
  metricMatrix_eq :=
    firstAgreement.metricMatrix_eq.trans secondAgreement.metricMatrix_eq
  metricDerivative_eq :=
    firstAgreement.metricDerivative_eq.trans
      secondAgreement.metricDerivative_eq

/-- Reflexive scalar second-jet agreement in one selected frame. -/
theorem localScalarSecondJetAgreement_refl
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LocalScalarSecondJetAgreement period hPeriod field
      patch patch coordinate coordinate where
  field_eq := rfl
  gradient_eq := rfl
  partialGradient_eq := rfl

/-- Symmetry of rebased scalar second-jet agreement. -/
theorem localScalarSecondJetAgreement_symm
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate) :
    LocalScalarSecondJetAgreement period hPeriod field
      secondPatch firstPatch secondCoordinate firstCoordinate where
  field_eq := agreement.field_eq.symm
  gradient_eq := agreement.gradient_eq.symm
  partialGradient_eq := agreement.partialGradient_eq.symm

/-- Transitivity of rebased scalar second-jet agreement. -/
theorem localScalarSecondJetAgreement_trans
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch thirdPatch :
      SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate thirdCoordinate : Vector4)
    (firstAgreement : LocalScalarSecondJetAgreement period hPeriod field
      firstPatch secondPatch firstCoordinate secondCoordinate)
    (secondAgreement : LocalScalarSecondJetAgreement period hPeriod field
      secondPatch thirdPatch secondCoordinate thirdCoordinate) :
    LocalScalarSecondJetAgreement period hPeriod field
      firstPatch thirdPatch firstCoordinate thirdCoordinate where
  field_eq := firstAgreement.field_eq.trans secondAgreement.field_eq
  gradient_eq :=
    firstAgreement.gradient_eq.trans secondAgreement.gradient_eq
  partialGradient_eq :=
    firstAgreement.partialGradient_eq.trans
      secondAgreement.partialGradient_eq

/-- Combined overlap datum after both coordinate jets have been rebased into
one common finite frame. -/
structure RebasedHolonomicTransitionJetAgreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4) : Prop where
  samePoint : firstPatch.coordinateMap firstCoordinate =
    secondPatch.coordinateMap secondCoordinate
  metricFirstJet : LocalMetricFirstJetAgreement period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate
  scalarSecondJet : LocalScalarSecondJetAgreement period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate

/-- Reflexivity of the combined rebased transition datum. -/
theorem rebasedHolonomicTransitionJetAgreement_refl
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    RebasedHolonomicTransitionJetAgreement period hPeriod metric field
      patch patch coordinate coordinate where
  samePoint := rfl
  metricFirstJet :=
    localMetricFirstJetAgreement_refl period hPeriod metric patch coordinate
  scalarSecondJet :=
    localScalarSecondJetAgreement_refl period hPeriod field patch coordinate

/-- The combined rebased transition datum is symmetric. -/
theorem RebasedHolonomicTransitionJetAgreement.symm
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field : SmoothScalarField period hPeriod}
    {firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod}
    {firstCoordinate secondCoordinate : Vector4}
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    RebasedHolonomicTransitionJetAgreement period hPeriod metric field
      secondPatch firstPatch secondCoordinate firstCoordinate where
  samePoint := agreement.samePoint.symm
  metricFirstJet := localMetricFirstJetAgreement_symm period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet
  scalarSecondJet := localScalarSecondJetAgreement_symm period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.scalarSecondJet

/-- The combined rebased transition datum is transitive. -/
theorem RebasedHolonomicTransitionJetAgreement.trans
    {metric : SmoothGeneralLorentzMetric period hPeriod}
    {field : SmoothScalarField period hPeriod}
    {firstPatch secondPatch thirdPatch :
      SmoothHolonomicFrameChart4 period hPeriod}
    {firstCoordinate secondCoordinate thirdCoordinate : Vector4}
    (firstAgreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate)
    (secondAgreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field secondPatch thirdPatch secondCoordinate thirdCoordinate) :
    RebasedHolonomicTransitionJetAgreement period hPeriod metric field
      firstPatch thirdPatch firstCoordinate thirdCoordinate where
  samePoint := firstAgreement.samePoint.trans secondAgreement.samePoint
  metricFirstJet := localMetricFirstJetAgreement_trans period hPeriod metric
    firstPatch secondPatch thirdPatch firstCoordinate secondCoordinate
      thirdCoordinate firstAgreement.metricFirstJet
      secondAgreement.metricFirstJet
  scalarSecondJet := localScalarSecondJetAgreement_trans period hPeriod field
    firstPatch secondPatch thirdPatch firstCoordinate secondCoordinate
      thirdCoordinate firstAgreement.scalarSecondJet
      secondAgreement.scalarSecondJet

/-- Rebased metric first jets give identical local Levi--Civita coefficients
in the selected common frame. -/
theorem localLeviCivitaChristoffel_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localLeviCivitaChristoffel period hPeriod metric firstPatch
        firstCoordinate =
      localLeviCivitaChristoffel period hPeriod metric secondPatch
        secondCoordinate :=
  localLeviCivitaChristoffel_eq_of_firstJetAgreement period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet

/-- Rebased scalar second jets give the same coordinate jet record. -/
theorem localCoordinateScalarJet_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localCoordinateScalarJet period hPeriod field firstPatch firstCoordinate =
      localCoordinateScalarJet period hPeriod field secondPatch
        secondCoordinate :=
  localCoordinateScalarJet_eq_of_secondJetAgreement period hPeriod field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.scalarSecondJet

/-- Metric and scalar rebased jets give the same covariant scalar jet. -/
theorem localCovariantScalarJet_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localCovariantScalarJet period hPeriod metric firstPatch field
        firstCoordinate =
      localCovariantScalarJet period hPeriod metric secondPatch field
        secondCoordinate :=
  localCovariantScalarJet_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet agreement.scalarSecondJet

/-- The scalar Euler residual glues across a rebased transition. -/
theorem localSmoothScalarEulerResidual_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (massSquared source : Real)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarEulerResidual period hPeriod metric firstPatch field
        massSquared source firstCoordinate =
      localSmoothScalarEulerResidual period hPeriod metric secondPatch field
        massSquared source secondCoordinate :=
  localSmoothScalarEulerResidual_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate massSquared source
      agreement.metricFirstJet agreement.scalarSecondJet

/-- The raised scalar gradient glues across a rebased transition. -/
theorem localSmoothScalarRaisedGradient_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarRaisedGradient period hPeriod metric firstPatch field
        firstCoordinate =
      localSmoothScalarRaisedGradient period hPeriod metric secondPatch field
        secondCoordinate :=
  localSmoothScalarRaisedGradient_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate
      agreement.metricFirstJet agreement.scalarSecondJet

/-- Rebased quotient-atlas jets give identical realized stress divergence. -/
theorem localSmoothScalarStressDivergence_eq_of_rebasedTransition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (massSquared source : Real)
    (agreement : RebasedHolonomicTransitionJetAgreement period hPeriod
      metric field firstPatch secondPatch firstCoordinate secondCoordinate) :
    localSmoothScalarStressDivergence period hPeriod metric firstPatch field
        massSquared source firstCoordinate =
      localSmoothScalarStressDivergence period hPeriod metric secondPatch field
        massSquared source secondCoordinate :=
  localSmoothScalarStressDivergence_eq_of_overlap period hPeriod metric field
    firstPatch secondPatch firstCoordinate secondCoordinate massSquared source
      agreement.metricFirstJet agreement.scalarSecondJet

/-- Exact residual contract: selected holonomic patches must realize the
analytic quotient transition jets in a common rebased frame. -/
structure CanonicalRebasedHolonomicAtlasTransitionJetContract
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)) : Prop where
  agreement : ∀
      (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod),
    firstPatch ∈ atlasPatches → secondPatch ∈ atlasPatches →
    ∀ (firstCoordinate secondCoordinate : Vector4),
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        RebasedHolonomicTransitionJetAgreement period hPeriod metric field
          firstPatch secondPatch firstCoordinate secondCoordinate

/-- Patchwise compatibility required by a future global stress-conservation
gluing theorem. -/
def CanonicalAtlasStressDivergenceCompatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod))
    (massSquared source : Real) : Prop :=
  ∀ (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod),
    firstPatch ∈ atlasPatches → secondPatch ∈ atlasPatches →
    ∀ (firstCoordinate secondCoordinate : Vector4),
      firstPatch.coordinateMap firstCoordinate =
          secondPatch.coordinateMap secondCoordinate →
        localSmoothScalarStressDivergence period hPeriod metric firstPatch field
            massSquared source firstCoordinate =
          localSmoothScalarStressDivergence period hPeriod metric secondPatch
            field massSquared source secondCoordinate

/-- The rebased transition-jet contract supplies the exact overlap condition
needed by global stress-divergence gluing. -/
theorem CanonicalRebasedHolonomicAtlasTransitionJetContract.toStressCompatibility
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod))
    (contract : CanonicalRebasedHolonomicAtlasTransitionJetContract
      period hPeriod metric field atlasPatches)
    (massSquared source : Real) :
    CanonicalAtlasStressDivergenceCompatible period hPeriod metric field
      atlasPatches massSquared source := by
  intro firstPatch secondPatch hFirst hSecond
    firstCoordinate secondCoordinate hSamePoint
  exact localSmoothScalarStressDivergence_eq_of_rebasedTransition
    period hPeriod metric field firstPatch secondPatch
      firstCoordinate secondCoordinate massSquared source
      (contract.agreement firstPatch secondPatch hFirst hSecond
        firstCoordinate secondCoordinate hSamePoint)

/-- Minimal downstream bridge for `GlobalScalarStressConservation`: a covering
family of selected holonomic patches together with coherent rebased jets. -/
structure CanonicalHolonomicAtlasStressConservationBridge
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod) where
  atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)
  covers : ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ atlasPatches, ∃ coordinate : Vector4,
      patch.coordinateMap coordinate = point
  transitionJets : CanonicalRebasedHolonomicAtlasTransitionJetContract
    period hPeriod metric field atlasPatches

/-- The downstream bridge immediately provides overlap compatibility of every
realized local stress divergence. -/
theorem CanonicalHolonomicAtlasStressConservationBridge.stressCompatible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field)
    (massSquared source : Real) :
    CanonicalAtlasStressDivergenceCompatible period hPeriod metric field
      bridge.atlasPatches massSquared source :=
  CanonicalRebasedHolonomicAtlasTransitionJetContract.toStressCompatibility
    period hPeriod metric field bridge.atlasPatches bridge.transitionJets
      massSquared source

end

end P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
end JanusFormal
