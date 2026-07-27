import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNaturalClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBoundaryCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorMassAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledDiracAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceAction

/-!
# Global covariant Candidate-A action assembly

This file transports every already constructed finite action term to the
single global Program-P configuration.  The regular functional domain ties
both Einstein--Hilbert metrics, both intrinsic abelian potentials, the smooth
Candidate-A interaction density and every boundary stratum to that same
configuration.

The matter block is the genuine canonically measured doubled D9 SpinC
Dirac-plus-mass action.  Its two halves are the chosen and opposite normal
roots carried by the same global configuration.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCovariantAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped BigOperators Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusProgramPD9MatterSpinorMassAction4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledDiracAction4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Couplings of the globally assembled finite action. -/
structure GlobalCandidateAActionCouplings where
  plusEinstein : EinsteinHilbertCouplings
  minusEinstein : EinsteinHilbertCouplings
  interactionScale : Real
  interactionCoefficients : PotentialCoefficients
  matterMassSquared : Real
  plusMaxwellScale : Real
  minusMaxwellScale : Real

/-- Basis supplied by the smooth regular metric frame at one quotient point. -/
def regularMetricBasisAt
  (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point) :=
  (Pi.basisFun Real (Fin 4)).map
    (metric.frameEquiv point).toLinearEquiv

/-- Maximal regular domain on which all currently geometric action summands
are finite expressions attached to one global configuration. -/
structure GlobalCandidateAActionData
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] where
  plusGravity : RegularEinsteinHilbertMetric period hPeriod
  minusGravity : RegularEinsteinHilbertMetric period hPeriod
  plusMetric_eq :
    plusGravity.metric.metric = configuration.geometry.plusMetric
  minusMetric_eq :
    minusGravity.metric.metric = configuration.geometry.minusMetric
  plusMaxwell :
    RegularIntrinsicMaxwellLine period hPeriod plusGravity.metric
  minusMaxwell :
    RegularIntrinsicMaxwellLine period hPeriod minusGravity.metric
  plusGauge_eq : ∀ point index component,
    plusMaxwell.potential.toFun component point
        (plusGravity.metric.frame index point) =
      configuration.coefficientFields.gauge.1 point (index, component)
  minusGauge_eq : ∀ point index component,
    minusMaxwell.potential.toFun component point
        (minusGravity.metric.frame index point) =
      configuration.coefficientFields.gauge.2 point (index, component)
  interactionDensity : SmoothScalarField period hPeriod
  interactionDensity_eq : ∀ point,
    interactionDensity point =
      configuration.geometry.interactionDensityAt period hPeriod
        couplings.interactionScale couplings.interactionCoefficients point
        (regularMetricBasisAt period hPeriod plusGravity.metric point)
  boundary :
    GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace
  nullActionFaces : NullFace → FiniteNullFaceActionDatum
  nullActionGenerator_eq : ∀ face,
    (nullActionFaces face).generator = (boundary.nullFaces face).generator
  nullActionInterval_eq : ∀ face,
    (nullActionFaces face).interval = (boundary.nullFaces face).interval

/-- Two intrinsic Einstein--Hilbert bulk terms. -/
def globalCandidateAEinsteinHilbertAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  intrinsicEinsteinHilbertAction period hPeriod couplings.plusEinstein
      data.plusGravity measure +
    intrinsicEinsteinHilbertAction period hPeriod couplings.minusEinstein
      data.minusGravity measure

/-- Smooth intrinsic Candidate-A interaction integral. -/
def globalCandidateAInteractionAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, data.interactionDensity point ∂measure

/-- The selected physical sector as one chosen/opposite-root doubled field. -/
def globalDoubledSpinorialMatter
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod
      configuration.normalRootChoice where
  first := selectSector sector configuration.spinorialMatter
  second := selectSector sector configuration.spinorialMatterOpposite

/-- Canonically measured doubled SpinC kinetic action in both sectors. -/
def globalCandidateAMatterKineticAction
    (configuration : GlobalFieldConfiguration period hPeriod) : Real :=
  d9DoubledMatterDiracAction period hPeriod
      configuration.normalRootChoice
      (globalDoubledSpinorialMatter period hPeriod configuration .plus) +
    d9DoubledMatterDiracAction period hPeriod
      configuration.normalRootChoice
      (globalDoubledSpinorialMatter period hPeriod configuration .minus)

/-- Canonically measured SpinC mass action for both roots and sectors. -/
def globalCandidateAMatterMassAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  d9SpinorialMatterMassAction period hPeriod
      configuration.normalRootChoice couplings.matterMassSquared
      configuration.spinorialMatter .plus +
    d9SpinorialMatterMassAction period hPeriod
      configuration.normalRootChoice couplings.matterMassSquared
      configuration.spinorialMatter .minus +
    d9SpinorialMatterMassAction period hPeriod
      (oppositeRoot configuration.normalRootChoice)
      couplings.matterMassSquared
      configuration.spinorialMatterOpposite .plus +
    d9SpinorialMatterMassAction period hPeriod
      (oppositeRoot configuration.normalRootChoice)
      couplings.matterMassSquared
      configuration.spinorialMatterOpposite .minus

/-- Complete doubled SpinC matter action. -/
def globalCandidateAMatterAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  globalCandidateAMatterKineticAction period hPeriod configuration +
    globalCandidateAMatterMassAction period hPeriod configuration couplings

/-- Both intrinsic Maxwell terms, with independent overall normalizations. -/
def globalCandidateAMaxwellAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  couplings.plusMaxwellScale *
      intrinsicMaxwellAction period hPeriod data.plusGravity.metric
        data.plusMaxwell.basePairing measure +
    couplings.minusMaxwellScale *
      intrinsicMaxwellAction period hPeriod data.minusGravity.metric
        data.minusMaxwell.basePairing measure

/-- Genuine PT-symmetric LL action on the canonical throat. -/
def globalCandidateALLAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Real :=
  globalPTSymmetricDifferentialLLAction period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Exact non-null GHY action on the supplied finite face family. -/
def globalCandidateAGHYAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Real :=
  totalNonNullGHYCurve data.boundary.nonNullFaces 0

/-- Finite null-face, expansion-counterterm and endpoint-joint action. -/
def globalCandidateANullBoundaryAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Real :=
  ∑ face : NullFace, finiteNullFaceAction (data.nullActionFaces face)

/-- Sum of every currently constructed covariant Candidate-A action block. -/
def globalCandidateACovariantAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  globalCandidateAEinsteinHilbertAction period hPeriod data measure +
    globalCandidateAInteractionAction period hPeriod data measure +
    globalCandidateAMatterAction period hPeriod configuration couplings +
    globalCandidateAMaxwellAction period hPeriod data measure +
    globalCandidateALLAction period hPeriod data +
    globalCandidateAGHYAction period hPeriod data +
    globalCandidateANullBoundaryAction period hPeriod data

/-- The smooth interaction representative is integrable for every finite
measure on the compact quotient. -/
theorem globalCandidateAInteractionDensity_integrable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable data.interactionDensity measure :=
  data.interactionDensity.contMDiff_toFun.continuous
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Exact decomposition and common-configuration attachment of the assembled
action.  Boundary cancellation is a theorem on the same data, not an action
or stationarity assumption. -/
theorem global_covariant_action_assembly_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) :
    globalCandidateACovariantAction period hPeriod data measure =
        globalCandidateAEinsteinHilbertAction period hPeriod data measure +
          globalCandidateAInteractionAction period hPeriod data measure +
          globalCandidateAMatterAction period hPeriod
            configuration couplings +
          globalCandidateAMaxwellAction period hPeriod data measure +
          globalCandidateALLAction period hPeriod data +
          globalCandidateAGHYAction period hPeriod data +
          globalCandidateANullBoundaryAction period hPeriod data ∧
      data.plusGravity.metric.metric = configuration.geometry.plusMetric ∧
      data.minusGravity.metric.metric = configuration.geometry.minusMetric ∧
      data.boundary.totalResidual period hPeriod llDirection = 0 := by
  exact ⟨rfl, data.plusMetric_eq, data.minusMetric_eq,
    data.boundary.totalResidual_eq_zero period hPeriod llDirection⟩

end
end P0EFTJanusProgramPGlobalCovariantAction4D
end JanusFormal
