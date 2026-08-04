import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNaturalClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBoundaryCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceAction

/-!
# Global covariant Candidate-A action assembly

This file transports every already constructed finite action term to the
single global Program-P configuration.  The regular functional domain ties
both Einstein--Hilbert metrics, both intrinsic abelian potentials, the smooth
Candidate-A interaction density and every boundary stratum to that same
configuration.

The matter block is the genuine primitive monopole SpinC Dirac-plus-mass
action.  Its two outer sectors are sections of the same geometric bundle used
by the signed spectral Dirac operator.
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
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
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

/-- Geometric sources accepted by the unique Candidate-A non-null boundary
summand.  Besides the historical finite control, the canonical latitude
constructor is the exact continuum ledger on the two oriented throat sheets.
No free scalar boundary action is stored. -/
inductive GlobalCandidateANonNullBoundaryDatum
    (period : Real) (hPeriod : period ≠ 0)
    (NonNullFace : Type*) [Fintype NonNullFace] where
  | fixed (faces : NonNullFace → NonNullFaceDatum)
  | canonicalLatitudeTwoSheet
      (faces : Fin 2 → CanonicalLatitudeBase → NonNullFaceDatum)

/-- Evaluation of the unique sourced non-null boundary summand. -/
def globalCandidateANonNullBoundaryAction
    {NonNullFace : Type*} [Fintype NonNullFace]
    (datum : GlobalCandidateANonNullBoundaryDatum period hPeriod NonNullFace) :
    Real :=
  match datum with
  | .fixed faces => totalNonNullGHYCurve faces 0
  | .canonicalLatitudeTwoSheet faces =>
      ∑ sheet : Fin 2, ∫ base, nonNullGHYCurve (faces sheet base) 0
        ∂canonicalLatitudeBaseMeasure period

@[simp]
theorem globalCandidateANonNullBoundaryAction_fixed
    {NonNullFace : Type*} [Fintype NonNullFace]
    (faces : NonNullFace → NonNullFaceDatum) :
    globalCandidateANonNullBoundaryAction period hPeriod
        (.fixed faces) =
      totalNonNullGHYCurve faces 0 :=
  rfl

@[simp]
theorem globalCandidateANonNullBoundaryAction_canonicalLatitudeTwoSheet
    {NonNullFace : Type*} [Fintype NonNullFace]
    (faces : Fin 2 → CanonicalLatitudeBase → NonNullFaceDatum) :
    globalCandidateANonNullBoundaryAction period hPeriod
        (.canonicalLatitudeTwoSheet faces :
          GlobalCandidateANonNullBoundaryDatum period hPeriod NonNullFace) =
      ∑ sheet : Fin 2, ∫ base, nonNullGHYCurve (faces sheet base) 0
        ∂canonicalLatitudeBaseMeasure period :=
  rfl

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
  nonNullBoundary :
    GlobalCandidateANonNullBoundaryDatum period hPeriod NonNullFace
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

/-- Primitive SpinC kinetic action in both physical outer sectors. -/
def globalCandidateAMatterKineticAction
    (configuration : GlobalFieldConfiguration period hPeriod) : Real :=
  programPPrimitiveSpinCMatterSmoothAction
    period hPeriod 0 configuration.spinCMatter

/-- Primitive SpinC mass term with the normalization whose Hessian is
`matterMassSquared`. -/
def globalCandidateAMatterMassAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  (couplings.matterMassSquared / 2) *
    ∑ sector : Sector,
      (d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (configuration.spinCMatter sector)
        (configuration.spinCMatter sector)).re

/-- Complete primitive SpinC matter action on both outer sectors. -/
def globalCandidateAMatterAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  programPPrimitiveSpinCMatterSmoothAction
    period hPeriod couplings.matterMassSquared configuration.spinCMatter

/-- On the whole finite signed SpinC core, the matter summand of the global
Candidate-A action is exactly the independently closed graph action. -/
theorem globalCandidateAMatterAction_finite_eq_graphAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    globalCandidateAMatterAction period hPeriod
        { configuration with
          spinCMatter :=
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis
              period hPeriod coefficients }
        couplings =
      programPPrimitiveSpinCMatterGraphAction
        period hPeriod couplings.matterMassSquared
        (programPPrimitiveSpinCMatterGraphFinite
          period hPeriod couplings.matterMassSquared coefficients) := by
  simpa [globalCandidateAMatterAction] using
    programPPrimitiveSpinCMatterSmoothAction_finite_eq_graphAction
      period hPeriod couplings.matterMassSquared coefficients

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

/-- Exact non-null GHY action selected by its geometric source.  The source
is either the historical fixed finite ledger or the genuine mobile normal
graph; no free scalar boundary action is stored in Candidate A. -/
def globalCandidateAGHYAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Real :=
  globalCandidateANonNullBoundaryAction period hPeriod data.nonNullBoundary

/-- Finite null-face, expansion-counterterm and endpoint-joint action. -/
def globalCandidateANullBoundaryAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Real :=
  ∑ face : NullFace, finiteNullFaceAction (data.nullActionFaces face)

/-- The two density-integrability hypotheses not already carried by the
global oriented-null-face boundary data. -/
structure GlobalCandidateANullBoundaryReparametrizationIntegrability
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Prop where
  inaffinity : ∀ face,
    IntervalIntegrable
      (inaffinityFaceDensity (data.nullActionFaces face))
      MeasureTheory.volume
      (data.nullActionFaces face).interval.initialParameter
      (data.nullActionFaces face).interval.finalParameter
  expansionCounterterm : ∀ face,
    IntervalIntegrable
      (expansionCountertermFaceDensity (data.nullActionFaces face))
      MeasureTheory.volume
      (data.nullActionFaces face).interval.initialParameter
      (data.nullActionFaces face).interval.finalParameter

/-- The global boundary datum supplies the reparametrization-shift
integrability, so the reduced contract completes the existing local one. -/
def GlobalCandidateANullBoundaryReparametrizationIntegrability.toInterval
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace}
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (face : NullFace) :
    NullFaceIntervalIntegrability (data.nullActionFaces face) where
  inaffinity := contract.inaffinity face
  expansionCounterterm := contract.expansionCounterterm face
  reparametrizationShift := by
    rw [data.nullActionGenerator_eq face, data.nullActionInterval_eq face]
    exact (data.boundary.nullFaces face).faceShiftIntervalIntegrable

/-- The same global finite-null-boundary block after rescaling every null
generator. -/
def globalCandidateAReparametrizedNullBoundaryAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : Real :=
  totalReparametrizedFiniteNullBoundaryAction data.nullActionFaces

/-- Exact scoped invariance of the global finite null-face/counterterm/joint
block under generator reparametrization. -/
theorem globalCandidateAReparametrizedNullBoundaryAction_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data) :
    globalCandidateAReparametrizedNullBoundaryAction
        period hPeriod data =
      globalCandidateANullBoundaryAction period hPeriod data := by
  change totalReparametrizedFiniteNullBoundaryAction data.nullActionFaces =
    totalFiniteNullBoundaryAction data.nullActionFaces
  exact totalReparametrizedFiniteNullBoundaryAction_eq
    data.nullActionFaces (contract.toInterval period hPeriod)

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
