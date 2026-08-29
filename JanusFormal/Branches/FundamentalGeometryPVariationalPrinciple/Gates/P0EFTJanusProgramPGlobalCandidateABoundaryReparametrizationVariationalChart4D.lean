import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackSecondVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D

/-!
# Candidate-A boundary-reparametrization variational chart

Independent null-generator normalization parameters are inserted into the
existing global Candidate-A action data.  All physical fields and all other
action blocks stay fixed.  The finite-null action is definitionally unchanged,
so the exact covariant action pullback is constant and its genuine chart
Hessian vanishes.

This covers normalization reparametrizations only, not normal displacement or
general boundary geometry.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff InnerProductSpace
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusFrechetPullbackSecondVariation
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
open P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

universe u

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

/-- Boundary datum with only the normalization function rescaled. -/
def scaledGlobalNullFaceDatum
    (parameter : Real) (face : NullFaceDatum) : NullFaceDatum where
  generator := scaledNullGeneratorReparametrizationData parameter face.generator
  interval := face.interval
  faceShiftIntervalIntegrable := by
    have hScaled := face.faceShiftIntervalIntegrable.const_mul parameter
    change IntervalIntegrable
      (localFaceShift
        (scaledNullGeneratorReparametrizationData parameter face.generator))
      MeasureTheory.volume face.interval.initialParameter
        face.interval.finalParameter
    convert hScaled using 1
    funext point
    exact scaledNullGenerator_localFaceShift
      parameter point face.generator

/-- Existing boundary data along independent face normalizations. -/
def globalCandidateABoundaryReparametrizationBoundaryDataAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace where
  nonNullWeight := data.boundary.nonNullWeight
  nonNullEinsteinScale := data.boundary.nonNullEinsteinScale
  nonNullOrientation := data.boundary.nonNullOrientation
  nonNullDirichletJet := data.boundary.nonNullDirichletJet
  nullFaces := fun face => scaledGlobalNullFaceDatum
    (parameters face) (data.boundary.nullFaces face)
  scalarMassSquared := data.boundary.scalarMassSquared
  scalarField := data.boundary.scalarField
  scalarTest := data.boundary.scalarTest
  scalarControl := data.boundary.scalarControl

/-- Global action data with independently rescaled null normalizations. -/
def globalCandidateABoundaryReparametrizationDataAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    GlobalCandidateAActionData period hPeriod configuration couplings
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
  boundary := globalCandidateABoundaryReparametrizationBoundaryDataAt
    period hPeriod data parameters
  nonNullBoundary := data.nonNullBoundary
  nullActionFaces := fun face => scaledFiniteNullFaceActionDatum
    (parameters face) (data.nullActionFaces face)
  nullActionGenerator_eq := by
    intro face
    change scaledNullGeneratorReparametrizationData (parameters face)
        (data.nullActionFaces face).generator =
      scaledNullGeneratorReparametrizationData (parameters face)
        (data.boundary.nullFaces face).generator
    rw [data.nullActionGenerator_eq face]
  nullActionInterval_eq := by
    intro face
    change (data.nullActionFaces face).interval =
      (data.boundary.nullFaces face).interval
    exact data.nullActionInterval_eq face

/-- The true finite-null block is unchanged on the family. -/
theorem globalCandidateABoundaryReparametrization_nullAction_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateANullBoundaryAction period hPeriod
        (globalCandidateABoundaryReparametrizationDataAt
          period hPeriod data parameters) =
      globalCandidateANullBoundaryAction period hPeriod data := by
  classical
  unfold globalCandidateANullBoundaryAction
    globalCandidateABoundaryReparametrizationDataAt
  apply Finset.sum_congr rfl
  intro face _
  exact finiteNullFaceAction_scaled_eq
    (parameters face) (data.nullActionFaces face)

/-- Exact action family on the finite Euclidean normalization chart. -/
def globalCandidateABoundaryReparametrizationActionFamily
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalCandidateAActionFamily period hPeriod
      (GlobalCandidateABoundaryReparametrizationHilbert NullFace)
      couplings NonNullFace NullFace where
  configurationAt := fun _ => configuration
  dataAt := globalCandidateABoundaryReparametrizationDataAt
    period hPeriod data

@[simp]
theorem globalCandidateABoundaryReparametrizationActionFamily_configurationAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    (globalCandidateABoundaryReparametrizationActionFamily
      period hPeriod data).configurationAt parameters = configuration :=
  rfl

/-- The complete existing covariant action is constant on this family. -/
theorem globalCandidateABoundaryReparametrization_covariantAction_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateACovariantAction period hPeriod
        (globalCandidateABoundaryReparametrizationDataAt
          period hPeriod data parameters) measure =
      globalCandidateACovariantAction period hPeriod data measure := by
  unfold globalCandidateACovariantAction
  rw [globalCandidateABoundaryReparametrization_nullAction_eq]
  rfl

private theorem boundaryReparametrization_candidateABlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).candidateA =
      fun _ => globalCandidateAInteractionAction period hPeriod data measure :=
  rfl

private theorem boundaryReparametrization_matterBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).matter =
      fun _ => globalCandidateAMatterAction
        period hPeriod configuration couplings := by
  funext parameters
  change globalCandidateAMatterAction period hPeriod
      ((globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data).configurationAt parameters) couplings = _
  rw [globalCandidateABoundaryReparametrizationActionFamily_configurationAt]

private theorem boundaryReparametrization_robinBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).robin =
      fun _ => globalCandidateAGHYAction period hPeriod data :=
  rfl

private theorem boundaryReparametrization_llBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).ll =
      fun _ => globalCandidateALLAction period hPeriod data :=
  rfl

private theorem boundaryReparametrization_einsteinHilbertPlusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).einsteinHilbertPlus =
      fun _ => intrinsicEinsteinHilbertAction period hPeriod
        couplings.plusEinstein data.plusGravity measure :=
  rfl

private theorem boundaryReparametrization_einsteinHilbertMinusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).einsteinHilbertMinus =
      fun _ => intrinsicEinsteinHilbertAction period hPeriod
        couplings.minusEinstein data.minusGravity measure :=
  rfl

private theorem boundaryReparametrization_maxwellPlusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).maxwellPlus =
      fun _ => couplings.plusMaxwellScale *
        intrinsicMaxwellAction period hPeriod data.plusGravity.metric
          data.plusMaxwell.basePairing measure :=
  rfl

private theorem boundaryReparametrization_maxwellMinusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).maxwellMinus =
      fun _ => couplings.minusMaxwellScale *
        intrinsicMaxwellAction period hPeriod data.minusGravity.metric
          data.minusMaxwell.basePairing measure :=
  rfl

private theorem boundaryReparametrization_finiteBVBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationActionFamily
        period hPeriod data) measure).finiteBV =
      fun _ => globalCandidateANullBoundaryAction period hPeriod data := by
  funext parameters
  exact globalCandidateABoundaryReparametrization_nullAction_eq
    period hPeriod data parameters

private theorem contDiffAt_of_eq_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : E → Real) (point : E) (constant : Real)
    (h : f = fun _ => constant) :
    ContDiffAt Real 2 f point := by
  rw [h]
  exact contDiffAt_const

/-- Genuine covariant variational chart for null normalization parameters. -/
def globalCandidateABoundaryReparametrizationVariationalChart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure where
  Configuration := GlobalCandidateABoundaryReparametrizationHilbert NullFace
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  family := globalCandidateABoundaryReparametrizationActionFamily
    period hPeriod data
  blocksC2 := fun parameters => by
    constructor
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_candidateABlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_matterBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_robinBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_llBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_einsteinHilbertPlusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_einsteinHilbertMinusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_maxwellPlusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_maxwellMinusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ parameters _
        (boundaryReparametrization_finiteBVBlock_eq_const
          period hPeriod data measure)

/-- The exact action pullback is constant on the normalization chart. -/
theorem globalCandidateABoundaryReparametrization_actionPullback_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    globalCandidateAActionPullback period hPeriod
        (globalCandidateABoundaryReparametrizationVariationalChart
          period hPeriod data measure) =
      fun _ => globalCandidateACovariantAction period hPeriod data measure := by
  funext parameters
  unfold globalCandidateAActionPullback
    globalCandidateABoundaryReparametrizationVariationalChart
    globalCandidateABoundaryReparametrizationActionFamily
  exact globalCandidateABoundaryReparametrization_covariantAction_eq
    period hPeriod data measure parameters

/-- The genuine covariant Hessian vanishes on normalization directions. -/
theorem globalCandidateABoundaryReparametrization_hessian_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateAHessian period hPeriod
        (globalCandidateABoundaryReparametrizationVariationalChart
          period hPeriod data measure) parameters =
      0 := by
  unfold globalCandidateAHessian globalEulerLagrangeOperator actionGradient
  rw [globalCandidateABoundaryReparametrization_actionPullback_eq]
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp
  change (0 : Real) = 0
  rfl

/-! ## Functorial extension of an arbitrary covariant chart -/

/-- Add independent null-normalization parameters to an existing chart while
leaving its physical configuration curve unchanged. -/
def globalCandidateABoundaryReparametrizationExtendActionFamily
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    GlobalCandidateAActionFamily period hPeriod
      (chart.Configuration ×
        GlobalCandidateABoundaryReparametrizationHilbert NullFace)
      couplings NonNullFace NullFace where
  configurationAt := fun state => chart.family.configurationAt state.1
  dataAt := fun state =>
    globalCandidateABoundaryReparametrizationDataAt period hPeriod
      (chart.family.dataAt state.1) state.2

private theorem boundaryReparametrizationExtend_candidateABlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).candidateA =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).candidateA state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_matterBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).matter =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).matter state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_robinBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).robin =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).robin state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_llBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).ll =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).ll state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_einsteinHilbertPlusBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).einsteinHilbertPlus =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).einsteinHilbertPlus state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_einsteinHilbertMinusBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).einsteinHilbertMinus =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).einsteinHilbertMinus state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_maxwellPlusBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).maxwellPlus =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).maxwellPlus state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_maxwellMinusBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).maxwellMinus =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).maxwellMinus state.1 :=
  rfl

private theorem boundaryReparametrizationExtend_finiteBVBlock_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateABoundaryReparametrizationExtendActionFamily
        period hPeriod chart) measure).finiteBV =
      fun state => (globalCandidateAActionBlocks period hPeriod
        chart.family measure).finiteBV state.1 := by
  funext state
  exact globalCandidateABoundaryReparametrization_nullAction_eq
    period hPeriod (chart.family.dataAt state.1) state.2

private theorem contDiffAt_fst_comp
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (function : E → Real) (point : E × F)
    (hFunction : ContDiffAt Real 2 function point.1) :
    ContDiffAt Real 2 (fun state : E × F => function state.1) point :=
  hFunction.comp point
    (ContinuousLinearMap.fst Real E F).contDiff.contDiffAt

/-- Any regular covariant chart extends regularly by independent null
normalizations. -/
def globalCandidateABoundaryReparametrizationExtendVariationalChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure where
  Configuration := chart.Configuration ×
    GlobalCandidateABoundaryReparametrizationHilbert NullFace
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  family := globalCandidateABoundaryReparametrizationExtendActionFamily
    period hPeriod chart
  blocksC2 := fun state => by
    let baseC2 := chart.blocksC2 state.1
    constructor
    · rw [boundaryReparametrizationExtend_candidateABlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.candidateA
    · rw [boundaryReparametrizationExtend_matterBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.matter
    · rw [boundaryReparametrizationExtend_robinBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.robin
    · rw [boundaryReparametrizationExtend_llBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.ll
    · rw [boundaryReparametrizationExtend_einsteinHilbertPlusBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.einsteinHilbertPlus
    · rw [boundaryReparametrizationExtend_einsteinHilbertMinusBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.einsteinHilbertMinus
    · rw [boundaryReparametrizationExtend_maxwellPlusBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.maxwellPlus
    · rw [boundaryReparametrizationExtend_maxwellMinusBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.maxwellMinus
    · rw [boundaryReparametrizationExtend_finiteBVBlock_eq]
      exact contDiffAt_fst_comp _ state baseC2.finiteBV

/-- Extending a chart by null normalizations only precomposes its exact action
with the first projection. -/
theorem globalCandidateABoundaryReparametrizationExtend_actionPullback_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    globalCandidateAActionPullback period hPeriod
        (globalCandidateABoundaryReparametrizationExtendVariationalChart
          period hPeriod chart) =
      fun state => globalCandidateAActionPullback period hPeriod chart state.1 := by
  funext state
  unfold globalCandidateAActionPullback
    globalCandidateABoundaryReparametrizationExtendVariationalChart
    globalCandidateABoundaryReparametrizationExtendActionFamily
  exact globalCandidateABoundaryReparametrization_covariantAction_eq
    period hPeriod (chart.family.dataAt state.1) measure state.2

/-- Continuous projection forgetting the null-normalization parameters. -/
def globalCandidateABoundaryReparametrizationFirstProjection
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (chart.Configuration ×
        GlobalCandidateABoundaryReparametrizationHilbert NullFace) →L[Real]
      chart.Configuration :=
  ContinuousLinearMap.fst Real chart.Configuration
    (GlobalCandidateABoundaryReparametrizationHilbert NullFace)

/-- The extended genuine Hessian is exactly the pullback of the original
Hessian through the first projection. -/
theorem globalCandidateABoundaryReparametrizationExtend_hessian_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (state first second : chart.Configuration ×
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateAHessian period hPeriod
        (globalCandidateABoundaryReparametrizationExtendVariationalChart
          period hPeriod chart) state first second =
      globalCandidateAHessian period hPeriod chart state.1 first.1 second.1 := by
  let projection :=
    globalCandidateABoundaryReparametrizationFirstProjection
      period hPeriod chart
  have hTarget : Differentiable Real
      (globalCandidateAActionPullback period hPeriod chart) :=
    (globalCandidateAActionPullback_contDiff_two
      period hPeriod chart).differentiable (by norm_num)
  have hProjection : Differentiable Real
      (fun input : chart.Configuration ×
          GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
        input.1) := by
    exact projection.differentiable
  have hProjectionFDeriv :
      (fun point : chart.Configuration ×
          GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
        fderiv Real
          (fun input : chart.Configuration ×
              GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
            input.1) point) =
      fun _ => projection := by
    funext point
    change fderiv Real projection point = projection
    exact ContinuousLinearMap.fderiv projection
  have hSecondJet :
      HasFDerivAt
        (fun point : chart.Configuration ×
            GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
          fderiv Real
            (fun input : chart.Configuration ×
                GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
              input.1) point)
        (0 :
          (chart.Configuration ×
              GlobalCandidateABoundaryReparametrizationHilbert NullFace) →L[Real]
            (chart.Configuration ×
              GlobalCandidateABoundaryReparametrizationHilbert NullFace) →L[Real]
              chart.Configuration)
        state := by
    rw [hProjectionFDeriv]
    exact hasFDerivAt_const (x := state) (c := projection)
  have hSecond := pulledBackAction_second_fderiv_apply
    (globalCandidateAActionPullback period hPeriod chart)
    (fun input : chart.Configuration ×
        GlobalCandidateABoundaryReparametrizationHilbert NullFace => input.1)
    hTarget hProjection state
    (0 :
      (chart.Configuration ×
          GlobalCandidateABoundaryReparametrizationHilbert NullFace) →L[Real]
        (chart.Configuration ×
          GlobalCandidateABoundaryReparametrizationHilbert NullFace) →L[Real]
          chart.Configuration)
    (globalCandidateAHessian period hPeriod chart state.1)
    hSecondJet
    (globalCandidateAHessian_hasFDerivAt
      period hPeriod chart state.1)
    first second
  unfold globalCandidateAHessian globalEulerLagrangeOperator actionGradient
  rw [globalCandidateABoundaryReparametrizationExtend_actionPullback_eq]
  change
    fderiv Real
        (fun point => fderiv Real
          (pulledBackAction
            (globalCandidateAActionPullback period hPeriod chart)
            (fun input : chart.Configuration ×
              GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
                input.1)) point)
        state first second = _
  rw [hSecond]
  rw [show fderiv Real
      (fun input : chart.Configuration ×
        GlobalCandidateABoundaryReparametrizationHilbert NullFace => input.1)
      state = projection by
    change fderiv Real projection state = projection
    exact ContinuousLinearMap.fderiv projection]
  change
    globalCandidateAHessian period hPeriod chart state.1 first.1 second.1 +
      fderiv Real (globalCandidateAActionPullback period hPeriod chart)
        state.1 0 = _
  simp
  rfl

/-- Operator form of the functorial Hessian pullback. -/
theorem globalCandidateABoundaryReparametrizationExtend_hessian_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (state : chart.Configuration ×
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateAHessian period hPeriod
        (globalCandidateABoundaryReparametrizationExtendVariationalChart
          period hPeriod chart) state =
      jacobianPullbackHessian
        (globalCandidateABoundaryReparametrizationFirstProjection
          period hPeriod chart)
        (globalCandidateAHessian period hPeriod chart state.1) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  exact globalCandidateABoundaryReparametrizationExtend_hessian_apply
    period hPeriod chart state first second

/-- Every pure normalization direction, and hence every mixed block involving
one, is in the kernel of the extended genuine Hessian. -/
@[simp]
theorem globalCandidateABoundaryReparametrizationExtend_hessian_boundary_right
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (state first : chart.Configuration ×
      GlobalCandidateABoundaryReparametrizationHilbert NullFace)
    (boundaryDirection :
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateAHessian period hPeriod
        (globalCandidateABoundaryReparametrizationExtendVariationalChart
          period hPeriod chart) state first (0, boundaryDirection) = 0 := by
  rw [globalCandidateABoundaryReparametrizationExtend_hessian_apply]
  exact map_zero _

@[simp]
theorem globalCandidateABoundaryReparametrizationExtend_hessian_boundary_left
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (state second : chart.Configuration ×
      GlobalCandidateABoundaryReparametrizationHilbert NullFace)
    (boundaryDirection :
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateAHessian period hPeriod
      (globalCandidateABoundaryReparametrizationExtendVariationalChart
          period hPeriod chart) state (0, boundaryDirection) second = 0 := by
  rw [globalCandidateABoundaryReparametrizationExtend_hessian_apply]
  change globalCandidateAHessian period hPeriod chart state.1
      (0 : chart.Configuration) second.1 = 0
  rw [map_zero]
  rfl

/-! ## Matter chart with null-normalization parameters -/

/-- The already closed matter chart extended by all independent null
normalizations. -/
def globalCandidateAMatterBoundaryReparametrizationVariationalChart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure :=
  globalCandidateABoundaryReparametrizationExtendVariationalChart
    period hPeriod
    (globalCandidateAMatterFiniteGraphVariationalChart
      period hPeriod data measure)

/-- Exact combined pullback: the normalization factor is invisible and the
matter factor retains its closed quadratic action. -/
theorem globalCandidateAMatterBoundaryReparametrization_actionPullback_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    globalCandidateAActionPullback period hPeriod
        (globalCandidateAMatterBoundaryReparametrizationVariationalChart
          period hPeriod data measure) =
      fun state :
          GlobalCandidateAMatterFiniteGraphCore period hPeriod
              couplings.matterMassSquared ×
            GlobalCandidateABoundaryReparametrizationHilbert NullFace =>
        globalCandidateAMatterFiniteGraphPulledAction
          period hPeriod data measure state.1 := by
  unfold globalCandidateAMatterBoundaryReparametrizationVariationalChart
  rw [globalCandidateABoundaryReparametrizationExtend_actionPullback_eq]
  rw [globalCandidateAMatterFiniteGraph_actionPullback_eq]
  rfl

/-- Genuine same-action Hessian on the combined matter/normalization chart;
there are no normalization or mixed contributions. -/
theorem globalCandidateAMatterBoundaryReparametrization_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (state first second :
      GlobalCandidateAMatterFiniteGraphCore period hPeriod
          couplings.matterMassSquared ×
        GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateAHessian period hPeriod
        (globalCandidateAMatterBoundaryReparametrizationVariationalChart
          period hPeriod data measure) state first second =
      programPPrimitiveSpinCMatterGraphForm period hPeriod
        couplings.matterMassSquared
        (globalCandidateAMatterFiniteGraphInclusion period hPeriod
          couplings.matterMassSquared first.1)
        (globalCandidateAMatterFiniteGraphInclusion period hPeriod
          couplings.matterMassSquared second.1) := by
  unfold globalCandidateAMatterBoundaryReparametrizationVariationalChart
  rw [globalCandidateABoundaryReparametrizationExtend_hessian_apply]
  exact globalCandidateAMatterFiniteGraph_sameActionHessian
    period hPeriod data measure state.1 first.1 second.1

end
end P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D
end JanusFormal
