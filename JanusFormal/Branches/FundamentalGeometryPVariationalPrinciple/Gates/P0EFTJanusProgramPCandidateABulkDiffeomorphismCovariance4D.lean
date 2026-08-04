import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFixedMeasureDiffeomorphismBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMeasureScalarTimeTranslationNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAInteractionDensityNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D

/-!
# Candidate-A bulk-density diffeomorphism covariance

The five measure-dependent Candidate-A blocks are integrals of explicit smooth
scalar densities: the interaction, two Einstein--Hilbert terms, and two
Maxwell terms.  This gate reuses the existing diffeomorphism measure pullback
to turn pointwise pullback identities for those densities into exact
transported-measure covariance.

The GHY block vanishes for the canonical throat.  The three remaining blocks
(SpinC matter, LL, and finite BV boundary data) stay explicit inputs.  No
variational chart, ghost flow, or field-level pullback is manufactured here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateABulkDiffeomorphismCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalMeasureScalarTimeTranslationNoether4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
open P0EFTJanusProgramPFixedMeasureDiffeomorphismBridge4D
open P0EFTJanusProgramPCandidateAInteractionDensityNaturality4D
open P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D
open P0EFTJanusNonlinearGaugeFlowNoether

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

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Change of variables for an arbitrary real integrand against the canonical
measure pullback associated with a smooth self-diffeomorphism. -/
theorem integral_diffeomorphismMeasurePullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (integrand : EffectiveQuotient period hPeriod → Real) :
    (∫ point, integrand (diffeomorphism point)
        ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)) =
      ∫ point, integrand point ∂measure := by
  simpa using
    (diffeomorphismMeasurePullback_measurePreserving period hPeriod
      diffeomorphism measure).integral_comp' integrand

/-- Exact covariance of the Candidate-A interaction block once its genuine
smooth density is identified with the scalar pullback. -/
theorem globalCandidateAInteractionAction_diffeomorphism
    {sourceConfiguration targetConfiguration :
      P0EFTJanusProgramPGlobalFieldSpace4D.GlobalFieldConfiguration
        period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (source :
      GlobalCandidateAActionData period hPeriod sourceConfiguration couplings
        NonNullFace NullFace)
    (target :
      GlobalCandidateAActionData period hPeriod targetConfiguration couplings
        NonNullFace NullFace)
    (hDensity :
      target.interactionDensity =
        pullbackSmoothField period hPeriod Real diffeomorphism
          source.interactionDensity)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    globalCandidateAInteractionAction period hPeriod target
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      globalCandidateAInteractionAction period hPeriod source measure := by
  unfold globalCandidateAInteractionAction
  rw [hDensity]
  change
    (∫ point, source.interactionDensity (diffeomorphism point)
        ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)) =
      ∫ point, source.interactionDensity point ∂measure
  exact integral_diffeomorphismMeasurePullback period hPeriod
    diffeomorphism measure source.interactionDensity

/-- Exact covariance of one Einstein--Hilbert block from pullback identities
for the regular volume and scalar-curvature representatives. -/
theorem intrinsicEinsteinHilbertAction_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (source target : RegularEinsteinHilbertMetric period hPeriod)
    (hVolume :
      target.metric.volume =
        pullbackSmoothField period hPeriod Real diffeomorphism
          source.metric.volume)
    (hScalarCurvature :
      target.scalarCurvature =
        pullbackSmoothField period hPeriod Real diffeomorphism
          source.scalarCurvature)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    intrinsicEinsteinHilbertAction period hPeriod couplings target
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      intrinsicEinsteinHilbertAction period hPeriod couplings source measure := by
  unfold intrinsicEinsteinHilbertAction regularEinsteinHilbertDensityField
  calc
    (∫ point,
        target.metric.volume point *
          ((1 / (2 * couplings.gravitationalCoupling)) *
            (target.scalarCurvature point -
              2 * couplings.cosmologicalConstant))
        ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)) =
        ∫ point,
          source.metric.volume (diffeomorphism point) *
            ((1 / (2 * couplings.gravitationalCoupling)) *
              (source.scalarCurvature (diffeomorphism point) -
                2 * couplings.cosmologicalConstant))
          ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism
            measure) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point => by
        have hVolumePoint := congrArg
          (fun field : SmoothScalarField period hPeriod => field point) hVolume
        have hCurvaturePoint := congrArg
          (fun field : SmoothScalarField period hPeriod => field point)
          hScalarCurvature
        simp only [pullbackSmoothField_apply] at hVolumePoint hCurvaturePoint
        simp only [hVolumePoint, hCurvaturePoint]
    _ = _ := by
      simpa only [regularEinsteinHilbertDensityField] using
        integral_diffeomorphismMeasurePullback period hPeriod
          diffeomorphism measure
            (fun point =>
              source.metric.volume point *
                ((1 / (2 * couplings.gravitationalCoupling)) *
                  (source.scalarCurvature point -
                    2 * couplings.cosmologicalConstant)))

/-- Exact covariance of one Maxwell block from pullback identities for the
regular metric volume and the already constructed Maxwell pairing scalar. -/
theorem intrinsicMaxwellAction_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (sourceMetric targetMetric : RegularGeneralLorentzMetric period hPeriod)
    (sourcePairing targetPairing : SmoothScalarField period hPeriod)
    (hVolume :
      targetMetric.volume =
        pullbackSmoothField period hPeriod Real diffeomorphism
          sourceMetric.volume)
    (hPairing :
      targetPairing =
        pullbackSmoothField period hPeriod Real diffeomorphism sourcePairing)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    intrinsicMaxwellAction period hPeriod targetMetric targetPairing
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      intrinsicMaxwellAction period hPeriod sourceMetric sourcePairing
        measure := by
  unfold intrinsicMaxwellAction
  calc
    (∫ point, targetMetric.volume point *
        (-(1 / 4 : Real) * targetPairing point)
        ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)) =
        ∫ point, sourceMetric.volume (diffeomorphism point) *
          (-(1 / 4 : Real) * sourcePairing (diffeomorphism point))
          ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism
            measure) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point => by
        have hVolumePoint := congrArg
          (fun field : SmoothScalarField period hPeriod => field point) hVolume
        have hPairingPoint := congrArg
          (fun field : SmoothScalarField period hPeriod => field point) hPairing
        simp only [pullbackSmoothField_apply] at hVolumePoint hPairingPoint
        simp only [hVolumePoint, hPairingPoint]
    _ = _ := integral_diffeomorphismMeasurePullback period hPeriod
      diffeomorphism measure
        (fun point =>
          sourceMetric.volume point * (-(1 / 4 : Real) * sourcePairing point))

/-- Field-level pullback identities sufficient for the five
measure-dependent Candidate-A blocks. -/
structure GlobalCandidateABulkDensityDiffeomorphismTransport
    {Transformation : Type*}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (transform : Transformation → chart.Configuration → chart.Configuration)
    (diffeomorphism :
      Transformation → SpacetimeDiffeomorphism period hPeriod) : Prop where
  interactionDensity : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).interactionDensity =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).interactionDensity
  plusVolume : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).plusGravity.metric.volume =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).plusGravity.metric.volume
  plusScalarCurvature : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).plusGravity.scalarCurvature =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).plusGravity.scalarCurvature
  minusVolume : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).minusGravity.metric.volume =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).minusGravity.metric.volume
  minusScalarCurvature : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).minusGravity.scalarCurvature =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).minusGravity.scalarCurvature
  plusMaxwellPairing : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).plusMaxwell.basePairing =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).plusMaxwell.basePairing
  minusMaxwellPairing : ∀ symmetry configuration,
    (chart.family.dataAt
        (transform symmetry configuration)).minusMaxwell.basePairing =
      pullbackSmoothField period hPeriod Real (diffeomorphism symmetry)
        (chart.family.dataAt configuration).minusMaxwell.basePairing

/-- The four non-bulk-density covariance obligations not discharged by the
generic change-of-variables argument. -/
structure GlobalCandidateARemainingDiffeomorphismCovariance
    {Transformation : Type*}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (transform : Transformation → chart.Configuration → chart.Configuration) :
    Prop where
  matter : ∀ symmetry configuration,
    globalCandidateAMatterAction period hPeriod
        (chart.family.configurationAt (transform symmetry configuration))
        couplings =
      globalCandidateAMatterAction period hPeriod
        (chart.family.configurationAt configuration) couplings
  ll : ∀ symmetry configuration,
    globalCandidateALLAction period hPeriod
        (chart.family.dataAt (transform symmetry configuration)) =
      globalCandidateALLAction period hPeriod
        (chart.family.dataAt configuration)
  robin : ∀ symmetry configuration,
    globalCandidateAGHYAction period hPeriod
        (chart.family.dataAt (transform symmetry configuration)) =
      globalCandidateAGHYAction period hPeriod
        (chart.family.dataAt configuration)
  finiteBV : ∀ symmetry configuration,
    globalCandidateANullBoundaryAction period hPeriod
        (chart.family.dataAt (transform symmetry configuration)) =
      globalCandidateANullBoundaryAction period hPeriod
        (chart.family.dataAt configuration)

/-- The seven density pullback identities above and the four remaining block
equalities construct the existing exact nine-block
transported-measure covariance contract. -/
def globalCandidateAActionBlocks_transportedMeasureCovariant
    {Transformation : Type*}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (transform : Transformation → chart.Configuration → chart.Configuration)
    (diffeomorphism :
      Transformation → SpacetimeDiffeomorphism period hPeriod)
    (bulk :
      GlobalCandidateABulkDensityDiffeomorphismTransport period hPeriod chart
        transform diffeomorphism)
    (remaining :
      GlobalCandidateARemainingDiffeomorphismCovariance period hPeriod chart
        transform) :
    FullCoupledTransportedMeasureCovariant period hPeriod
      (fun currentMeasure =>
        globalCandidateAActionBlocks period hPeriod chart.family currentMeasure)
      transform
      (fun symmetry =>
        diffeomorphismMeasurePullback period hPeriod
          (diffeomorphism symmetry) measure)
      measure where
  candidateA := by
    intro symmetry configuration
    exact globalCandidateAInteractionAction_diffeomorphism period hPeriod
      (diffeomorphism symmetry)
      (chart.family.dataAt configuration)
      (chart.family.dataAt (transform symmetry configuration))
      (bulk.interactionDensity symmetry configuration) measure
  matter := remaining.matter
  robin := by
    intro symmetry configuration
    exact remaining.robin symmetry configuration
  ll := remaining.ll
  einsteinHilbertPlus := by
    intro symmetry configuration
    exact intrinsicEinsteinHilbertAction_diffeomorphism period hPeriod
      (diffeomorphism symmetry) couplings.plusEinstein
      (chart.family.dataAt configuration).plusGravity
      (chart.family.dataAt
        (transform symmetry configuration)).plusGravity
      (bulk.plusVolume symmetry configuration)
      (bulk.plusScalarCurvature symmetry configuration) measure
  einsteinHilbertMinus := by
    intro symmetry configuration
    exact intrinsicEinsteinHilbertAction_diffeomorphism period hPeriod
      (diffeomorphism symmetry) couplings.minusEinstein
      (chart.family.dataAt configuration).minusGravity
      (chart.family.dataAt
        (transform symmetry configuration)).minusGravity
      (bulk.minusVolume symmetry configuration)
      (bulk.minusScalarCurvature symmetry configuration) measure
  maxwellPlus := by
    intro symmetry configuration
    apply congrArg (fun value : Real => couplings.plusMaxwellScale * value)
    exact intrinsicMaxwellAction_diffeomorphism period hPeriod
      (diffeomorphism symmetry)
      (chart.family.dataAt configuration).plusGravity.metric
      (chart.family.dataAt
        (transform symmetry configuration)).plusGravity.metric
      (chart.family.dataAt configuration).plusMaxwell.basePairing
      (chart.family.dataAt
        (transform symmetry configuration)).plusMaxwell.basePairing
      (bulk.plusVolume symmetry configuration)
      (bulk.plusMaxwellPairing symmetry configuration) measure
  maxwellMinus := by
    intro symmetry configuration
    apply congrArg (fun value : Real => couplings.minusMaxwellScale * value)
    exact intrinsicMaxwellAction_diffeomorphism period hPeriod
      (diffeomorphism symmetry)
      (chart.family.dataAt configuration).minusGravity.metric
      (chart.family.dataAt
        (transform symmetry configuration)).minusGravity.metric
      (chart.family.dataAt configuration).minusMaxwell.basePairing
      (chart.family.dataAt
        (transform symmetry configuration)).minusMaxwell.basePairing
      (bulk.minusVolume symmetry configuration)
      (bulk.minusMaxwellPairing symmetry configuration) measure
  finiteBV := remaining.finiteBV

/-- Fixed-measure nonlinear Candidate-A symmetry obtained from the bulk
transport bridge, the three remaining blocks, and exact measure preservation.
The supplied chart flow is not claimed to have been constructed here. -/
def globalCandidateADiffeomorphismFlowSymmetry_of_bulkDensityTransport
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (flow :
      CInfinityDiffeomorphismGhost period hPeriod →
        CompleteGaugeFlow chart.Configuration)
    (diffeomorphism :
      CInfinityDiffeomorphismGhost period hPeriod → Real →
        SpacetimeDiffeomorphism period hPeriod)
    (bulk : ∀ ghost,
      GlobalCandidateABulkDensityDiffeomorphismTransport period hPeriod chart
        (flow ghost).flow (diffeomorphism ghost))
    (remaining : ∀ ghost,
      GlobalCandidateARemainingDiffeomorphismCovariance period hPeriod chart
        (flow ghost).flow)
    (hMeasure : ∀ ghost parameter,
      MeasurePreserving
        (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
          (diffeomorphism ghost parameter)) measure measure) :
    GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart :=
  globalCandidateATransportedMeasureCovariance_toFlowSymmetry period hPeriod
    chart flow
    (fun ghost parameter =>
      diffeomorphismMeasurePullback period hPeriod
        (diffeomorphism ghost parameter) measure)
    (fun ghost =>
      globalCandidateAActionBlocks_transportedMeasureCovariant period hPeriod
        chart (flow ghost).flow (diffeomorphism ghost) (bulk ghost)
          (remaining ghost))
    (fun ghost parameter =>
      diffeomorphismMeasurePullback_eq_self_of_measurePreserving
        period hPeriod (diffeomorphism ghost parameter) measure
          (hMeasure ghost parameter))

/-- The installed time-translation diffeomorphisms and canonical
Lorentz measure remove the measure hypothesis from the five-block reduction.
The chart transform and the three residual block covariances remain supplied. -/
def globalCandidateAActionBlocks_timeTranslationInvariant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
    (transform : Real → chart.Configuration → chart.Configuration)
    (bulk :
      GlobalCandidateABulkDensityDiffeomorphismTransport period hPeriod chart
        transform (effectiveTimeFlowDiffeomorph period hPeriod))
    (remaining :
      GlobalCandidateARemainingDiffeomorphismCovariance period hPeriod chart
        transform) :
    FullCoupledInvariantUnder
      (globalCandidateAActionBlocks period hPeriod chart.family
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
      transform :=
  (globalCandidateAActionBlocks_transportedMeasureCovariant period hPeriod
    chart transform (effectiveTimeFlowDiffeomorph period hPeriod) bulk remaining)
      |>.toFixedMeasureInvariant period hPeriod
        (intrinsicCanonicalLorentzVolumeMeasure_timeDiffeomorphism_pullback
          period hPeriod)

/-- Exact Candidate-A action invariance along a supplied complete chart flow
whose five bulk densities are the pullbacks by the installed nontrivial time
flow and whose three residual blocks are invariant. -/
theorem globalCandidateAAction_timeTranslationFlow_invariant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
    (flow : CompleteGaugeFlow chart.Configuration)
    (bulk :
      GlobalCandidateABulkDensityDiffeomorphismTransport period hPeriod chart
        flow.flow (effectiveTimeFlowDiffeomorph period hPeriod))
    (remaining :
      GlobalCandidateARemainingDiffeomorphismCovariance period hPeriod chart
        flow.flow) :
    FlowGaugeInvariant flow
      (globalCandidateAActionPullback period hPeriod chart) := by
  intro configuration parameter
  rw [globalCandidateAActionPullback_eq_blocks period hPeriod chart]
  exact fullCoupledAction_invariant
    (globalCandidateAActionBlocks period hPeriod chart.family
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
    flow.flow
    (globalCandidateAActionBlocks_timeTranslationInvariant period hPeriod
      chart flow.flow bulk remaining)
    parameter configuration

end
end P0EFTJanusProgramPCandidateABulkDiffeomorphismCovariance4D
end JanusFormal
