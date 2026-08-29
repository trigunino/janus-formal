import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D

/-!
# Transported-measure to fixed-measure diffeomorphism bridge

Existing geometric covariance theorems naturally pull back the measure,
whereas the Candidate-A variational chart fixes one measure.  This gate
isolates the exact conversion: transported covariance of all nine blocks
becomes fixed-measure invariance whenever the transported measure is equal to
the chart measure.

The scalar-action corollary instantiates this conversion for an arbitrary
measure-preserving smooth self-diffeomorphism.  No Candidate-A nine-block
covariance or chart flow is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFixedMeasureDiffeomorphismBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
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

/-- Covariance of nine scalar action blocks when the configuration and the
integration measure are transported simultaneously. -/
structure FullCoupledTransportedMeasureCovariant
    {Configuration Transformation : Type*}
    (blocks :
      Measure (EffectiveQuotient period hPeriod) →
        FullCoupledActionBlocks Configuration)
    (transform : Transformation → Configuration → Configuration)
    (transportedMeasure :
      Transformation → Measure (EffectiveQuotient period hPeriod))
    (baseMeasure : Measure (EffectiveQuotient period hPeriod)) : Prop where
  candidateA : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).candidateA
        (transform symmetry configuration) =
      (blocks baseMeasure).candidateA configuration
  matter : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).matter
        (transform symmetry configuration) =
      (blocks baseMeasure).matter configuration
  robin : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).robin
        (transform symmetry configuration) =
      (blocks baseMeasure).robin configuration
  ll : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).ll
        (transform symmetry configuration) =
      (blocks baseMeasure).ll configuration
  einsteinHilbertPlus : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).einsteinHilbertPlus
        (transform symmetry configuration) =
      (blocks baseMeasure).einsteinHilbertPlus configuration
  einsteinHilbertMinus : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).einsteinHilbertMinus
        (transform symmetry configuration) =
      (blocks baseMeasure).einsteinHilbertMinus configuration
  maxwellPlus : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).maxwellPlus
        (transform symmetry configuration) =
      (blocks baseMeasure).maxwellPlus configuration
  maxwellMinus : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).maxwellMinus
        (transform symmetry configuration) =
      (blocks baseMeasure).maxwellMinus configuration
  finiteBV : ∀ symmetry configuration,
    (blocks (transportedMeasure symmetry)).finiteBV
        (transform symmetry configuration) =
      (blocks baseMeasure).finiteBV configuration

/-- If the transported measure is the fixed chart measure, transported
covariance is exactly the existing nine-block invariance contract. -/
def FullCoupledTransportedMeasureCovariant.toFixedMeasureInvariant
    {Configuration Transformation : Type*}
    {blocks :
      Measure (EffectiveQuotient period hPeriod) →
        FullCoupledActionBlocks Configuration}
    {transform : Transformation → Configuration → Configuration}
    {transportedMeasure :
      Transformation → Measure (EffectiveQuotient period hPeriod)}
    {baseMeasure : Measure (EffectiveQuotient period hPeriod)}
    (covariance :
      FullCoupledTransportedMeasureCovariant period hPeriod blocks transform
        transportedMeasure baseMeasure)
    (hFixed : ∀ symmetry, transportedMeasure symmetry = baseMeasure) :
    FullCoupledInvariantUnder (blocks baseMeasure) transform where
  candidateA := by
    intro symmetry configuration
    simpa [hFixed symmetry] using covariance.candidateA symmetry configuration
  matter := by
    intro symmetry configuration
    simpa [hFixed symmetry] using covariance.matter symmetry configuration
  robin := by
    intro symmetry configuration
    simpa [hFixed symmetry] using covariance.robin symmetry configuration
  ll := by
    intro symmetry configuration
    simpa [hFixed symmetry] using covariance.ll symmetry configuration
  einsteinHilbertPlus := by
    intro symmetry configuration
    simpa [hFixed symmetry] using
      covariance.einsteinHilbertPlus symmetry configuration
  einsteinHilbertMinus := by
    intro symmetry configuration
    simpa [hFixed symmetry] using
      covariance.einsteinHilbertMinus symmetry configuration
  maxwellPlus := by
    intro symmetry configuration
    simpa [hFixed symmetry] using
      covariance.maxwellPlus symmetry configuration
  maxwellMinus := by
    intro symmetry configuration
    simpa [hFixed symmetry] using
      covariance.maxwellMinus symmetry configuration
  finiteBV := by
    intro symmetry configuration
    simpa [hFixed symmetry] using covariance.finiteBV symmetry configuration

/-- Candidate-A specialization of the generic measure bridge.  This converts
transported-measure covariance into the existing fixed-measure flow symmetry;
it does not identify the supplied chart flow with geometric pullback. -/
def globalCandidateATransportedMeasureCovariance_toFlowSymmetry
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (flow :
      CInfinityDiffeomorphismGhost period hPeriod →
        CompleteGaugeFlow chart.Configuration)
    (transportedMeasure :
      CInfinityDiffeomorphismGhost period hPeriod → Real →
        Measure (EffectiveQuotient period hPeriod))
    (covariance : ∀ ghost,
      FullCoupledTransportedMeasureCovariant period hPeriod
        (fun currentMeasure =>
          globalCandidateAActionBlocks period hPeriod chart.family
            currentMeasure)
        (flow ghost).flow (transportedMeasure ghost) measure)
    (hFixed : ∀ ghost parameter,
      transportedMeasure ghost parameter = measure) :
    GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart where
  flow := flow
  blocksInvariant := fun ghost =>
    (covariance ghost).toFixedMeasureInvariant period hPeriod (hFixed ghost)

/-- A measure-preserving self-diffeomorphism has trivial measure pullback. -/
theorem diffeomorphismMeasurePullback_eq_self_of_measurePreserving
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hMeasure :
      MeasurePreserving
        (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
          diffeomorphism) measure measure) :
    diffeomorphismMeasurePullback period hPeriod diffeomorphism measure =
      measure := by
  unfold diffeomorphismMeasurePullback
  exact
    (MeasurePreserving.symm
      (spacetimeDiffeomorphismMeasurableEquiv period hPeriod diffeomorphism)
      hMeasure).map_eq

/-- Fixed-measure version of the existing transported-measure scalar-action
covariance theorem. -/
theorem measuredGeneralLorentzHolonomicScalarAction_diffeomorphism_fixedMeasure
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (pullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      diffeomorphism metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (hMeasure :
      MeasurePreserving
        (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
          diffeomorphism) measure measure) :
    measuredGeneralLorentzHolonomicScalarAction period hPeriod
        pullback.pulledMetric massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame) measure =
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure := by
  have hCovariance :=
    measuredGeneralLorentzHolonomicScalarAction_diffeomorphism
      period hPeriod diffeomorphism metric pullback massSquared field frame
      measure
  rw [diffeomorphismMeasurePullback_eq_self_of_measurePreserving
    period hPeriod diffeomorphism measure hMeasure] at hCovariance
  exact hCovariance

end
end P0EFTJanusProgramPFixedMeasureDiffeomorphismBridge4D
end JanusFormal
