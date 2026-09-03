import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D

/-!
# Exact Einstein--Hilbert blocks on the paired smooth chart

The intrinsic scalar-curvature bridge identifies both fixed-volume completed
families with the genuine plus/minus Einstein--Hilbert action blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The fixed-volume completed density of a smooth chart variation is the
genuine Einstein--Hilbert density of the reconstructed regular metric. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod
        metric couplings
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularEinsteinHilbertDensityField period hPeriod couplings
          (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
            period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
                metric tensor hLorentz))) := by
  let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    metric tensor hLorentz
  have hVaried : varied.metric.tensor = metric.metric.tensor + tensor := by
    exact regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric
      tensor hLorentz
  have hScalar :
      regularGeneralMetricC0ScalarCurvature period hPeriod metric
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) =
        smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (globalSmoothScalarCurvature period hPeriod varied.metric) := by
    simpa only [regularGeneralMetricSmoothC2Variation] using
      (regularGeneralMetricC0ScalarCurvature_smooth period hPeriod metric tensor
        varied.metric hVaried hLorentz.1)
  unfold regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
  rw [hScalar]
  apply ContinuousMap.ext
  intro point
  rfl

/-- Integration upgrades the smooth density identification to the genuine
Einstein--Hilbert action. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
        metric measure couplings
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) =
      intrinsicEinsteinHilbertAction period hPeriod couplings
        (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
          period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              metric tensor hLorentz))
        measure := by
  unfold regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
  rw [regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_smooth period
      hPeriod metric tensor hLorentz couplings,
    regularGeneralMetricC0IntegralCLM_apply period hPeriod measure]
  rfl

/-- On the exact paired domain the genuine plus Einstein--Hilbert block is
the pullback of the completed fixed-volume action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure).einsteinHilbertPlus direction =
      regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings.plusEinstein
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change intrinsicEinsteinHilbertAction period hPeriod couplings.plusEinstein
      (family.datumAtTotal period hPeriod 0 hZero direction).2.plusGravity
        measure = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  change intrinsicEinsteinHilbertAction period hPeriod couplings.plusEinstein
      (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
        period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            plusBase
              (direction.1.completeVariation.fullMetricPerturbation .plus)
              hDirection.plus_mem)) measure =
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
      plusBase measure couplings.plusEinstein
        (regularGeneralMetricSmoothC2Variation period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus))
  exact (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_smooth
    period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus)
      hDirection.plus_mem measure couplings.plusEinstein).symm

/-- On the exact paired domain the genuine minus Einstein--Hilbert block is
the pullback of the completed fixed-volume action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure).einsteinHilbertMinus direction =
      regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings.minusEinstein
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change intrinsicEinsteinHilbertAction period hPeriod couplings.minusEinstein
      (family.datumAtTotal period hPeriod 0 hZero direction).2.minusGravity
        measure = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  change intrinsicEinsteinHilbertAction period hPeriod couplings.minusEinstein
      (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
        period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            minusBase
              (direction.1.completeVariation.fullMetricPerturbation .minus)
              hDirection.minus_mem)) measure =
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
      minusBase measure couplings.minusEinstein
        (regularGeneralMetricSmoothC2Variation period hPeriod minusBase
          (direction.1.completeVariation.fullMetricPerturbation .minus))
  exact (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_smooth
    period hPeriod minusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus)
      hDirection.minus_mem measure couplings.minusEinstein).symm

/-- The genuine plus Einstein--Hilbert block is C² within the exact paired
minimal-physical domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).einsteinHilbertPlus
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  have hAux : ContDiffWithinAt Real 2
      (fun direction =>
        regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
          period hPeriod plusBase minusBase measure couplings.plusEinstein
          (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_projected_contDiffOn
      period hPeriod configuration data analysis realization plusBase minusBase
        measure).contDiffWithinAt hPoint
  exact hAux.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection)
    hPoint

/-- The genuine minus Einstein--Hilbert block is C² within the exact paired
minimal-physical domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).einsteinHilbertMinus
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  have hAux : ContDiffWithinAt Real 2
      (fun direction =>
        regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
          period hPeriod plusBase minusBase measure couplings.minusEinstein
          (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_projected_contDiffOn
      period hPeriod configuration data analysis realization plusBase minusBase
        measure).contDiffWithinAt hPoint
  exact hAux.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection)
    hPoint

/-- Gate marker: both genuine Einstein--Hilbert members of the five variable
physical blocks are discharged exactly. -/
theorem regular_general_metric_c2_paired_minimal_physical_einstein_hilbert_c2_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).einsteinHilbertPlus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point ∧
      ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).einsteinHilbertMinus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point := by
  exact ⟨
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint,
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D
end JanusFormal
