import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

/-!
# Fixed-volume Einstein--Hilbert C² families on the paired chart

The paired Lorentz chart transports its frame and keeps each base volume.
This file isolates the matching C² Einstein--Hilbert family.  The remaining
geometric task is the nonzero scalar-curvature identification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D

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
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

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

/-- Einstein--Hilbert density with the base volume held fixed, matching the
transported-frame paired chart. -/
def regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume *
    ((1 / (2 * couplings.gravitationalCoupling)) •
      (regularGeneralMetricC0ScalarCurvature period hPeriod metric variation -
        regularGeneralMetricC0Constant period hPeriod
          (2 * couplings.cosmologicalConstant)))

theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod
        metric couplings)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
  exact contDiffOn_const.mul
    ((regularGeneralMetricC0ScalarCurvature_contDiffOn_two period hPeriod
      metric).sub contDiffOn_const |>.const_smul _)

/-- Integrated fixed-volume Einstein--Hilbert family. -/
def regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  regularGeneralMetricC0IntegralCLM period hPeriod measure
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod
      metric couplings variation)

theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
        metric measure couplings)
      (regularGeneralMetricC2Domain period hPeriod metric) :=
  (regularGeneralMetricC0IntegralCLM period hPeriod measure).contDiff.contDiffOn
    |>.comp
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_contDiffOn_two
        period hPeriod metric couplings)
      (fun _ _ => Set.mem_univ _)

/-- Plus fixed-volume family on the complete paired relative core. -/
def regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) : Real :=
  regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
    plusBase measure couplings core.1.1

/-- Minus fixed-volume family on the complete paired relative core. -/
def regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) : Real :=
  regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod
    minusBase measure couplings core.1.2

theorem regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings)
      (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase) := by
  exact (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two
      period hPeriod plusBase measure couplings).comp
    (contDiff_fst.comp contDiff_fst).contDiffOn
    (fun _ hCore => hCore.1.1.1)

theorem regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings)
      (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase) := by
  exact (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two
      period hPeriod minusBase measure couplings).comp
    (contDiff_snd.comp contDiff_fst).contDiffOn
    (fun _ hCore => hCore.1.2.1)

/-- Plus fixed-volume gravity remains C² after pullback to the actual
minimal-physical tangent. -/
theorem regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_projected_contDiffOn
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
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
          period hPeriod plusBase minusBase measure couplings.plusEinstein
          (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period
        hPeriod configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  exact
    (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.plusEinstein).comp
      (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
      (fun direction hDirection =>
        (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase direction).1
            hDirection)

/-- Minus fixed-volume gravity remains C² after pullback to the actual
minimal-physical tangent. -/
theorem regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_projected_contDiffOn
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
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
          period hPeriod plusBase minusBase measure couplings.minusEinstein
          (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period
        hPeriod configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  exact
    (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.minusEinstein).comp
      (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
      (fun direction hDirection =>
        (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase direction).1
            hDirection)

/-- Both gravity-sector auxiliary actions are C² on the exact paired domain. -/
theorem regular_general_metric_c2_paired_fixed_volume_einstein_hilbert_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (plusCouplings minusCouplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
        (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
          period hPeriod plusBase minusBase measure plusCouplings)
        (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
          plusBase minusBase) ∧
      ContDiffOn Real 2
        (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
          period hPeriod plusBase minusBase measure minusCouplings)
        (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
          plusBase minusBase) := by
  exact ⟨
    regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure plusCouplings,
    regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure minusCouplings⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
end JanusFormal
