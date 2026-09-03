import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D

/-! # Exact Maxwell blocks on the paired smooth chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGravity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartTargetLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev GaugeC2Core :=
  RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

/-- The paired domain constrains both metric sectors and leaves gauge packets free. -/
def regularGeneralMetricC2PairedMetricGaugeMaxwellDomain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase) :=
  regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
      plusBase minusBase ×ˢ Set.univ

/-- Plus-sector input: native metric core and translated moving-frame gauge data. -/
def regularGeneralMetricC2PairedPlusGaugeCoefficientInput
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase) :
    RegularGeneralMetricC2Core period hPeriod plusBase ×
      GaugeC2Core period hPeriod :=
  (core.1.1.1,
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        configuration.coefficientFields.gauge.1 + core.2.1)

/-- Minus-sector input: native metric core and translated moving-frame gauge data. -/
def regularGeneralMetricC2PairedMinusGaugeCoefficientInput
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase) :
    RegularGeneralMetricC2Core period hPeriod minusBase ×
      GaugeC2Core period hPeriod :=
  (core.1.1.2,
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        configuration.coefficientFields.gauge.2 + core.2.2)

@[simp]
theorem regularGeneralMetricC2PairedPlusGaugeCoefficientInput_projected
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    regularGeneralMetricC2PairedPlusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) =
      (regularGeneralMetricSmoothC2Variation period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus),
        smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (configuration.coefficientFields.gauge.1 +
            direction.1.completeVariation.independent.gauge.1)) := by
  apply Prod.ext
  · rfl
  · exact ((smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_add
      configuration.coefficientFields.gauge.1
        direction.1.completeVariation.independent.gauge.1).symm

@[simp]
theorem regularGeneralMetricC2PairedMinusGaugeCoefficientInput_projected
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    regularGeneralMetricC2PairedMinusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) =
      (regularGeneralMetricSmoothC2Variation period hPeriod minusBase
          (direction.1.completeVariation.fullMetricPerturbation .minus),
        smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (configuration.coefficientFields.gauge.2 +
            direction.1.completeVariation.independent.gauge.2)) := by
  apply Prod.ext
  · rfl
  · exact ((smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_add
      configuration.coefficientFields.gauge.2
        direction.1.completeVariation.independent.gauge.2).symm

theorem regularGeneralMetricC2PairedPlusGaugeCoefficientInput_contDiffOn_two
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedPlusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  have hMetric : ContDiff Real 2
      (fun core : RegularGeneralMetricC2PairedMetricGaugeCore
          period hPeriod plusBase minusBase => core.1.1.1) :=
    contDiff_fst.comp (contDiff_fst.comp contDiff_fst)
  have hGauge : ContDiff Real 2
      (fun core : RegularGeneralMetricC2PairedMetricGaugeCore
          period hPeriod plusBase minusBase =>
        smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            configuration.coefficientFields.gauge.1 + core.2.1) :=
    contDiff_const.add (contDiff_fst.comp contDiff_snd)
  exact hMetric.contDiffOn.prodMk hGauge.contDiffOn

theorem regularGeneralMetricC2PairedMinusGaugeCoefficientInput_contDiffOn_two
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedMinusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  have hMetric : ContDiff Real 2
      (fun core : RegularGeneralMetricC2PairedMetricGaugeCore
          period hPeriod plusBase minusBase => core.1.1.2) :=
    contDiff_snd.comp (contDiff_fst.comp contDiff_fst)
  have hGauge : ContDiff Real 2
      (fun core : RegularGeneralMetricC2PairedMetricGaugeCore
          period hPeriod plusBase minusBase =>
        smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            configuration.coefficientFields.gauge.2 + core.2.2) :=
    contDiff_const.add (contDiff_snd.comp contDiff_snd)
  exact hMetric.contDiffOn.prodMk hGauge.contDiffOn

theorem regularGeneralMetricC2PairedPlusGaugeCoefficientInput_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    {core : RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase}
    (hCore : core ∈ regularGeneralMetricC2PairedMetricGaugeMaxwellDomain
      period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedPlusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase core ∈
      regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod
        plusBase :=
  ⟨hCore.1.1.1, Set.mem_univ _⟩

theorem regularGeneralMetricC2PairedMinusGaugeCoefficientInput_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    {core : RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase}
    (hCore : core ∈ regularGeneralMetricC2PairedMetricGaugeMaxwellDomain
      period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedMinusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase core ∈
      regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod
        minusBase :=
  ⟨hCore.1.1.2, Set.mem_univ _⟩

/-- Plus fixed-volume Maxwell action on the joint paired core. -/
def regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (core : RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase) : Real :=
  regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
    period hPeriod plusBase measure
      (regularGeneralMetricC2PairedPlusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase core).1
      (regularGeneralMetricC2PairedPlusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase core).2

/-- Minus fixed-volume Maxwell action on the joint paired core. -/
def regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (core : RegularGeneralMetricC2PairedMetricGaugeCore
      period hPeriod plusBase minusBase) : Real :=
  regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
    period hPeriod minusBase measure
      (regularGeneralMetricC2PairedMinusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase core).1
      (regularGeneralMetricC2PairedMinusGaugeCoefficientInput period hPeriod
        configuration plusBase minusBase core).2

theorem regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_contDiffOn_two
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
        period hPeriod configuration plusBase minusBase measure)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  exact
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod plusBase measure).comp
        (regularGeneralMetricC2PairedPlusGaugeCoefficientInput_contDiffOn_two
          period hPeriod configuration plusBase minusBase)
        (fun _ hCore => regularGeneralMetricC2PairedPlusGaugeCoefficientInput_mem
          period hPeriod configuration plusBase minusBase hCore)

theorem regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_contDiffOn_two
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
        period hPeriod configuration plusBase minusBase measure)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  exact
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod minusBase measure).comp
        (regularGeneralMetricC2PairedMinusGaugeCoefficientInput_contDiffOn_two
          period hPeriod configuration plusBase minusBase)
        (fun _ hCore => regularGeneralMetricC2PairedMinusGaugeCoefficientInput_mem
          period hPeriod configuration plusBase minusBase hCore)

/-- The plus auxiliary action is C² after pullback to the genuine tangent. -/
theorem regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_projected_contDiffOn
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
          configuration.physical plusBase minusBase measure
          (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact
    (regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod configuration.physical plusBase minusBase measure).comp
      (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
      (fun direction hDirection =>
        ⟨(globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase direction).1
            hDirection, Set.mem_univ _⟩)

/-- The minus auxiliary action is C² after pullback to the genuine tangent. -/
theorem regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_projected_contDiffOn
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
          configuration.physical plusBase minusBase measure
          (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
            configuration data analysis realization plusBase minusBase
              direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact
    (regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod configuration.physical plusBase minusBase measure).comp
      (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
      (fun direction hDirection =>
        ⟨(globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase direction).1
            hDirection, Set.mem_univ _⟩)

/-- On a smooth projected direction, the plus auxiliary action is intrinsic. -/
theorem regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_projected_smooth
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
        configuration plusBase minusBase measure
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) =
      let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
        plusBase (direction.1.completeVariation.fullMetricPerturbation .plus)
          hDirection.plus_mem
      let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
        varied (configuration.coefficientFields.gauge.1 +
          direction.1.completeVariation.independent.gauge.1)
      intrinsicMaxwellAction period hPeriod varied
        (globalSmoothMaxwellPairing period hPeriod varied.metric potential
          potential) measure := by
  dsimp only
  unfold regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
  rw [regularGeneralMetricC2PairedPlusGaugeCoefficientInput_projected]
  simpa only [gaugePotentialFrameCoefficients_reconstructed] using
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_smooth
      period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus)
        hDirection.plus_mem measure
        (regularFrameGaugePotentialFromCoefficients period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            plusBase
              (direction.1.completeVariation.fullMetricPerturbation .plus)
              hDirection.plus_mem)
          (configuration.coefficientFields.gauge.1 +
            direction.1.completeVariation.independent.gauge.1)))

/-- On a smooth projected direction, the minus auxiliary action is intrinsic. -/
theorem regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_projected_smooth
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
        configuration plusBase minusBase measure
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) =
      let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
        minusBase (direction.1.completeVariation.fullMetricPerturbation .minus)
          hDirection.minus_mem
      let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
        varied (configuration.coefficientFields.gauge.2 +
          direction.1.completeVariation.independent.gauge.2)
      intrinsicMaxwellAction period hPeriod varied
        (globalSmoothMaxwellPairing period hPeriod varied.metric potential
          potential) measure := by
  dsimp only
  unfold regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
  rw [regularGeneralMetricC2PairedMinusGaugeCoefficientInput_projected]
  simpa only [gaugePotentialFrameCoefficients_reconstructed] using
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_smooth
      period hPeriod minusBase
        (direction.1.completeVariation.fullMetricPerturbation .minus)
        hDirection.minus_mem measure
        (regularFrameGaugePotentialFromCoefficients period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            minusBase
              (direction.1.completeVariation.fullMetricPerturbation .minus)
              hDirection.minus_mem)
          (configuration.coefficientFields.gauge.2 +
            direction.1.completeVariation.independent.gauge.2)))

/-- The genuine plus Maxwell block is the scaled completed paired action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_eq
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
        measure).maxwellPlus direction =
      couplings.plusMaxwellScale *
        regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
          configuration plusBase minusBase measure
            (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
              configuration plusBase minusBase direction) := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change couplings.plusMaxwellScale *
      intrinsicMaxwellAction period hPeriod
        (family.datumAtTotal period hPeriod 0 hZero direction).2.plusGravity.metric
        (family.datumAtTotal period hPeriod 0 hZero direction).2.plusMaxwell.basePairing
          measure = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  change couplings.plusMaxwellScale *
      intrinsicMaxwellAction period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
            hDirection.plus_mem)
        (globalSmoothMaxwellPairing period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
            (direction.1.completeVariation.fullMetricPerturbation .plus)
              hDirection.plus_mem).metric
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              plusBase
                (direction.1.completeVariation.fullMetricPerturbation .plus)
                hDirection.plus_mem)
            (configuration.coefficientFields.gauge.1 +
              direction.1.completeVariation.independent.gauge.1))
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              plusBase
                (direction.1.completeVariation.fullMetricPerturbation .plus)
                hDirection.plus_mem)
            (configuration.coefficientFields.gauge.1 +
              direction.1.completeVariation.independent.gauge.1))) measure = _
  rw [regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_projected_smooth
    period hPeriod configuration plusBase minusBase measure direction hDirection]

/-- The genuine minus Maxwell block is the scaled completed paired action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_eq
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
        measure).maxwellMinus direction =
      couplings.minusMaxwellScale *
        regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
          configuration plusBase minusBase measure
            (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
              configuration plusBase minusBase direction) := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change couplings.minusMaxwellScale *
      intrinsicMaxwellAction period hPeriod
        (family.datumAtTotal period hPeriod 0 hZero direction).2.minusGravity.metric
        (family.datumAtTotal period hPeriod 0 hZero direction).2.minusMaxwell.basePairing
          measure = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  change couplings.minusMaxwellScale *
      intrinsicMaxwellAction period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
          (direction.1.completeVariation.fullMetricPerturbation .minus)
            hDirection.minus_mem)
        (globalSmoothMaxwellPairing period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
            (direction.1.completeVariation.fullMetricPerturbation .minus)
              hDirection.minus_mem).metric
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              minusBase
                (direction.1.completeVariation.fullMetricPerturbation .minus)
                hDirection.minus_mem)
            (configuration.coefficientFields.gauge.2 +
              direction.1.completeVariation.independent.gauge.2))
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              minusBase
                (direction.1.completeVariation.fullMetricPerturbation .minus)
                hDirection.minus_mem)
            (configuration.coefficientFields.gauge.2 +
              direction.1.completeVariation.independent.gauge.2))) measure = _
  rw [regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_projected_smooth
    period hPeriod configuration plusBase minusBase measure direction hDirection]

/-- The genuine plus Maxwell block is C² on the exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_contDiffWithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).maxwellPlus
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hAux : ContDiffWithinAt Real 2
      (fun direction => couplings.plusMaxwellScale *
        regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
          configuration.physical plusBase minusBase measure
            (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
              configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (contDiffOn_const.mul
      (regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_projected_contDiffOn
        period hPeriod configuration data analysis realization plusBase
          minusBase measure)).contDiffWithinAt hPoint
  exact hAux.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection)
    hPoint

/-- The genuine minus Maxwell block is C² on the exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_contDiffWithinAt
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).maxwellMinus
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  have hAux : ContDiffWithinAt Real 2
      (fun direction => couplings.minusMaxwellScale *
        regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
          configuration.physical plusBase minusBase measure
            (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
              configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (contDiffOn_const.mul
      (regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_projected_contDiffOn
        period hPeriod configuration data analysis realization plusBase
          minusBase measure)).contDiffWithinAt hPoint
  exact hAux.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection)
    hPoint

/-- Gate marker: both genuine Maxwell blocks are exact and C². -/
theorem regular_general_metric_c2_paired_minimal_physical_maxwell_c2_gate
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).maxwellPlus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point ∧
      ContDiffWithinAt Real 2
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).maxwellMinus
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
          configuration.physical plusBase minusBase) point := by
  exact ⟨
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint,
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
end JanusFormal
