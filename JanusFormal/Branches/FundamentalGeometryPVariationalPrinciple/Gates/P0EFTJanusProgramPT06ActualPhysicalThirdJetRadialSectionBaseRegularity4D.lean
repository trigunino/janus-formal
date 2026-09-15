import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanPiolaNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

/-!
# Base regularity of the radial physical third-jet density

In a fixed simultaneous base/fiber trivialization, the radial vector density
is evaluated on the actual Candidate-A physical third-jet section.  The
resulting base field is smooth on the common chart locus, hence measurable
there and integrable on every compact subdomain for the canonical throat
measure.  The Cartan--Piola law is also specialized to that physical section.

No regularity of the preferred-index selector, global fixed-coordinate
trivialization, or global Stokes statement is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetRadialSectionBaseRegularity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanPiolaNaturality4D
open P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D
open P0EFTJanusProgramPT06RadialJointHorizontalDifferentialBridge4D
open P0EFTJanusProgramPT06GlobalPhysicalThirdJetVectorDensitySection4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (Base period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (Base period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (Base period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (Base period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (Base period hPeriod) where
  measurable_eq := rfl

private abbrev Chart :=
  ActualPhysicalThirdOrderJetProductBundleIndex period hPeriod

private abbrev PhysicalThirdJetCore :=
  actualPhysicalThirdOrderJetProductVectorBundleCore
    period hPeriod .positiveQuarter

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Common locus of two fixed base charts and two physical J³ fiber charts. -/
def programPT06RadialPhysicalThirdJetBaseChartDomain
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod) : Set (Base period hPeriod) :=
  ((extChartAt throatCoverModelWithCorners chartCenter).source ∩
      (extChartAt throatCoverModelWithCorners referenceCenter).source) ∩
    ((PhysicalThirdJetCore period hPeriod).baseSet chart ∩
      (PhysicalThirdJetCore period hPeriod).baseSet reference)

theorem programPT06RadialPhysicalThirdJetBaseChartDomain_isOpen
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod) :
    IsOpen (programPT06RadialPhysicalThirdJetBaseChartDomain period hPeriod
      referenceCenter chartCenter reference chart) := by
  unfold programPT06RadialPhysicalThirdJetBaseChartDomain
  simpa only [extChartAt_source] using
    (((chartAt ThroatCoverModel chartCenter).open_source.inter
    (chartAt ThroatCoverModel referenceCenter).open_source).inter
      ((PhysicalThirdJetCore period hPeriod).isOpen_baseSet chart |>.inter
        ((PhysicalThirdJetCore period hPeriod).isOpen_baseSet reference)))

/-- Proof-free local representative evaluated on the genuine Candidate-A
physical J³ section. -/
def programPT06RadialPhysicalThirdJetBaseChartField
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod) :
    Base period hPeriod → ThroatCoverCoordinates :=
  fun base ↦
    programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
      chartCenter referenceCenter chart reference
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional)
      (extChartAt throatCoverModelWithCorners chartCenter base,
        (globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
          period hPeriod data).extractor chart base)

/-- On the valid locus, the proof-free field is the established physical J³
chart evaluation. -/
theorem programPT06RadialPhysicalThirdJetBaseChartField_eq_chartEvaluation
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (reference chart : Chart period hPeriod)
    (hBase : base ∈ programPT06RadialPhysicalThirdJetBaseChartDomain
      period hPeriod referenceCenter chartCenter reference chart) :
    programPT06RadialPhysicalThirdJetBaseChartField period hPeriod data
        functional referenceCenter chartCenter reference chart base =
      globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation
        period hPeriod data functional referenceCenter chartCenter base
        hBase.1.2 hBase.1.1 reference chart := by
  unfold programPT06RadialPhysicalThirdJetBaseChartField
    globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
  exact programPT06ActualPhysicalThirdJetVectorDensityJointPullback_at
    period hPeriod chartCenter referenceCenter base hBase.1.1 hBase.1.2
      chart reference
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional)
      ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod data).extractor chart base)

/-- The local evaluation field is smooth in the base variable on its common
trivialization locus. -/
theorem programPT06RadialPhysicalThirdJetBaseChartField_contMDiffOn
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
      (programPT06RadialPhysicalThirdJetBaseChartField period hPeriod data
        functional referenceCenter chartCenter reference chart)
      (programPT06RadialPhysicalThirdJetBaseChartDomain period hPeriod
        referenceCenter chartCenter reference chart) := by
  intro base hBase
  let coordinates :=
    globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod data
  have hJoint :=
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityJointPullback_contDiffAt
      period hPeriod functional chartCenter referenceCenter base hBase.1.1
        hBase.1.2 chart reference hBase.2
        (coordinates.extractor chart base)
  have hInput : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D) ∞
      (fun current : Base period hPeriod ↦
        (extChartAt throatCoverModelWithCorners chartCenter current,
          coordinates.extractor chart current)) base :=
    (contMDiffAt_extChartAt' (by
      simpa only [extChartAt_source] using hBase.1.1)).prodMk_space
      ((coordinates.extractor_contMDiffOn chart base hBase.2.1).contMDiffAt
        ((PhysicalThirdJetCore period hPeriod).isOpen_baseSet chart |>.mem_nhds
          hBase.2.1))
  exact (ContDiffAt.comp_contMDiffAt
    (f := fun current : Base period hPeriod ↦
      (extChartAt throatCoverModelWithCorners chartCenter current,
        coordinates.extractor chart current)) hJoint hInput).contMDiffWithinAt

/-- Local smoothness gives canonical-measure strong measurability on the
common chart locus. -/
theorem programPT06RadialPhysicalThirdJetBaseChartField_aestronglyMeasurable
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod) :
    AEStronglyMeasurable
      (programPT06RadialPhysicalThirdJetBaseChartField period hPeriod data
        functional referenceCenter chartCenter reference chart)
      ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
        (programPT06RadialPhysicalThirdJetBaseChartDomain period hPeriod
          referenceCenter chartCenter reference chart)) := by
  exact
    (programPT06RadialPhysicalThirdJetBaseChartField_contMDiffOn period hPeriod
      data functional referenceCenter chartCenter reference chart).continuousOn
      |>.aestronglyMeasurable
        (programPT06RadialPhysicalThirdJetBaseChartDomain_isOpen period hPeriod
          referenceCenter chartCenter reference chart).measurableSet

/-- The evaluated radial field is integrable on every compact subdomain of a
fixed valid trivialization for the canonical throat measure. -/
theorem programPT06RadialPhysicalThirdJetBaseChartField_integrableOn_compact
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod)
    (compactDomain : Set (Base period hPeriod))
    (hCompact : IsCompact compactDomain)
    (hSubset : compactDomain ⊆
      programPT06RadialPhysicalThirdJetBaseChartDomain period hPeriod
        referenceCenter chartCenter reference chart) :
    IntegrableOn
      (programPT06RadialPhysicalThirdJetBaseChartField period hPeriod data
        functional referenceCenter chartCenter reference chart)
      compactDomain (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact
    ((programPT06RadialPhysicalThirdJetBaseChartField_contMDiffOn period hPeriod
      data functional referenceCenter chartCenter reference chart).continuousOn.mono
        hSubset).integrableOn_compact hCompact

/-- Pointwise, choosing the preferred reference at the current base recovers
the Gate-1073 radial global-section representative. -/
theorem programPT06RadialPhysicalThirdJetBaseChartField_eq_globalSection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (chartCenter base : Base period hPeriod)
    (chart : Chart period hPeriod)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (hChart : base ∈ (PhysicalThirdJetCore period hPeriod).baseSet chart) :
    programPT06RadialPhysicalThirdJetBaseChartField period hPeriod data
        functional base chartCenter
        ((PhysicalThirdJetCore period hPeriod).indexAt base) chart base =
      (programPT06T02DegreeFourRadialCartanGlobalPhysicalThirdJetVectorDensitySection
        period hPeriod functional).representative base
          { center := chartCenter
            center_mem := hChartCenter
            fiberChart := chart
            fiber_mem := hChart }
        ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
          period hPeriod data).extractor chart base) := by
  unfold programPT06RadialPhysicalThirdJetBaseChartField
    programPT06T02DegreeFourRadialCartanGlobalPhysicalThirdJetVectorDensitySection
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
  exact programPT06ActualPhysicalThirdJetVectorDensityJointPullback_at
    period hPeriod chartCenter base base hChartCenter
      (mem_extChartAt_source base) chart
      ((PhysicalThirdJetCore period hPeriod).indexAt base)
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional)
      ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod data).extractor chart base)

/-- Cartan--Piola naturality evaluated on the genuine physical J³ section;
the target jet is the actual extractor in the reference chart. -/
theorem programPT06T02DegreeFourRadialCartan_horizontalDifferential_on_physicalSection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (reference chart : Chart period hPeriod)
    (hBase : base ∈ programPT06RadialPhysicalThirdJetBaseChartDomain
      period hPeriod referenceCenter chartCenter reference chart)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        (extChartAt throatCoverModelWithCorners chartCenter base)
        ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
          period hPeriod data).extractor chart base) frame =
      programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
          chartCenter referenceCenter
          (extChartAt throatCoverModelWithCorners chartCenter base) *
        programPT06ActualPhysicalThirdJetJointHorizontalDifferential
          (programPT06BaseDependentPhysicalVectorDensityOfAutonomous
            (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
              period hPeriod functional))
          (extChartAt throatCoverModelWithCorners referenceCenter base)
          ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
            period hPeriod data).extractor reference base)
          (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
            chartCenter referenceCenter base hBase.1.1 hBase.1.2
            chart reference hBase.2
            ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
              period hPeriod data).extractor chart base) frame) := by
  rw [← globalCandidateAActualPhysicalThirdOrderJetExtractor_coordChange
    period hPeriod data chart reference base hBase.2]
  exact
    programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_horizontalDifferential
      period hPeriod functional referenceCenter chartCenter base hBase.1.2
        hBase.1.1 reference chart hBase.2
        ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
          period hPeriod data).extractor chart base) frame

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetRadialSectionBaseRegularity4D
end JanusFormal
