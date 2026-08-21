import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11TrueKernelGramFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteOrthogonalNamedModeOffDiagonalGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionSymmetryOrthogonalOffDiagonalGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D

/-!
# Strictly pre-named-kernel Candidate-A D11 adapter

The canonical H12 frontier already contains the physical five-sector geometry
and its actual basepoint operator.  A complete basepoint basis can either be
supplied directly or generated from independent named zero modes and one
global Garding estimate.  No named-kernel-family or Bismut--Freed packet is
imported.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleIsomorphismFamilyKernelGramGlobalBridge4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11TrueKernelGramFrontend4D
open P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteNamedModeComplementGap4D
open P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D
open P0EFTJanusProgramPFiniteOrthogonalNamedModeOffDiagonalGap4D
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalOperatorGarding4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateAActionSymmetryOrthogonalOffDiagonalGap4D
open P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

variable {measure : Measure (EffectiveQuotient period hPeriod)}

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFiveSectorCompletionHilbert4D period hPeriod configuration
    data analysis

attribute [local instance]
  commonHilbertNormedAddCommGroup
  commonHilbertInnerProductSpace
  commonHilbertNormedSpace
  commonHilbertModule
  commonHilbertCompleteSpace

private abbrev CanonicalChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelChart period hPeriod configuration data analysis
    einsteinScale hTransverse family

private abbrev CanonicalSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelSameAction period hPeriod configuration data
    analysis einsteinScale hTransverse family

private abbrev CanonicalPhysical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound

private abbrev CanonicalOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateAActualKernelOperator period hPeriod configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (frontier : GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode)

private abbrev Geometry := frontier.analytic.geometry

/-- The physical resolution is already fixed by the strict pre-named frontier. -/
def globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution :
    FiveSectorOrthogonalProductDecomposition
      (E := CandidateAHilbert period hPeriod configuration data analysis)
      (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary) :=
  (Geometry period hPeriod frontier).orthogonalResolution.toGeneric

theorem globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition :
    (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
      hPeriod frontier).decomposition =
    (Geometry period hPeriod frontier).coordinates.coordinates.decomposition.toContinuousLinearEquiv := by
  rfl

/-- The exact extra H12 estimate missing from the geometric frontier.  Its
vectors are not new data: they are the frontier's physical action generators. -/
structure GlobalHessianPreferredFiveSectorGeneratorGardingData4D where
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound)
      frontier.generators.translations.vector
      (frontier.generators.vector_annihilated period hPeriod))
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ current :
      CandidateAHilbert period hPeriod configuration data analysis,
    constant * ‖current‖ ^ 2 ≤
      ⟪current,
        CanonicalOperator period hPeriod einsteinScale hTransverse family
          chartBound current⟫_Real +
      defectConstant *
        ∑ mode : ZeroMode,
          ⟪current, frontier.generators.translations.vector mode⟫_Real ^ 2

/-- Package the frontier generators and the preceding estimate as the generic
automatic no-hidden-mode input. -/
def GlobalHessianPreferredFiveSectorGeneratorGardingData4D.toAutomaticSplit
    (gardingData : GlobalHessianPreferredFiveSectorGeneratorGardingData4D
      period hPeriod frontier) :
    FiniteKernelNamedModeAutomaticSplitData
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound) ZeroMode where
  vector := frontier.generators.translations.vector
  annihilated := frontier.generators.vector_annihilated period hPeriod
  linearIndependent := gardingData.linearIndependent
  constant := gardingData.constant
  constant_pos := gardingData.constant_pos
  defectConstant := gardingData.defectConstant
  defectConstant_nonneg := gardingData.defectConstant_nonneg
  garding := gardingData.garding

/-- Alternative H12 input: nonzero orthogonal frontier generators and the
five-sector lower bound on the complement of their ambient span. -/
structure GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
    (Component : CandidateAZeroModeSector → Type*)
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)] where
  nonzero : ∀ mode, frontier.generators.translations.vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪frontier.generators.translations.vector first,
      frontier.generators.translations.vector second⟫_Real = 0
  complementGarding :
    CandidateAFiveSectorOrthogonalOffDiagonalOperatorGardingData
      (Component := Component)
      (finiteNamedModeComplementOperator
        (CanonicalOperator period hPeriod einsteinScale hTransverse family
          chartBound)
        (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
          configuration data analysis
            (CanonicalChart period hPeriod einsteinScale hTransverse family)
            (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
            (CanonicalPhysical period hPeriod einsteinScale hTransverse family
              chartBound))
        frontier.generators.translations.vector
        (frontier.generators.vector_annihilated period hPeriod))

/-- Minimal orthogonality input: the frontier resolution already proves
cross-sector orthogonality, so only same-sector pairs remain to be checked. -/
structure GlobalHessianPreferredFiveSectorGeneratorWithinSectorGardingData4D
    (Component : CandidateAZeroModeSector → Type*)
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)] where
  nonzero : ∀ mode, frontier.generators.translations.vector mode ≠ 0
  within_orthogonal : ∀ {first second : ZeroMode}, first ≠ second →
    frontier.generators.classification.sectorOf first =
        frontier.generators.classification.sectorOf second →
      inner Real (frontier.generators.translations.vector first)
        (frontier.generators.translations.vector second) = 0
  complementGarding :
    CandidateAFiveSectorOrthogonalOffDiagonalOperatorGardingData
      (Component := Component)
      (finiteNamedModeComplementOperator
        (CanonicalOperator period hPeriod einsteinScale hTransverse family
          chartBound)
        (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
          configuration data analysis
            (CanonicalChart period hPeriod einsteinScale hTransverse family)
            (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
            (CanonicalPhysical period hPeriod einsteinScale hTransverse family
              chartBound))
        frontier.generators.translations.vector
        (frontier.generators.vector_annihilated period hPeriod))

/-- Complete the same-sector input with the cross-sector orthogonality already
proved by the physical five-sector resolution. -/
def GlobalHessianPreferredFiveSectorGeneratorWithinSectorGardingData4D.toComplementGarding
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (withinData :
      GlobalHessianPreferredFiveSectorGeneratorWithinSectorGardingData4D
        period hPeriod frontier Component) :
    GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
      period hPeriod frontier Component where
  nonzero := withinData.nonzero
  orthogonal := by
    intro first second hDifferent
    by_cases hSector :
        frontier.generators.classification.sectorOf first =
          frontier.generators.classification.sectorOf second
    · exact withinData.within_orthogonal hDifferent hSector
    · exact frontier.generators.vectors_inner_eq_zero_of_sector_ne period
        hPeriod first second hSector
  complementGarding := withinData.complementGarding

/-- Convert the preferred complement estimate to the generic exact-kernel
packet. -/
def GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D.toGeneric
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (complementData :
      GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
        period hPeriod frontier Component) :
    FiniteOrthogonalNamedModeOffDiagonalGapData
      (Component := Component)
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound)
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
          (CanonicalPhysical period hPeriod einsteinScale hTransverse family
            chartBound))
      ZeroMode where
  vector := frontier.generators.translations.vector
  annihilated := frontier.generators.vector_annihilated period hPeriod
  nonzero := complementData.nonzero
  orthogonal := complementData.orthogonal
  complementGarding := complementData.complementGarding

/-- The same preferred data closes the existing Candidate-A H12
action-symmetry packet; stationarity is already carried by the frontier. -/
def GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D.toActionSymmetryGap
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (complementData :
      GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
        period hPeriod frontier Component) :
    GlobalCandidateAActionSymmetryOrthogonalOffDiagonalGap4D period hPeriod
      Component configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode where
  translations := frontier.generators.translations
  nonzero := complementData.nonzero
  orthogonal := complementData.orthogonal
  complementGarding := complementData.complementGarding
  ll_stationary := frontier.analytic.ll_stationary

/-- The preferred complement packet also produces the existing H12
Fredholm/index-zero certificate. -/
def global_hessian_preferred_five_sector_complementGarding_h12
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (complementData :
      GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
        period hPeriod frontier Component) :=
  (complementData.toActionSymmetryGap period hPeriod frontier).h12 period
    hPeriod Component

/-- H12 with cross-sector orthogonality supplied by the frontier resolution. -/
def global_hessian_preferred_five_sector_withinSectorGarding_h12
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (withinData :
      GlobalHessianPreferredFiveSectorGeneratorWithinSectorGardingData4D
        period hPeriod frontier Component) :=
  global_hessian_preferred_five_sector_complementGarding_h12 period hPeriod
    frontier (withinData.toComplementGarding period hPeriod frontier)

/-- The complement estimate turns the physical frontier generators into the
complete basepoint-kernel basis. -/
noncomputable def globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_complementGarding
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (complementData :
      GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
        period hPeriod frontier Component) :
    Module.Basis ZeroMode Real
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound).ker :=
  let generic := complementData.toGeneric period hPeriod frontier
  (P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D.FiniteNamedModeComplementGapData.toNamedSpanning
    (generic.toComplementGap Component)
    (generic.kernelLinearIndependent Component)).toBasis

/-- Same basis constructor with cross-sector orthogonality discharged by the
frontier resolution. -/
noncomputable def globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_withinSectorGarding
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (withinData :
      GlobalHessianPreferredFiveSectorGeneratorWithinSectorGardingData4D
        period hPeriod frontier Component) :
    Module.Basis ZeroMode Real
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound).ker :=
  globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_complementGarding
    period hPeriod frontier (withinData.toComplementGarding period hPeriod frontier)

variable
    {operator : Real →
      CandidateAHilbert period hPeriod configuration data analysis →L[Real]
        CandidateAHilbert period hPeriod configuration data analysis}
    (operator_zero : operator 0 =
      CanonicalOperator period hPeriod einsteinScale hTransverse family chartBound)
    (baseKernelBasis : Module.Basis ZeroMode Real
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound).ker)

/-- The unique missing H12 entry, recast to the chosen D11 operator family. -/
def globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis :
    Module.Basis ZeroMode Real (operator 0).ker := by
  rw [operator_zero]
  exact baseKernelBasis

/-- Independent named zero modes and a global Garding estimate generate the
missing H12 basepoint basis; no kernel-spanning premise is supplied. -/
noncomputable def globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_automaticSplit
    (automatic : FiniteKernelNamedModeAutomaticSplitData
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound) ZeroMode) :
    Module.Basis ZeroMode Real
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound).ker :=
  automatic.toNoHidden.toNamedGarding.spanning.toBasis

/-- The established action-symmetry/stable-physical-form packet already
contains the exact named Gårding basis for the canonical operator. -/
noncomputable def globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_stablePhysicalForm
    (stable : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode) :
    Module.Basis ZeroMode Real
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound).ker :=
  (stable.toNamedGarding period hPeriod).garding.spanning.toBasis

variable
    {immersionCategory : SpinCImmersionCategory}
    {ellipticFamily : NaturalEllipticOperatorFamily immersionCategory}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory ellipticFamily
        (fun parameter state => operator parameter state))
    (refinement : FiveSectorNaturalRepresentationRefinementData representation
      (Geometry period hPeriod frontier).coordinates.coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData representation
      (Geometry period hPeriod frontier).coordinates.coordinates refinement)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation (Geometry period hPeriod frontier).coordinates.coordinates
        refinement pullback)

/-- Strict pre-named adapter.  Apart from the one complete basepoint basis, its
only new analytic premise is differentiability of the D11-transported vectors. -/
def globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis := baseKernelBasis) mode).1)) :
    GlobalHessianPreferredFiveSectorD11BasepointInput4D period hPeriod
      configuration data analysis Metric Abelian Matter Longitudinal Boundary
        ZeroMode operator (Geometry period hPeriod frontier).coordinates
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
            hPeriod frontier)
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
            period hPeriod frontier)
          representation refinement pullback isomorphisms where
  baseKernelBasis :=
    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
      (period := period) (hPeriod := hPeriod) (operator := operator)
      (operator_zero := operator_zero) (baseKernelBasis := baseKernelBasis)
  transported_vector_differentiable := transported_vector_differentiable

/-- Operator-norm regularity supplies differentiability of every transported
mode of the
strict pre-named input. -/
def globalHessianPreferredFiveSectorD11BasepointInput_of_operatorNormPreNamedFrontier
    (regularity : OperatorNormDifferentiableLinearTransportData
      (fun parameter vector =>
        isomorphisms.transport representation
          (Geometry period hPeriod frontier).coordinates.coordinates refinement
            pullback 0 parameter vector)) :
    GlobalHessianPreferredFiveSectorD11BasepointInput4D period hPeriod
      configuration data analysis Metric Abelian Matter Longitudinal Boundary
        ZeroMode operator (Geometry period hPeriod frontier).coordinates
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
            hPeriod frontier)
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
            period hPeriod frontier)
          representation refinement pullback isomorphisms :=
  globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier
    period hPeriod frontier operator_zero baseKernelBasis representation
      refinement pullback isomorphisms
        (fun mode => regularity.differentiable_apply
          (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
            (period := period) (hPeriod := hPeriod) (operator := operator)
            (operator_zero := operator_zero) (baseKernelBasis := baseKernelBasis)
              mode).1)

/-- Terminal strict pre-named checkpoint.  The frontier geometry, one H12
basepoint basis and the D11 transport data generate the complete differentiable true
kernel family, global Gram regularity and constant kernel rank. -/
theorem global_hessian_preferred_five_sector_D11_preNamed_true_kernel_gram_gate
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis := baseKernelBasis) mode).1)) :
    let d11Input :=
      globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier
        period hPeriod frontier operator_zero baseKernelBasis representation
          refinement pullback isomorphisms transported_vector_differentiable
    let gramData :=
      globalCandidateAFiveSectorIsomorphismFamilyKernelGramData period hPeriod
        configuration data analysis
          (Geometry period hPeriod frontier).coordinates
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
            hPeriod frontier)
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
            period hPeriod frontier)
          representation refinement pullback isomorphisms
            d11Input.baseKernelBasis
    let kernels :=
      globalHessianPreferredFiveSectorD11DifferentiableKernelBasisFamilyData
        period hPeriod (Geometry period hPeriod frontier).coordinates
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
            hPeriod frontier)
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
            period hPeriod frontier)
          representation refinement pullback isomorphisms d11Input
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => kernels.kernels.vector parameter mode)) ∧
    (∀ parameter,
      Submodule.span Real
          (Set.range
            (gramData.transportedKernelVector representation
              (Geometry period hPeriod frontier).coordinates.coordinates
                refinement pullback parameter)) = ⊤) ∧
    transportedKernelGramRegularSet representation
        (Geometry period hPeriod frontier).coordinates.coordinates refinement
          pullback gramData = Set.univ ∧
    (∀ parameter,
      Module.finrank Real (operator parameter).ker = Fintype.card ZeroMode) := by
  exact
    global_hessian_preferred_five_sector_D11_true_kernel_gram_gate period hPeriod
      (sectorData := (Geometry period hPeriod frontier).coordinates)
      (resolution :=
        globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
          hPeriod frontier)
      (decomposition_eq :=
        globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
          period hPeriod frontier)
      representation refinement pullback isomorphisms
        (globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier
          period hPeriod frontier operator_zero baseKernelBasis representation
            refinement pullback isomorphisms transported_vector_differentiable)

/-- Operator-norm version of the strict pre-named checkpoint. -/
def global_hessian_preferred_five_sector_D11_preNamed_operatorNorm_true_kernel_gram_gate
    (regularity : OperatorNormDifferentiableLinearTransportData
      (fun parameter vector =>
        isomorphisms.transport representation
          (Geometry period hPeriod frontier).coordinates.coordinates refinement
            pullback 0 parameter vector)) :=
  global_hessian_preferred_five_sector_D11_preNamed_true_kernel_gram_gate
    period hPeriod frontier operator_zero baseKernelBasis representation
      refinement pullback isomorphisms
        (fun mode => regularity.differentiable_apply
          (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
            (period := period) (hPeriod := hPeriod) (operator := operator)
            (operator_zero := operator_zero) (baseKernelBasis := baseKernelBasis)
              mode).1)

/-- Canonical restriction of the represented D11 family to its basepoint
linear frame. -/
def globalHessianPreferredFiveSectorD11PreNamedLinearFrame :
    LinearNaturalRepresentationAdmissibleIsomorphismFrameData representation
      (Geometry period hPeriod frontier).coordinates.coordinates refinement
        pullback where
  isomorphismAt := fun parameter => isomorphisms.isomorphism 0 parameter
  isomorphism_zero_inv := isomorphisms.isomorphism_self_inv 0
  reverseLinear := fun parameter => isomorphisms.reverseLinear 0 parameter
  forwardLinear := fun parameter => isomorphisms.forwardLinear 0 parameter
  reverse_source_agreement := fun parameter state =>
    isomorphisms.reverse_source_agreement 0 parameter state
  forward_source_agreement := fun parameter state =>
    isomorphisms.forward_source_agreement 0 parameter state
  reverse_target_agreement := fun parameter state =>
    isomorphisms.reverse_target_agreement 0 parameter state

/-- Metric compatibility of the pairwise D11 family supplies norm
preservation for its canonical basepoint frame. -/
theorem globalHessianPreferredFiveSectorD11PreNamedLinearFrame_reverse_norm_map
    (metric : LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      representation (Geometry period hPeriod frontier).coordinates.coordinates
        refinement pullback isomorphisms)
    (parameter : Real)
    (state : CandidateAHilbert period hPeriod configuration data analysis) :
    ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
      frontier representation refinement pullback isomorphisms).reverseLinear
        parameter state‖ = ‖state‖ := by
  change ‖isomorphisms.reverseLinear 0 parameter state‖ = ‖state‖
  exact metric.reverse_norm_map representation
    (Geometry period hPeriod frontier).coordinates.coordinates refinement
      pullback isomorphisms 0 parameter state

/-- Norm preservation upgrades the canonical basepoint linear frame to a
unitary frame. -/
def globalHessianPreferredFiveSectorD11PreNamedUnitaryFrame
    (reverse_norm_map : ∀ parameter state,
      ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
        frontier representation refinement pullback isomorphisms).reverseLinear
          parameter state‖ = ‖state‖) :
    UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData representation
      (Geometry period hPeriod frontier).coordinates.coordinates refinement
        pullback where
  linearFrame := globalHessianPreferredFiveSectorD11PreNamedLinearFrame period
    hPeriod frontier representation refinement pullback isomorphisms
  reverse_norm_map := reverse_norm_map

/-- The canonical unitary frame associated with the norm-preserving D11
family. -/
def globalHessianPreferredFiveSectorD11PreNamedRepresentedUnitaryFrame
    (reverse_norm_map : ∀ parameter state,
      ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
        frontier representation refinement pullback isomorphisms).reverseLinear
          parameter state‖ = ‖state‖)
    (parameter : Real) :
    CandidateAHilbert period hPeriod configuration data analysis
      ≃ₗᵢ[Real]
    CandidateAHilbert period hPeriod configuration data analysis :=
  (globalHessianPreferredFiveSectorD11PreNamedUnitaryFrame period hPeriod
    frontier representation refinement pullback isomorphisms reverse_norm_map).frame
      representation (Geometry period hPeriod frontier).coordinates.coordinates
        refinement pullback parameter

/-- Strong operator-norm regularity for the represented D11 family, packaged
without any kernel-family input.  This is optional for the kernel-only route,
whose minimal endpoint remains differentiability of the finitely many modes. -/
structure GlobalHessianPreferredFiveSectorD11PreNamedGeometricRegularityData4D where
  reverse_norm_map : ∀ parameter state,
    ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
      frontier representation refinement pullback isomorphisms).reverseLinear
        parameter state‖ = ‖state‖
  operatorRegularity : OperatorNormDifferentiableUnitaryFrameData
    (globalHessianPreferredFiveSectorD11PreNamedRepresentedUnitaryFrame
      period hPeriod frontier representation refinement pullback isomorphisms
        reverse_norm_map)

/-- Unitary specialization: a unitary frame, its operator derivative and its
pointwise agreement with represented D11 transport close the pre-named gate. -/
def global_hessian_preferred_five_sector_D11_preNamed_unitaryOperatorNorm_true_kernel_gram_gate
    (frame : Real →
      CandidateAHilbert period hPeriod configuration data analysis
        ≃ₗᵢ[Real]
      CandidateAHilbert period hPeriod configuration data analysis)
    (regularity : OperatorNormDifferentiableUnitaryFrameData frame)
    (agreement : ∀ parameter vector,
      frame parameter vector =
        isomorphisms.transport representation
          (Geometry period hPeriod frontier).coordinates.coordinates refinement
            pullback 0 parameter vector) :=
  global_hessian_preferred_five_sector_D11_preNamed_operatorNorm_true_kernel_gram_gate
    period hPeriod frontier operator_zero baseKernelBasis representation
      refinement pullback isomorphisms
        (OperatorNormDifferentiableLinearTransportData.ofUnitaryFrameAgreement
          frame regularity agreement)

/-- Canonical unitary specialization.  Norm preservation makes the unitary
frame and its agreement with represented transport automatic; only its single
operator-valued derivative remains analytic input. -/
def global_hessian_preferred_five_sector_D11_preNamed_normPreservingOperatorNorm_true_kernel_gram_gate
    (reverse_norm_map : ∀ parameter state,
      ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
        frontier representation refinement pullback isomorphisms).reverseLinear
          parameter state‖ = ‖state‖)
    (regularity : OperatorNormDifferentiableUnitaryFrameData
      (globalHessianPreferredFiveSectorD11PreNamedRepresentedUnitaryFrame
        period hPeriod frontier representation refinement pullback isomorphisms
          reverse_norm_map)) :=
  global_hessian_preferred_five_sector_D11_preNamed_unitaryOperatorNorm_true_kernel_gram_gate
    period hPeriod frontier operator_zero baseKernelBasis representation
      refinement pullback isomorphisms
        (globalHessianPreferredFiveSectorD11PreNamedRepresentedUnitaryFrame
          period hPeriod frontier representation refinement pullback isomorphisms
            reverse_norm_map)
        regularity (fun _ _ => rfl)

/-- Stronger strict pre-named checkpoint: independent zero modes plus Garding
generate the basepoint basis and hence the complete differentiable true-kernel family. -/
def global_hessian_preferred_five_sector_D11_automaticSplit_true_kernel_gram_gate
    (automatic : FiniteKernelNamedModeAutomaticSplitData
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound) ZeroMode)
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis :=
                    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_automaticSplit
                      period hPeriod automatic) mode).1)) :=
  global_hessian_preferred_five_sector_D11_preNamed_true_kernel_gram_gate
    period hPeriod frontier operator_zero
      (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_automaticSplit
        period hPeriod automatic)
      representation refinement pullback isomorphisms
        transported_vector_differentiable

/-- Preferred physical endpoint: the frontier action generators, their
independence, Garding, and differentiable D11 transport generate the true kernel family. -/
def global_hessian_preferred_five_sector_D11_generatorGarding_true_kernel_gram_gate
    (gardingData : GlobalHessianPreferredFiveSectorGeneratorGardingData4D
      period hPeriod frontier)
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis :=
                    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_automaticSplit
                      period hPeriod gardingData.toAutomaticSplit) mode).1)) :=
  global_hessian_preferred_five_sector_D11_automaticSplit_true_kernel_gram_gate
    period hPeriod frontier operator_zero representation refinement pullback
      isomorphisms gardingData.toAutomaticSplit
        transported_vector_differentiable

/-- Reuse the established stable-physical-form H12 construction as the
basepoint input of the D11 true-kernel/Gram frontend. -/
def global_hessian_preferred_five_sector_D11_stablePhysicalForm_true_kernel_gram_gate
    (stable : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode)
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis :=
                    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_stablePhysicalForm
                      period hPeriod stable) mode).1)) :=
  global_hessian_preferred_five_sector_D11_preNamed_true_kernel_gram_gate
    period hPeriod frontier operator_zero
      (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_stablePhysicalForm
        period hPeriod stable)
      representation refinement pullback isomorphisms
        transported_vector_differentiable

/-- A single operator-norm derivative discharges every modewise differentiability premise in
the preferred stable-physical-form endpoint. -/
def global_hessian_preferred_five_sector_D11_stablePhysicalForm_operatorNorm_true_kernel_gram_gate
    (stable : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode)
    (regularity : OperatorNormDifferentiableLinearTransportData
      (fun parameter vector =>
        isomorphisms.transport representation
          (Geometry period hPeriod frontier).coordinates.coordinates refinement
            pullback 0 parameter vector)) :=
  global_hessian_preferred_five_sector_D11_preNamed_operatorNorm_true_kernel_gram_gate
    period hPeriod frontier operator_zero
      (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_stablePhysicalForm
        period hPeriod stable)
      representation refinement pullback isomorphisms regularity

/-- Recommended pre-`NamedKernel` endpoint.  The stable physical packet
supplies the complete H12 basis, norm preservation supplies the canonical
unitary D11 frame, and one operator derivative supplies all differentiable modes. -/
def global_hessian_preferred_five_sector_D11_stablePhysicalForm_normPreservingOperatorNorm_true_kernel_gram_gate
    (stable : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode)
    (reverse_norm_map : ∀ parameter state,
      ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
        frontier representation refinement pullback isomorphisms).reverseLinear
          parameter state‖ = ‖state‖)
    (regularity : OperatorNormDifferentiableUnitaryFrameData
      (globalHessianPreferredFiveSectorD11PreNamedRepresentedUnitaryFrame
        period hPeriod frontier representation refinement pullback isomorphisms
          reverse_norm_map)) :=
  global_hessian_preferred_five_sector_D11_preNamed_normPreservingOperatorNorm_true_kernel_gram_gate
    period hPeriod frontier operator_zero
      (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_stablePhysicalForm
        period hPeriod stable)
      representation refinement pullback isomorphisms reverse_norm_map regularity

/-- Compact strong endpoint: one stable H12 packet and one operator-norm D11
regularity packet generate the complete differentiable true-kernel/Gram conclusion. -/
def global_hessian_preferred_five_sector_D11_stablePhysicalForm_geometricRegularity_true_kernel_gram_gate
    (stable : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode)
    (regularityData :
      GlobalHessianPreferredFiveSectorD11PreNamedGeometricRegularityData4D
        period hPeriod frontier representation refinement pullback isomorphisms) :=
  global_hessian_preferred_five_sector_D11_stablePhysicalForm_normPreservingOperatorNorm_true_kernel_gram_gate
    period hPeriod frontier operator_zero representation refinement pullback
      isomorphisms stable regularityData.reverse_norm_map
        regularityData.operatorRegularity

/-- Metric form of the strong endpoint: inner-product compatibility derives
norm preservation, leaving only the operator-valued derivative as analytic
input. -/
def global_hessian_preferred_five_sector_D11_stablePhysicalForm_metricOperatorNorm_true_kernel_gram_gate
    (stable : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        ZeroMode)
    (metric : LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      representation (Geometry period hPeriod frontier).coordinates.coordinates
        refinement pullback isomorphisms)
    (regularity : OperatorNormDifferentiableUnitaryFrameData
      (globalHessianPreferredFiveSectorD11PreNamedRepresentedUnitaryFrame
        period hPeriod frontier representation refinement pullback isomorphisms
          (globalHessianPreferredFiveSectorD11PreNamedLinearFrame_reverse_norm_map
            period hPeriod frontier representation refinement pullback
              isomorphisms metric))) :=
  global_hessian_preferred_five_sector_D11_stablePhysicalForm_normPreservingOperatorNorm_true_kernel_gram_gate
    period hPeriod frontier operator_zero representation refinement pullback
      isomorphisms stable
        (globalHessianPreferredFiveSectorD11PreNamedLinearFrame_reverse_norm_map
          period hPeriod frontier representation refinement pullback
            isomorphisms metric)
        regularity

/-- Preferred five-sector H12 endpoint: orthogonal nonzero frontier generators
and a positive complement margin generate the complete differentiable true-kernel family. -/
def global_hessian_preferred_five_sector_D11_complementGarding_true_kernel_gram_gate
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (complementData :
      GlobalHessianPreferredFiveSectorGeneratorComplementGardingData4D
        period hPeriod frontier Component)
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis :=
                    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_complementGarding
                      period hPeriod frontier complementData) mode).1)) :=
  global_hessian_preferred_five_sector_D11_preNamed_true_kernel_gram_gate
    period hPeriod frontier operator_zero
      (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_complementGarding
        period hPeriod frontier complementData)
      representation refinement pullback isomorphisms
        transported_vector_differentiable

/-- Strongest current H12--D11 endpoint: cross-sector orthogonality is
automatic, leaving only same-sector orthogonality and the complement margin. -/
def global_hessian_preferred_five_sector_D11_withinSectorGarding_true_kernel_gram_gate
    {Component : CandidateAZeroModeSector → Type*}
    [∀ sector, NormedAddCommGroup (Component sector)]
    [∀ sector, InnerProductSpace Real (Component sector)]
    (withinData :
      GlobalHessianPreferredFiveSectorGeneratorWithinSectorGardingData4D
        period hPeriod frontier Component)
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (Geometry period hPeriod frontier).coordinates.coordinates refinement
              pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod) (operator := operator)
                  (operator_zero := operator_zero)
                  (baseKernelBasis :=
                    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis_of_withinSectorGarding
                      period hPeriod frontier withinData) mode).1)) :=
  global_hessian_preferred_five_sector_D11_complementGarding_true_kernel_gram_gate
    period hPeriod frontier operator_zero representation refinement pullback
      isomorphisms (withinData.toComplementGarding period hPeriod frontier)
        transported_vector_differentiable

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
end JanusFormal
