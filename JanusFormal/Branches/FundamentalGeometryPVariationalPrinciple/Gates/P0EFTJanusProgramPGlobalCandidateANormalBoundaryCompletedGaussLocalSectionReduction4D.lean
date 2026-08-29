import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalSourceMetricBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCompletedGaussCanonicalSourceBridge4D

/-!
# Terminal H10 reduction to one local-section identity

The canonical inverse-metric cancellation and its transport to the
orientation-double source have removed the shape-operator side of the final
H10 residue.  It now suffices to identify the completed Candidate-A Gauss
scalar with the already installed holonomic local-section second fundamental
form on the transported finite-frame generators.

This file records that smaller residual proposition and threads it through
the existing canonical, historical, trace, density, two-sheet action and
Candidate-A source bridges.  It introduces no new geometric datum or axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000
noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance completedGaussLocalSectionCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance completedGaussLocalSectionCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    completedGaussLocalSectionOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussLocalSectionOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    completedGaussLocalSectionEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    completedGaussLocalSectionEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Smallest remaining local geometric statement: on each installed generator
pair, the completed Candidate-A Gauss scalar is the existing holonomic
local-section second fundamental form evaluated on the transported vectors. -/
structure CandidateANormalBoundaryCompletedGaussLocalSectionAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) : Prop where
  pointwise :
    letI : NormedAddCommGroup
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
      candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
        period hPeriod metric
    letI : NormedSpace Real
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
      candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric
    letI : ChartedSpace ThroatCoverModel
        (CutThroatBoundary period hPeriod) :=
      P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
        period hPeriod
    letI : IsManifold throatCoverModelWithCorners ω
        (CutThroatBoundary period hPeriod) :=
      P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
        period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
        period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotient_isManifold period hPeriod
    ∀ (boundary : CutThroatBoundary period hPeriod)
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
      (hAt : patch.coordinateMap coordinate =
        normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
      (row column : NormalBoundaryTangentIndex period hPeriod),
      let current :=
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter)
      let frame := finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
          period hPeriod metric row column current boundary =
        normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
          period hPeriod variedMetric displacement boundary parameter patch
            coordinate
            (orientationDoubleToThroat period hPeriod boundary, parameter)
            (normalBoundaryOrientationTangentEquiv period hPeriod boundary
              (frame.vectorAt boundary column))
            (normalBoundaryOrientationTangentEquiv period hPeriod boundary
              (frame.vectorAt boundary row))

set_option backward.isDefEq.respectTransparency false in
/-- The local-section identity implies the previous canonical pulled-back
shape identity, by the proved source/target induced-metric bridge. -/
theorem
    candidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement_of_localSection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hLocal : CandidateANormalBoundaryCompletedGaussLocalSectionAgreement period
      hPeriod metric tensor variedMetric displacement parameter) :
    CandidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull :=
  CandidateANormalBoundaryMetricUnitGaussPointwiseAgreement.mk
    (period := period) (hPeriod := hPeriod) (metric := metric) (tensor := tensor)
      (variedMetric := variedMetric) (displacement := displacement)
        (parameter := parameter) (hNonNull := hNonNull) (by
          intro boundary patch coordinate hAt row column
          dsimp only
          let frame := finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          have hLocalAt :=
            hLocal.pointwise boundary patch coordinate hAt row column
          dsimp only at hLocalAt
          have hSource :=
            normalBoundarySmoothGraphInducedMetricMusical_canonicalShape_eq_localSection
              period hPeriod variedMetric displacement parameter hNonNull boundary
                patch coordinate hAt (frame.vectorAt boundary column)
                  (frame.vectorAt boundary row)
          exact hLocalAt.trans hSource.symm)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

set_option backward.isDefEq.respectTransparency false in
/-- Terminal Candidate-A GHY source theorem with the residual assumption
reduced to equality with the already installed holonomic local section. -/
theorem
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_completedGaussLocalSection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hNormalRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hVolumeRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hLocal :
      CandidateANormalBoundaryCompletedGaussLocalSectionAgreement period hPeriod
        metric tensor variedMetric displacement parameter)
    (hSource : data.nonNullBoundary =
      normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
        (NonNullFace := NonNullFace) einsteinScale variedMetric displacement
          parameter hNonNull) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) =
      globalCandidateAGHYAction period hPeriod data := by
  exact
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_of_completedGaussCanonical
      period hPeriod data einsteinScale metric hTransverse tensor variedMetric
        hVaried displacement parameter hNonNull hCurrent hNormalRootNonneg
          hVolumeRootNonneg
          (candidateANormalBoundaryCompletedGaussCanonicalSecondFormAgreement_of_localSection
            period hPeriod metric tensor variedMetric displacement parameter
              hNonNull hLocal)
          hSource

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionSourceBridge4D
end JanusFormal
