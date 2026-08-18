import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalWeingartenCoordinatePairing4D

/-!
# Raw local-section reduction for terminal H10

The completed Candidate-A second form and the canonical local-section second
form are both defined by symmetrizing their raw pairings.  This gate removes
that purely algebraic layer: it proves that equality of the raw pairings for
both index orders implies the terminal completed local-section agreement.

The remaining geometric statement is therefore unsymmetrized.  No new metric,
normal, connection, chart, frame, boundary datum, or axiom is introduced.
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
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance rawLocalSectionCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance rawLocalSectionCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    rawLocalSectionOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    rawLocalSectionOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    rawLocalSectionEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    rawLocalSectionEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Unsymmetrized terminal H10 contract.  Candidate indices `(row,column)`
correspond to the local-section pairing on the transported vectors
`(column,row)`, exactly as in the installed completed shape convention. -/
def CandidateANormalBoundaryCompletedGaussRawLocalSectionAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Prop :=
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
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric row column current boundary =
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod variedMetric displacement boundary parameter patch
          coordinate
          (normalBoundaryOrientationTangentEquiv period hPeriod boundary
            (frame.vectorAt boundary column))
          (normalBoundaryOrientationTangentEquiv period hPeriod boundary
            (frame.vectorAt boundary row))
          base

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the two raw index orders closes the symmetric local-section
agreement used by the terminal Candidate-A source bridge. -/
theorem
    candidateANormalBoundaryCompletedGaussLocalSectionAgreement_of_raw
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hRaw : CandidateANormalBoundaryCompletedGaussRawLocalSectionAgreement
      period hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryCompletedGaussLocalSectionAgreement period hPeriod
      metric tensor variedMetric displacement parameter := by
  refine { pointwise := ?_ }
  unfold CandidateANormalBoundaryCompletedGaussRawLocalSectionAgreement at hRaw
  intro boundary patch coordinate hAt row column
  dsimp only
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hRowColumn := hRaw boundary patch coordinate hAt row column
  have hColumnRow := hRaw boundary patch coordinate hAt column row
  dsimp only at hRowColumn hColumnRow
  unfold candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul,
    BoundedContinuousFunction.add_apply]
  rw [hRowColumn, hColumnRow]
  rw [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply]

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
