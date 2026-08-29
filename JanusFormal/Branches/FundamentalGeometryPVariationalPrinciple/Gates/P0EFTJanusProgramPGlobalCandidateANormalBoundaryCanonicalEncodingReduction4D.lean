import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalShapeTrace4D

/-!
# Scalar reduction of the canonical H10 encoding agreement

The preceding gate fixes the intrinsic shape operator and proves its trace.
The remaining `HistoricalGaussEncodingAgreement` is still an equality of
redundant finite-frame matrices.  This file removes that coefficient-space
algebra.

It is enough to identify the historical symmetric second fundamental form on
each pair of the already installed finite throat generators with the intrinsic
metric pairing of `(g₀⁻¹ h) ∘ (h⁻¹ K)`.  Faithful analysis/synthesis and the
inverse frame-operator cancellation then recover the full matrix equality.

A second reduction rewrites that pairing through the pulled-back induced
metric musical map.  Thus the final geometric residue is a scalar equality of
two second fundamental forms; no inverse matrix, redundant trace, or new
boundary datum remains.
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
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalEncodingReductionCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance canonicalEncodingReductionCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    canonicalEncodingReductionOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalEncodingReductionOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    canonicalEncodingReductionEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalEncodingReductionEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise form of the residual H10 encoding statement.  It contains no
coefficient-space inverse: the historical second fundamental form is compared
directly with the intrinsic metric pairing of the canonical composite
`(g₀⁻¹ h) ∘ (h⁻¹ K)` on the installed finite generating family. -/
def CandidateANormalBoundaryHistoricalGaussShapePairingAgreement
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
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
      variedMetric displacement parameter boundary
    let shape :=
      normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull row column boundary =
      (intrinsicSmoothNondegenerateThroatMetric
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).1.tensor
        boundary
        (frame.vectorAt boundary row)
        ((relative.toLinearMap.comp shape)
          (frame.vectorAt boundary column))

/-- Faithful finite-frame reconstruction turns pointwise pairing equality into
the full redundant matrix encoding required by the preceding H10 gate. -/
theorem candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_shapePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hPairing : CandidateANormalBoundaryHistoricalGaussShapePairingAgreement
      period hPeriod metric tensor variedMetric displacement parameter
        hNonNull) :
    CandidateANormalBoundaryHistoricalGaussEncodingAgreement period hPeriod
      metric tensor variedMetric displacement parameter hNonNull := by
  unfold CandidateANormalBoundaryHistoricalGaussEncodingAgreement
  unfold CandidateANormalBoundaryHistoricalGaussShapePairingAgreement at hPairing
  intro boundary patch coordinate hAt
  classical
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
    variedMetric displacement parameter boundary
  let shape :=
    normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter hNonNull boundary patch coordinate hAt
  have hDual :
      (fun row column =>
        normalBoundaryReferenceDualCoefficientMatrix
          period hPeriod row column boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary
          ((intrinsicThroatFiniteFrameOperator
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            frame boundary).inverse.toLinearMap) := by
    ext row column
    simpa [frame] using
      (normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse
        period hPeriod row column boundary)
  have hHistorical :
      (fun row column =>
        candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt period
          hPeriod metric tensor variedMetric displacement parameter hNonNull row
            column boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary
          ((intrinsicThroatFiniteFrameOperator
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              frame boundary).toLinearMap.comp
            (relative.toLinearMap.comp shape)) := by
    ext row column
    have hPair := hPairing boundary patch coordinate hAt row column
    dsimp only at hPair
    calc
      candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt period
          hPeriod metric tensor variedMetric displacement parameter hNonNull row
            column boundary =
          (intrinsicSmoothNondegenerateThroatMetric
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).1.tensor
          boundary (frame.vectorAt boundary row)
          ((relative.toLinearMap.comp shape)
            (frame.vectorAt boundary column)) := by
            simpa only [frame, relative, shape] using hPair
      _ = intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary
          ((intrinsicThroatFiniteFrameOperator
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              frame boundary).toLinearMap.comp
            (relative.toLinearMap.comp shape)) row column := by
              symm
              exact
                intrinsicThroatFiniteFrameEndomorphismMatrixAt_operator_comp_apply
                  (doubledPeriod period)
                  (doubledPeriod_ne_zero period hPeriod) frame boundary
                  (relative.toLinearMap.comp shape) row column
  have hCancel :=
    intrinsicThroatFiniteFrameEncoding_inverse_mul_operator_comp
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary (relative.toLinearMap.comp shape)
  rw [← hDual, ← hHistorical] at hCancel
  unfold
    candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
  ext row column
  have hEntry := congrArg (fun matrix => matrix row column) hCancel
  simpa [Matrix.mul_apply, frame, NormalBoundaryTangentIndex] using hEntry

/-- Pointwise completed metric-unit Gauss form paired with the canonical shape
operator, under this module's installed boundary instances. -/
structure CandidateANormalBoundaryMetricUnitGaussPointwiseAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) : Prop where
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
      let shape :=
        normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
          variedMetric displacement parameter hNonNull boundary patch coordinate
            hAt
      candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
          period hPeriod metric row column current boundary =
        normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric
          displacement parameter boundary
          (shape (frame.vectorAt boundary column))
          (frame.vectorAt boundary row)

/-- Final scalar geometric residue after cancelling the intrinsic reference
metric.  It says that the historical symmetric form equals the induced metric
applied to the canonical shape operator. -/
def CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement
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
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let shape :=
      normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull row column boundary =
      normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric
        displacement parameter boundary
        (shape (frame.vectorAt boundary column))
        (frame.vectorAt boundary row)

/-- Constructor for the pointwise presentation of the pulled-back second-form
agreement, kept beside the definition so its installed instances are shared. -/
theorem candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_mk
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hPointwise :
      ∀ (boundary : CutThroatBoundary period hPeriod)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
        (hAt : patch.coordinateMap coordinate =
          normalGraphOrientationDouble period hPeriod displacement
            (boundary, parameter))
        (row column : NormalBoundaryTangentIndex period hPeriod),
        let frame := finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        let shape :=
          normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
            variedMetric displacement parameter hNonNull boundary patch
              coordinate hAt
        candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt
            period hPeriod metric tensor variedMetric displacement parameter
              hNonNull row column boundary =
          normalBoundarySmoothGraphInducedMetricMusical period hPeriod
            variedMetric displacement parameter boundary
            (shape (frame.vectorAt boundary column))
            (frame.vectorAt boundary row)) :
    CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull := by
  exact hPointwise

set_option maxHeartbeats 4800000 in
set_option backward.isDefEq.respectTransparency false in
/-- A completed metric-unit Gauss pairing gives the historical pairing
pointwise, with all boundary instances fixed at the definition site. -/
theorem candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_of_metricUnitGaussPointwise
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
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hRootNonneg : ∀ point : CutThroatBoundary period hPeriod, 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point)
    (hPointwise :
      CandidateANormalBoundaryMetricUnitGaussPointwiseAgreement period hPeriod
        metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement period
      hPeriod metric tensor variedMetric displacement parameter hNonNull := by
  apply candidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement_mk
    period hPeriod metric tensor variedMetric displacement parameter hNonNull
  intro boundary patch coordinate hAt row column
  dsimp only
  exact
    (candidateANormalBoundaryMetricUnitGaussExtrinsicCurvature_eq_historicalWeingarten
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter hNonNull hCurrent hRootNonneg row column boundary patch
          coordinate hAt).symm.trans
      (hPointwise.pointwise boundary patch coordinate hAt row column)

/-- Raising with the intrinsic reference metric and then pairing with that same
metric cancels exactly.  Therefore the pulled-back second-form equality is
already the pointwise shape-pairing equality above. -/
theorem candidateANormalBoundaryHistoricalGaussShapePairingAgreement_of_pulledBackSecondForm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hSecondForm :
      CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull) :
    CandidateANormalBoundaryHistoricalGaussShapePairingAgreement period hPeriod
      metric tensor variedMetric displacement parameter hNonNull := by
  unfold CandidateANormalBoundaryHistoricalGaussShapePairingAgreement
  unfold CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement at hSecondForm
  intro boundary patch coordinate hAt row column
  classical
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
    variedMetric displacement parameter boundary
  let shape :=
    normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter hNonNull boundary patch coordinate hAt
  have hHistorical := hSecondForm boundary patch coordinate hAt row column
  dsimp only at hHistorical ⊢
  rw [hHistorical]
  have hRaise := intrinsicThroatMetric_apply_inverseMusical
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) boundary
    (frame.vectorAt boundary row)
    (normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric
      displacement parameter boundary
      (shape (frame.vectorAt boundary column)))
  change
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod variedMetric
        displacement parameter boundary
        (shape (frame.vectorAt boundary column))
        (frame.vectorAt boundary row) =
      (intrinsicSmoothNondegenerateThroatMetric
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).1.tensor
        boundary (frame.vectorAt boundary row)
        (intrinsicThroatInverseMusical
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) boundary
          (normalBoundarySmoothGraphInducedMetricMusical period hPeriod
            variedMetric displacement parameter boundary
            (shape (frame.vectorAt boundary column))))
  exact hRaise.symm

/-- The scalar second-form identity is sufficient for the exact matrix
encoding consumed by the terminal Candidate-A source bridge. -/
theorem candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_pulledBackSecondForm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hSecondForm :
      CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull) :
    CandidateANormalBoundaryHistoricalGaussEncodingAgreement period hPeriod
      metric tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_shapePairing
    period hPeriod metric tensor variedMetric displacement parameter hNonNull
      (candidateANormalBoundaryHistoricalGaussShapePairingAgreement_of_pulledBackSecondForm
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull hSecondForm)

/-- Direct chart-free trace bridge from the final scalar second-form residue. -/
theorem candidateANormalBoundaryHistoricalGaussTraceAgreement_of_pulledBackSecondForm
    (metric : RegularGeneralLorentzMetric period hPeriod)
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
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hSecondForm :
      CandidateANormalBoundaryHistoricalGaussPulledBackSecondFormAgreement
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull) :
    CandidateANormalBoundaryHistoricalGaussTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussTraceAgreement_of_encodingAgreement
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      hNonNull hCurrent
      (candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_pulledBackSecondForm
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull hSecondForm)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
