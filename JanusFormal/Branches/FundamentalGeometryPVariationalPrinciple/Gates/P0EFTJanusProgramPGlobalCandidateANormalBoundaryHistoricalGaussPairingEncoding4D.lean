import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryCanonicalShapeTrace4D

/-!
# Generator-pairing reduction for the H10 historical Gauss encoding

The last H10 encoding statement is a faithful finite-frame matrix identity.
This gate reduces it to its geometric scalar content: on every pair of the
already installed redundant throat generators, the historical symmetric
Weingarten form is the induced metric paired with the canonical shape
operator.

The fixed dual coefficient matrix then cancels the reference frame operator
by the existing finite-frame algebra.  Thus no matrix inverse, trace, or
coefficient-space extension remains in the residual geometric statement.
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
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance historicalGaussPairingEncodingCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance historicalGaussPairingEncodingCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    historicalGaussPairingEncodingOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussPairingEncodingOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    historicalGaussPairingEncodingEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    historicalGaussPairingEncodingEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Scalar residual behind the final historical redundant-frame encoding.
It states the usual identity `K(u,v) = h(u, S v)` on the already installed
finite generating family. -/
def CandidateANormalBoundaryHistoricalGaussGeneratorPairingAgreement
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
    candidateANormalBoundaryHistoricalWeingartenExtrinsicCurvatureAt period
        hPeriod metric tensor variedMetric displacement parameter hNonNull row
          column boundary =
      (intrinsicSmoothNondegenerateThroatMetric
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).1.tensor
        boundary (frame.vectorAt boundary row)
        (relative (shape (frame.vectorAt boundary column)))

/-- Generator pairings determine the full faithful encoding.  The proof uses
only the existing coefficient reconstruction and inverse-frame cancellation. -/
theorem candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_generatorPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hPairing :
      CandidateANormalBoundaryHistoricalGaussGeneratorPairingAgreement period
        hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussEncodingAgreement period hPeriod
      metric tensor variedMetric displacement parameter hNonNull := by
  intro boundary patch coordinate hAt
  dsimp only
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
          (relative (shape (frame.vectorAt boundary column))) := by
            simpa [frame, relative, shape] using hPair
      _ = intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary
          ((intrinsicThroatFiniteFrameOperator
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              frame boundary).toLinearMap.comp
            (relative.toLinearMap.comp shape)) row column := by
              symm
              simpa [LinearMap.comp_apply] using
                (intrinsicThroatFiniteFrameEndomorphismMatrixAt_operator_comp_apply
                  (doubledPeriod period)
                  (doubledPeriod_ne_zero period hPeriod) frame boundary
                  (relative.toLinearMap.comp shape) row column)
  have hCancel :=
    intrinsicThroatFiniteFrameEncoding_inverse_mul_operator_comp
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary (relative.toLinearMap.comp shape)
  rw [← hDual, ← hHistorical] at hCancel
  unfold
    candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
  simpa [Matrix.mul_apply] using hCancel

/-- Consequently the scalar generator identity already yields the chart-free
trace agreement consumed by the action-source theorem. -/
theorem candidateANormalBoundaryHistoricalGaussTraceAgreement_of_generatorPairing
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
    (hPairing :
      CandidateANormalBoundaryHistoricalGaussGeneratorPairingAgreement period
        hPeriod metric tensor variedMetric displacement parameter hNonNull) :
    CandidateANormalBoundaryHistoricalGaussTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussTraceAgreement_of_encodingAgreement
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      hNonNull hCurrent
      (candidateANormalBoundaryHistoricalGaussEncodingAgreement_of_generatorPairing
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull hPairing)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
