import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalGaussTraceFactorization4D

/-!
# Canonical shape trace for the completed Candidate-A boundary

This gate removes the trace half of the last H10 finite-frame witness.  The
intrinsic shape operator is the already installed inverse induced metric
composed with the already installed smooth local-section second fundamental
form, transported through the proved orientation-double tangent equivalence.
Its basis-independent linear trace is therefore exactly the existing
holonomic local mean curvature.

After this construction the residual H10 statement is only that the
historical redundant-frame matrix encodes the relative induced metric
composed with this canonical shape operator.  No additional metric, normal,
connection, chart, or boundary action is introduced.
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

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance canonicalShapeTraceCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance canonicalShapeTraceCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000)
    canonicalShapeTraceOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalShapeTraceOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000)
    canonicalShapeTraceEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000)
    canonicalShapeTraceEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance canonicalShapeTraceTangentFiniteDimensional
    (boundary : CutThroatBoundary period hPeriod) :
    FiniteDimensional Real
      (TangentSpace throatCoverModelWithCorners boundary) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

/-- Target-side intrinsic shape operator `h⁻¹K` in the smooth local section
of the effective throat. -/
def normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    TangentSpace throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary) →ₗ[Real]
      TangentSpace throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary) :=
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  (normalGraphInducedMetricInverseCoordinates period hPeriod variedMetric
      displacement base base).toLinearMap.comp
    (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
      period hPeriod variedMetric displacement boundary parameter patch
        coordinate base).toLinearMap

/-- Source-side canonical shape operator.  It is the target operator pulled
back through the already proved orientation-double tangent equivalence. -/
private def normalBoundaryOrientationCoordinateEquiv
    (boundary : CutThroatBoundary period hPeriod) :
    ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates :=
  (normalBoundaryOrientationTangentEquiv period hPeriod
    boundary).symm.toLinearEquiv

def normalGraphCanonicalHolonomicGaussShapeEndomorphismAt
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    TangentSpace throatCoverModelWithCorners boundary →ₗ[Real]
      TangentSpace throatCoverModelWithCorners boundary := by
  change ThroatCoverCoordinates →ₗ[Real] ThroatCoverCoordinates
  let transport :=
    normalBoundaryOrientationCoordinateEquiv period hPeriod boundary
  exact (transport.toLinearMap.comp
      (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period
        hPeriod variedMetric displacement parameter boundary patch coordinate)).comp
    transport.symm.toLinearMap

private theorem throatCoverCoordinates_trace_conj
    (targetShape : ThroatCoverCoordinates →ₗ[Real] ThroatCoverCoordinates)
    (e : ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates) :
    LinearMap.trace Real ThroatCoverCoordinates (e.conj targetShape) =
      LinearMap.trace Real ThroatCoverCoordinates targetShape := by
  exact LinearMap.trace_conj' targetShape e

set_option backward.isDefEq.respectTransparency false in
private theorem normalGraphCanonicalHolonomicGaussShape_trace_eq_target
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners boundary)
        (normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
          variedMetric displacement parameter hNonNull boundary patch
            coordinate hAt) =
      LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod boundary))
        (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period
          hPeriod variedMetric displacement parameter boundary patch
            coordinate) := by
  unfold normalGraphCanonicalHolonomicGaussShapeEndomorphismAt
  change LinearMap.trace Real ThroatCoverCoordinates
      ((normalBoundaryOrientationCoordinateEquiv period hPeriod
        boundary).conj
          (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period
            hPeriod variedMetric displacement parameter boundary patch
              coordinate)) =
    LinearMap.trace Real ThroatCoverCoordinates
    (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter boundary patch coordinate)
  exact throatCoverCoordinates_trace_conj
    (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter boundary patch coordinate)
    (normalBoundaryOrientationCoordinateEquiv period hPeriod boundary)

set_option backward.isDefEq.respectTransparency false in
private theorem normalGraphCanonicalHolonomicGaussTargetShape_trace
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod boundary))
        (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period
          hPeriod variedMetric displacement parameter boundary patch
            coordinate) =
      normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
        hPeriod variedMetric displacement boundary parameter patch coordinate
          (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  unfold normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt
  exact
    (normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eq_trace
      period hPeriod variedMetric displacement boundary parameter patch
        coordinate
          (orientationDoubleToThroat period hPeriod boundary, parameter)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic trace of the canonical source shape is exactly the
holonomic local mean curvature already used by the chart-free Gauss action. -/
theorem normalGraphCanonicalHolonomicGaussShapeEndomorphismAt_trace
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners boundary)
        (normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
          variedMetric displacement parameter hNonNull boundary patch
            coordinate hAt) =
      normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod
        variedMetric displacement base patch coordinate ambient base := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      variedMetric displacement parameter hNonNull boundary patch coordinate hAt
  calc
    LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners boundary)
        (normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
          variedMetric displacement parameter hNonNull boundary patch
            coordinate hAt) =
      LinearMap.trace Real
        (TangentSpace throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod boundary))
        (normalGraphCanonicalHolonomicGaussTargetShapeEndomorphismAt period
          hPeriod variedMetric displacement parameter boundary patch
            coordinate) :=
      normalGraphCanonicalHolonomicGaussShape_trace_eq_target period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    _ = normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
        hPeriod variedMetric displacement boundary parameter patch coordinate
          base :=
      normalGraphCanonicalHolonomicGaussTargetShape_trace period hPeriod
        variedMetric displacement parameter boundary patch coordinate
    _ = normalGraphCanonicalGaussMeanCurvature period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
      exact
        normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_base_eq_gauss
          period hPeriod variedMetric displacement parameter hNonNull boundary
            patch coordinate hAt
    _ = normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod
        variedMetric displacement base patch coordinate ambient base := by
      exact
        (normalGraphCanonicalHolonomicLocalMeanCurvatureFamily_base_eq_gauss
          period hPeriod variedMetric displacement parameter hNonNull boundary
            patch coordinate hAt).symm

/-- Residual H10 encoding statement after the canonical shape and its trace
have been constructed.  It asks only that the historical redundant matrix is
the faithful encoding of `(g₀⁻¹h) ∘ (h⁻¹K)`. -/
def CandidateANormalBoundaryHistoricalGaussEncodingAgreement
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
        (boundary, parameter)),
    let frame := finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    let relative := normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
      variedMetric displacement parameter boundary
    let shape :=
      normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
        variedMetric displacement parameter hNonNull boundary patch coordinate
          hAt
    candidateANormalBoundaryHistoricalWeingartenRelativeEndomorphismMatrixAt
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull boundary =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        frame boundary (relative.toLinearMap.comp shape)

/-- The reduced encoding statement supplies the former existential
factorization, with the canonical shape operator as its unique witness. -/
theorem candidateANormalBoundaryHistoricalIntrinsicTraceFactorization_of_encodingAgreement
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hEncoding : CandidateANormalBoundaryHistoricalGaussEncodingAgreement
      period hPeriod metric tensor variedMetric displacement parameter
        hNonNull) :
    CandidateANormalBoundaryHistoricalIntrinsicTraceFactorization period
      hPeriod metric tensor variedMetric displacement parameter hNonNull := by
  intro boundary patch coordinate hAt
  dsimp only
  let shape :=
    normalGraphCanonicalHolonomicGaussShapeEndomorphismAt period hPeriod
      variedMetric displacement parameter hNonNull boundary patch coordinate hAt
  refine ⟨shape, ?_, ?_⟩
  · unfold CandidateANormalBoundaryHistoricalGaussEncodingAgreement at hEncoding
    have hEncodingAt := hEncoding boundary patch coordinate hAt
    simpa [shape] using hEncodingAt
  · simpa [shape] using
      (normalGraphCanonicalHolonomicGaussShapeEndomorphismAt_trace period
        hPeriod variedMetric displacement parameter hNonNull boundary patch
          coordinate hAt)

/-- Consequently the residual encoding statement already implies the
chart-free historical/Gauss trace agreement consumed by the action bridge. -/
theorem candidateANormalBoundaryHistoricalGaussTraceAgreement_of_encodingAgreement
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
    (hEncoding : CandidateANormalBoundaryHistoricalGaussEncodingAgreement
      period hPeriod metric tensor variedMetric displacement parameter
        hNonNull) :
    CandidateANormalBoundaryHistoricalGaussTraceAgreement period hPeriod metric
      tensor variedMetric displacement parameter hNonNull :=
  candidateANormalBoundaryHistoricalGaussTraceAgreement_of_intrinsicFactorization
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      hNonNull hCurrent
      (candidateANormalBoundaryHistoricalIntrinsicTraceFactorization_of_encodingAgreement
        period hPeriod metric tensor variedMetric displacement parameter
          hNonNull hEncoding)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
