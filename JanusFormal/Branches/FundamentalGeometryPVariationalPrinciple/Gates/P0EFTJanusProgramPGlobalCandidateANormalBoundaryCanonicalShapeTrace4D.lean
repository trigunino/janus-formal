import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalGaussTraceFactorization4D

/-!
# Canonical shape trace for the completed Candidate-A boundary

This gate removes the trace half of the last H10 finite-frame witness.  The
intrinsic shape operator is defined from the already installed holonomic
matrix `h⁻¹ K`.  Its basis-independent linear trace is therefore exactly the
existing holonomic local mean curvature.

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

/-- A fixed three-dimensional basis of the throat tangent model.  It is used
only to turn the already existing holonomic `h⁻¹K` matrix into the intrinsic
shape endomorphism; the resulting trace is basis independent. -/
def candidateANormalBoundaryCanonicalTangentBasis
    (boundary : CutThroatBoundary period hPeriod) :
    Basis (Fin 3) Real
      (TangentSpace throatCoverModelWithCorners boundary) := by
  let basis := Module.finBasis Real
    (TangentSpace throatCoverModelWithCorners boundary)
  have hDimension : Module.finrank Real
      (TangentSpace throatCoverModelWithCorners boundary) = 3 := by
    change Module.finrank Real ThroatCoverCoordinates = 3
    simp [ThroatCoverCoordinates]
  simpa [hDimension] using basis

/-- Intrinsic shape operator represented in a holonomic throat chart by the
already installed matrix product `h⁻¹K`. -/
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
      TangentSpace throatCoverModelWithCorners boundary :=
  Matrix.toLin
    (candidateANormalBoundaryCanonicalTangentBasis period hPeriod boundary)
    (candidateANormalBoundaryCanonicalTangentBasis period hPeriod boundary)
    (normalGraphInducedInverseMatrix period hPeriod variedMetric displacement
        (orientationDoubleToThroat period hPeriod boundary, parameter) *
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt
        period hPeriod variedMetric displacement parameter hNonNull boundary
          patch coordinate hAt)

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic trace of the canonical shape operator is exactly the
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
  unfold normalGraphCanonicalHolonomicGaussShapeEndomorphismAt
    normalGraphCanonicalHolonomicLocalMeanCurvatureFamily
  rw [normalGraphInducedInverseMatrixFamily_base,
    normalGraphCanonicalHolonomicWeingartenMatrix_base_eq_gauss]
  exact Matrix.trace_toLin_eq
    (normalGraphInducedInverseMatrix period hPeriod variedMetric displacement
        (orientationDoubleToThroat period hPeriod boundary, parameter) *
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt
        period hPeriod variedMetric displacement parameter hNonNull boundary
          patch coordinate hAt)
    (candidateANormalBoundaryCanonicalTangentBasis period hPeriod boundary)

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
