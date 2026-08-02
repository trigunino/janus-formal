import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D

/-!
# Intrinsic Sylvester regularity and the local Candidate-A root chart

This gate transports pointwise intrinsic Sylvester regularity through the
redundant finite-frame model to the complete strong projector corner.  It then
activates the existing Banach inverse-function gate.  The result is a local
`C²` root chart on the regular stratum, without a global frame or a new
physical axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterLocalRoot4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev StrongFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  StrongFiniteMatrix period hPeriod frame.count

private abbrev MatrixN (dimension : Nat) :=
  Matrix (Fin dimension) (Fin dimension) Real

@[reducible] local instance matrixNNormedAddCommGroup (dimension : Nat) :
    NormedAddCommGroup (MatrixN dimension) :=
  Matrix.normedAddCommGroup

@[reducible] local instance matrixNNormedSpace (dimension : Nat) :
    NormedSpace Real (MatrixN dimension) :=
  Matrix.normedSpace

local instance matrixNOperatorNormedAddCommGroup (dimension : Nat) :
    NormedAddCommGroup (MatrixN dimension →L[Real] MatrixN dimension) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance matrixNOperatorNormedSpace (dimension : Nat) :
    NormedSpace Real (MatrixN dimension →L[Real] MatrixN dimension) :=
  ContinuousLinearMap.toNormedSpace

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

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

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

local instance strongFiniteFrameCornerNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (StrongFiniteFrameCorner period hPeriod frame metric) :=
  (strongFiniteFrameCornerSubmodule
    period hPeriod frame metric).normedAddCommGroup

local instance strongFiniteFrameCornerNormedSpace
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (StrongFiniteFrameCorner period hPeriod frame metric) :=
  inferInstance

local instance strongFiniteFrameCornerCompleteSpaceInstance
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (StrongFiniteFrameCorner period hPeriod frame metric) :=
  strongFiniteFrameCornerCompleteSpace period hPeriod frame metric

/-- The strong corner projection agrees with its smooth matrix formula on the
dense smooth core. -/
theorem strongFiniteFrameCornerProjection_smooth
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count) :
    strongFiniteFrameCornerProjection period hPeriod frame metric
        (smoothFiniteMatrixToStrong period hPeriod frame.count variation) =
      smoothFiniteMatrixToStrong period hPeriod frame.count
        (smoothFiniteFrameCornerProjectionApply
          period hPeriod frame metric variation) := by
  let projector := smoothFiniteFrameProjectorCoefficients
    period hPeriod frame metric
  let embed := smoothFiniteMatrixToStrong period hPeriod frame.count
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let smoothProduct := smoothFiniteMatrixProduct
    period hPeriod frame.count
  calc
    strongFiniteFrameCornerProjection period hPeriod frame metric
          (embed variation) =
        product (strongFiniteFrameProjector period hPeriod frame metric)
          (product (embed variation)
            (strongFiniteFrameProjector period hPeriod frame metric)) :=
      strongFiniteFrameCornerProjection_apply
        period hPeriod frame metric (embed variation)
    _ = product (embed projector)
        (product (embed variation) (embed projector)) := rfl
    _ = product (embed projector)
        (embed (smoothProduct variation projector)) := by
      exact congrArg (product (embed projector))
        (strongFiniteMatrixProduct_smooth
          period hPeriod frame.count variation projector)
    _ = embed (smoothProduct projector
        (smoothProduct variation projector)) :=
      strongFiniteMatrixProduct_smooth
        period hPeriod frame.count projector (smoothProduct variation projector)
    _ = embed (smoothFiniteFrameCornerProjectionApply
        period hPeriod frame metric variation) := rfl

/-- The explicit strong extended Sylvester operator agrees with the smooth
coefficient formula on the dense smooth core. -/
theorem strongFiniteFrameExtendedSylvester_smooth
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : SmoothFiniteMatrix period hPeriod frame.count) :
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame
        (smoothFiniteMatrixToStrong period hPeriod frame.count variation) =
      smoothFiniteMatrixToStrong period hPeriod frame.count
        (smoothFiniteFrameExtendedSylvesterApply
          period hPeriod geometry frame variation) := by
  let rootSmooth := smoothGlobalCandidateAFiniteFrameRootCoefficients
    period hPeriod geometry frame
  let cornerSmooth := smoothFiniteFrameCornerProjectionApply
    period hPeriod frame geometry.plusMetric variation
  let embed := smoothFiniteMatrixToStrong period hPeriod frame.count
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let smoothProduct := smoothFiniteMatrixProduct
    period hPeriod frame.count
  let corner := strongFiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  have hCorner : corner (embed variation) = embed cornerSmooth :=
    strongFiniteFrameCornerProjection_smooth
      period hPeriod frame geometry.plusMetric variation
  calc
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame
          (embed variation) =
        product (strongGlobalCandidateAFiniteFrameRoot
            period hPeriod geometry frame) (corner (embed variation)) +
          product (corner (embed variation))
            (strongGlobalCandidateAFiniteFrameRoot
              period hPeriod geometry frame) +
          (embed variation - corner (embed variation)) :=
      strongFiniteFrameExtendedSylvester_apply
        period hPeriod geometry frame (embed variation)
    _ = product (embed rootSmooth) (corner (embed variation)) +
          product (corner (embed variation)) (embed rootSmooth) +
          (embed variation - corner (embed variation)) := rfl
    _ = product (embed rootSmooth) (embed cornerSmooth) +
          product (embed cornerSmooth) (embed rootSmooth) +
          (embed variation - embed cornerSmooth) := by
      exact congrArg (fun current =>
        product (embed rootSmooth) current +
          product current (embed rootSmooth) +
          (embed variation - current)) hCorner
    _ = embed (smoothProduct rootSmooth cornerSmooth) +
          product (embed cornerSmooth) (embed rootSmooth) +
          (embed variation - embed cornerSmooth) := by
      exact congrArg (fun current => current +
        product (embed cornerSmooth) (embed rootSmooth) +
        (embed variation - embed cornerSmooth))
          (strongFiniteMatrixProduct_smooth
            period hPeriod frame.count rootSmooth cornerSmooth)
    _ = embed (smoothProduct rootSmooth cornerSmooth) +
          embed (smoothProduct cornerSmooth rootSmooth) +
          (embed variation - embed cornerSmooth) := by
      exact congrArg (fun current =>
        embed (smoothProduct rootSmooth cornerSmooth) + current +
          (embed variation - embed cornerSmooth))
        (strongFiniteMatrixProduct_smooth
          period hPeriod frame.count cornerSmooth rootSmooth)
    _ = embed (smoothProduct rootSmooth cornerSmooth +
          smoothProduct cornerSmooth rootSmooth) +
          embed (variation - cornerSmooth) := by
      exact congrArg₂ (fun first second => first + second)
        (embed.map_add
          (smoothProduct rootSmooth cornerSmooth)
          (smoothProduct cornerSmooth rootSmooth)).symm
        (embed.map_sub variation cornerSmooth).symm
    _ = embed (smoothProduct rootSmooth cornerSmooth +
          smoothProduct cornerSmooth rootSmooth +
          (variation - cornerSmooth)) :=
      (embed.map_add
        (smoothProduct rootSmooth cornerSmooth +
          smoothProduct cornerSmooth rootSmooth)
        (variation - cornerSmooth)).symm
    _ = embed (smoothFiniteFrameExtendedSylvesterApply
          period hPeriod geometry frame variation) := rfl

/-- Two bounded strong matrix operators that agree on the smooth core agree
everywhere. -/
theorem strongFiniteMatrixOperator_eq_of_smooth
    (dimension : Nat)
    (field : SmoothQuotientField period hPeriod
      (MatrixN dimension →L[Real] MatrixN dimension))
    (target : StrongFiniteMatrix period hPeriod dimension →L[Real]
      StrongFiniteMatrix period hPeriod dimension)
    (hCore : ∀ smooth : SmoothFiniteMatrix period hPeriod dimension,
      target (smoothFiniteMatrixToStrong period hPeriod dimension smooth) =
        smoothFiniteMatrixToStrong period hPeriod dimension
          (smoothFiniteMatrixOperatorApply
            period hPeriod dimension field smooth)) :
    strongFiniteMatrixOperator period hPeriod dimension field = target := by
  let abstract := strongFiniteMatrixOperator period hPeriod dimension field
  apply ContinuousLinearMap.ext
  intro matrix
  change abstract matrix = target matrix
  refine DenseRange.induction_on
    (smoothFiniteMatrixToStrong_denseRange period hPeriod dimension) matrix
    (isClosed_eq abstract.continuous target.continuous) ?_
  intro smooth
  rw [show abstract
      (smoothFiniteMatrixToStrong period hPeriod dimension smooth) =
      smoothFiniteMatrixToStrong period hPeriod dimension
        (smoothFiniteMatrixOperatorApply
          period hPeriod dimension field smooth) from
    strongFiniteMatrixOperator_smooth
      period hPeriod dimension field smooth]
  exact (hCore smooth).symm

theorem strongFiniteMatrixOperator_eq_extendedSylvester
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    strongFiniteMatrixOperator period hPeriod frame.count
        (globalCandidateAFiniteFrameExtendedSylvesterField
          period hPeriod geometry frame) =
      strongFiniteFrameExtendedSylvester period hPeriod geometry frame := by
  apply strongFiniteMatrixOperator_eq_of_smooth
    period hPeriod frame.count
  intro smooth
  rw [strongFiniteFrameExtendedSylvester_smooth]
  exact congrArg (smoothFiniteMatrixToStrong period hPeriod frame.count)
    (smoothFiniteMatrixOperatorApply_extended
      period hPeriod geometry frame smooth).symm

theorem strongFiniteFrameExtendedSylvesterEquiv_forward_eq
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    (strongFiniteFrameExtendedSylvesterEquiv
        period hPeriod geometry frame hRegular :
      StrongFrameMatrix period hPeriod frame →L[Real]
        StrongFrameMatrix period hPeriod frame) =
      strongFiniteFrameExtendedSylvester period hPeriod geometry frame := by
  calc
    (strongFiniteFrameExtendedSylvesterEquiv
          period hPeriod geometry frame hRegular :
        StrongFrameMatrix period hPeriod frame →L[Real]
          StrongFrameMatrix period hPeriod frame) =
        strongFiniteMatrixOperator period hPeriod frame.count
          (globalCandidateAFiniteFrameExtendedSylvesterField
            period hPeriod geometry frame) :=
      strongFiniteMatrixOperatorEquiv_forward_eq
        period hPeriod frame.count
          (globalCandidateAFiniteFrameExtendedSylvesterField
            period hPeriod geometry frame)
          (globalCandidateAFiniteFrameExtendedSylvesterField_bijective
            period hPeriod geometry frame hRegular)
    _ = strongFiniteFrameExtendedSylvester period hPeriod geometry frame :=
      strongFiniteMatrixOperator_eq_extendedSylvester
        period hPeriod geometry frame

end
end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterLocalRoot4D
end JanusFormal
