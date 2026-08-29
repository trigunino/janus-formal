import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterLocalRoot4D

/-!
# Candidate-A Sylvester regularity on the strong corner

The ambient finite-matrix equivalence is restricted to the complete projector
corner.  Intrinsic pointwise Sylvester regularity then supplies the exact
regularity hypothesis required by the existing local `C²` root gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterCornerLocalRoot4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
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
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterLocalRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev StrongFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  StrongFiniteMatrix period hPeriod frame.count

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

theorem strongFiniteFrameCornerSylvester_value
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root variation : StrongFiniteFrameCorner period hPeriod frame metric) :
    (strongFiniteFrameCornerSylvester
      period hPeriod frame metric root variation).1 =
      strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          root.1 variation.1 +
        strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          variation.1 root.1 := by
  let cornerProduct := strongFiniteFrameCornerProduct
    period hPeriod frame metric
  have hSylvesterDef :
      strongFiniteFrameCornerSylvester period hPeriod frame metric root =
        cornerProduct root +
          (cornerProduct.flip root :
            StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
              StrongFiniteFrameCorner period hPeriod frame metric) := rfl
  have hAddApply :
      ((cornerProduct root +
          (cornerProduct.flip root :
            StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
              StrongFiniteFrameCorner period hPeriod frame metric)) variation).1 =
        (cornerProduct root variation).1 +
          (cornerProduct variation root).1 := rfl
  calc
    (strongFiniteFrameCornerSylvester
          period hPeriod frame metric root variation).1 =
        ((cornerProduct root +
          (cornerProduct.flip root :
            StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
              StrongFiniteFrameCorner period hPeriod frame metric)) variation).1 := by
      exact congrArg (fun operator :
        StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
          StrongFiniteFrameCorner period hPeriod frame metric =>
        (operator variation).1) hSylvesterDef
    _ = (cornerProduct root variation).1 +
          (cornerProduct variation root).1 := hAddApply
    _ = strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          root.1 variation.1 +
        strongFiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          variation.1 root.1 := by
      exact congrArg₂ (fun first second => first + second)
        (strongFiniteFrameCornerProduct_apply
          period hPeriod frame metric root variation)
        (strongFiniteFrameCornerProduct_apply
          period hPeriod frame metric variation root)

/-- The extended ambient operator restricts to the existing strong corner
Sylvester derivative. -/
theorem strongFiniteFrameExtendedSylvester_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : StrongFiniteFrameCorner
      period hPeriod frame geometry.plusMetric) :
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame
        variation.1 =
      (strongFiniteFrameCornerSylvester
        period hPeriod frame geometry.plusMetric
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) variation).1 := by
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let corner := strongFiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  let root := strongGlobalCandidateAFiniteFrameRoot
    period hPeriod geometry frame
  let rootCorner := strongGlobalCandidateAFiniteFrameRootCorner
    period hPeriod geometry frame
  have hVariation : corner variation.1 = variation.1 :=
    (strongFiniteFrameCorner_mem_iff
      period hPeriod frame geometry.plusMetric variation.1).mp variation.2
  calc
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame
          variation.1 =
        product root (corner variation.1) +
          product (corner variation.1) root +
          (variation.1 - corner variation.1) :=
      strongFiniteFrameExtendedSylvester_apply
        period hPeriod geometry frame variation.1
    _ = product root variation.1 + product variation.1 root +
          (variation.1 - variation.1) := by
      exact congrArg (fun current =>
        product root current + product current root +
          (variation.1 - current)) hVariation
    _ = product root variation.1 + product variation.1 root := by
      exact (congrArg (fun current =>
        product root variation.1 + product variation.1 root + current)
          (sub_self variation.1)).trans
        (add_zero (product root variation.1 + product variation.1 root))
    _ = (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric rootCorner variation).1 :=
      (strongFiniteFrameCornerSylvester_value
        period hPeriod frame geometry.plusMetric rootCorner variation).symm

/-- The extended Sylvester operator preserves the projector splitting. -/
theorem strongFiniteFrameExtendedSylvester_commutes_cornerProjection
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (matrix : StrongFrameMatrix period hPeriod frame) :
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame
        (strongFiniteFrameCornerProjection
          period hPeriod frame geometry.plusMetric matrix) =
      strongFiniteFrameCornerProjection
        period hPeriod frame geometry.plusMetric
        (strongFiniteFrameExtendedSylvester
          period hPeriod geometry frame matrix) := by
  let product := strongFiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let corner := strongFiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  let root := strongGlobalCandidateAFiniteFrameRoot
    period hPeriod geometry frame
  let rootCorner := strongGlobalCandidateAFiniteFrameRootCorner
    period hPeriod geometry frame
  let cornerMatrix : StrongFiniteFrameCorner
      period hPeriod frame geometry.plusMetric :=
    ⟨corner matrix,
      strongFiniteFrameCornerProjection_mem
        period hPeriod frame geometry.plusMetric matrix⟩
  let left := product root (corner matrix)
  let right := product (corner matrix) root
  have hCornerCorner : corner (corner matrix) = corner matrix :=
    strongFiniteFrameCornerProjection_idempotent
      period hPeriod frame geometry.plusMetric matrix
  have hLeft : corner left = left :=
    (strongFiniteFrameCorner_mem_iff
      period hPeriod frame geometry.plusMetric left).mp
        (strongFiniteFrameCorner_product_mem
          period hPeriod frame geometry.plusMetric rootCorner cornerMatrix)
  have hRight : corner right = right :=
    (strongFiniteFrameCorner_mem_iff
      period hPeriod frame geometry.plusMetric right).mp
        (strongFiniteFrameCorner_product_mem
          period hPeriod frame geometry.plusMetric cornerMatrix rootCorner)
  have hProjected :
      corner (left + right + (matrix - corner matrix)) = left + right := by
    calc
      corner (left + right + (matrix - corner matrix)) =
          corner (left + right) + corner (matrix - corner matrix) :=
        corner.map_add (left + right) (matrix - corner matrix)
      _ = (left + right) + (corner matrix - corner matrix) := by
        exact congrArg₂ (fun first second => first + second)
          ((corner.map_add left right).trans
            (congrArg₂ (fun first second => first + second) hLeft hRight))
          ((corner.map_sub matrix (corner matrix)).trans
            (congrArg₂ (fun first second => first - second)
              rfl hCornerCorner))
      _ = left + right := by
        exact (congrArg (fun current => left + right + current)
          (sub_self (corner matrix))).trans (add_zero (left + right))
  calc
    strongFiniteFrameExtendedSylvester period hPeriod geometry frame
          (corner matrix) =
        product root (corner (corner matrix)) +
          product (corner (corner matrix)) root +
          (corner matrix - corner (corner matrix)) :=
      by
        simpa only [product, root, corner] using
          strongFiniteFrameExtendedSylvester_apply
            period hPeriod geometry frame (corner matrix)
    _ = left + right + (corner matrix - corner matrix) := by
      simpa only [left, right] using
        congrArg (fun current =>
          product root current + product current root +
            (corner matrix - current)) hCornerCorner
    _ = left + right := by
      exact (congrArg (fun current => left + right + current)
        (sub_self (corner matrix))).trans (add_zero (left + right))
    _ = corner (left + right + (matrix - corner matrix)) := hProjected.symm
    _ = corner (strongFiniteFrameExtendedSylvester
          period hPeriod geometry frame matrix) := by
      have hApply :
          strongFiniteFrameExtendedSylvester period hPeriod geometry frame matrix =
            left + right + (matrix - corner matrix) := by
        simpa only [left, right, product, root, corner] using
          strongFiniteFrameExtendedSylvester_apply
            period hPeriod geometry frame matrix
      exact congrArg corner hApply.symm


end
end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterCornerLocalRoot4D
end JanusFormal
