import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixLinearEquivLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterLocalRoot4D

/-!
# Intrinsic Candidate-A Sylvester regularity on the uniform C² corner

The already proved smooth extended Sylvester field is lifted to the uniform
C² matrix core.  Dense smooth agreement identifies it with the explicit
projector-corner operator.  Intrinsic pointwise regularity then gives a
bijective Sylvester derivative on the complete C² corner and activates the
existing open-domain Banach inverse-function theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixLinearEquivLift4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2FrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  C2FiniteMatrix period hPeriod frame.count

private abbrev SmoothFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D.SmoothFiniteMatrix
    period hPeriod frame.count

private abbrev MatrixN (dimension : Nat) :=
  Matrix (Fin dimension) (Fin dimension) Real

@[reducible] local instance finiteMatrixNormedAddCommGroup (dimension : Nat) :
    NormedAddCommGroup (MatrixN dimension) :=
  Matrix.normedAddCommGroup

@[reducible] local instance finiteMatrixNormedSpace (dimension : Nat) :
    NormedSpace Real (MatrixN dimension) :=
  Matrix.normedSpace

local instance finiteMatrixOperatorNormedAddCommGroup (dimension : Nat) :
    NormedAddCommGroup (MatrixN dimension →L[Real] MatrixN dimension) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance finiteMatrixOperatorNormedSpace (dimension : Nat) :
    NormedSpace Real (MatrixN dimension →L[Real] MatrixN dimension) :=
  ContinuousLinearMap.toNormedSpace

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance c2FiniteFrameCornerNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (C2FiniteFrameCorner period hPeriod frame metric) :=
  (c2FiniteFrameCornerSubmodule
    period hPeriod frame metric).normedAddCommGroup

local instance c2FiniteFrameCornerNormedSpace
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (C2FiniteFrameCorner period hPeriod frame metric) :=
  inferInstance

local instance c2FiniteFrameCornerCompleteSpaceInstance
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (C2FiniteFrameCorner period hPeriod frame metric) :=
  c2FiniteFrameCornerCompleteSpace period hPeriod frame metric

theorem c2FiniteFrameCornerProjection_smooth
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : SmoothFrameMatrix period hPeriod frame) :
    c2FiniteFrameCornerProjection period hPeriod frame metric
        (smoothFiniteMatrixToC2 period hPeriod frame.count variation) =
      smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameCornerProjectionApply
          period hPeriod frame metric variation) := by
  let projector := smoothFiniteFrameProjectorCoefficients
    period hPeriod frame metric
  let embed := smoothFiniteMatrixToC2 period hPeriod frame.count
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let smoothProduct :=
    P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D.smoothFiniteMatrixProduct
      period hPeriod frame.count
  calc
    c2FiniteFrameCornerProjection period hPeriod frame metric
          (embed variation) =
        product (c2FiniteFrameProjector period hPeriod frame metric)
          (product (embed variation)
            (c2FiniteFrameProjector period hPeriod frame metric)) :=
      c2FiniteFrameCornerProjection_apply
        period hPeriod frame metric (embed variation)
    _ = product (embed projector)
        (product (embed variation) (embed projector)) := rfl
    _ = product (embed projector)
        (embed (smoothProduct variation projector)) := by
      exact congrArg (product (embed projector))
        (c2FiniteMatrixProduct_smooth
          period hPeriod frame.count variation projector)
    _ = embed (smoothProduct projector
        (smoothProduct variation projector)) :=
      c2FiniteMatrixProduct_smooth
        period hPeriod frame.count projector (smoothProduct variation projector)
    _ = embed (smoothFiniteFrameCornerProjectionApply
        period hPeriod frame metric variation) := rfl

/-- Explicit C² realization of the extended Sylvester family. -/
def c2FiniteFrameExtendedSylvester
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    C2FrameMatrix period hPeriod frame →L[Real]
      C2FrameMatrix period hPeriod frame :=
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let corner := c2FiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  let root := c2GlobalCandidateAFiniteFrameRoot
    period hPeriod geometry frame
  (product root).comp corner +
    (product.flip root).comp corner +
    (ContinuousLinearMap.id Real
      (C2FrameMatrix period hPeriod frame) - corner)

@[simp]
theorem c2FiniteFrameExtendedSylvester_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (matrix : C2FrameMatrix period hPeriod frame) :
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame matrix =
      let corner := c2FiniteFrameCornerProjection
        period hPeriod frame geometry.plusMetric matrix
      c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) frame.count
            (c2GlobalCandidateAFiniteFrameRoot
              period hPeriod geometry frame) corner +
        c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) frame.count corner
            (c2GlobalCandidateAFiniteFrameRoot
              period hPeriod geometry frame) +
        (matrix - corner) :=
  rfl

theorem c2FiniteFrameExtendedSylvester_smooth
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : SmoothFrameMatrix period hPeriod frame) :
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame
        (smoothFiniteMatrixToC2 period hPeriod frame.count variation) =
      smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameExtendedSylvesterApply
          period hPeriod geometry frame variation) := by
  let rootSmooth := smoothGlobalCandidateAFiniteFrameRootCoefficients
    period hPeriod geometry frame
  let cornerSmooth := smoothFiniteFrameCornerProjectionApply
    period hPeriod frame geometry.plusMetric variation
  let embed := smoothFiniteMatrixToC2 period hPeriod frame.count
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let smoothProduct :=
    P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D.smoothFiniteMatrixProduct
      period hPeriod frame.count
  let corner := c2FiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  have hCorner : corner (embed variation) = embed cornerSmooth :=
    c2FiniteFrameCornerProjection_smooth
      period hPeriod frame geometry.plusMetric variation
  calc
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame
          (embed variation) =
        product (c2GlobalCandidateAFiniteFrameRoot
            period hPeriod geometry frame) (corner (embed variation)) +
          product (corner (embed variation))
            (c2GlobalCandidateAFiniteFrameRoot
              period hPeriod geometry frame) +
          (embed variation - corner (embed variation)) :=
      c2FiniteFrameExtendedSylvester_apply
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
          (c2FiniteMatrixProduct_smooth
            period hPeriod frame.count rootSmooth cornerSmooth)
    _ = embed (smoothProduct rootSmooth cornerSmooth) +
          embed (smoothProduct cornerSmooth rootSmooth) +
          (embed variation - embed cornerSmooth) := by
      exact congrArg (fun current =>
        embed (smoothProduct rootSmooth cornerSmooth) + current +
          (embed variation - embed cornerSmooth))
        (c2FiniteMatrixProduct_smooth
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

theorem c2FiniteMatrixOperator_eq_extendedSylvester
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    c2FiniteMatrixOperator period hPeriod frame.count
        (globalCandidateAFiniteFrameExtendedSylvesterField
          period hPeriod geometry frame) =
      c2FiniteFrameExtendedSylvester period hPeriod geometry frame := by
  apply c2FiniteMatrixOperator_eq_of_smooth
    period hPeriod frame.count
  intro smooth
  rw [c2FiniteFrameExtendedSylvester_smooth]
  exact congrArg (smoothFiniteMatrixToC2 period hPeriod frame.count)
    (smoothFiniteMatrixOperatorApply_extended
      period hPeriod geometry frame smooth).symm

def c2FiniteFrameExtendedSylvesterEquiv
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    C2FrameMatrix period hPeriod frame ≃L[Real]
      C2FrameMatrix period hPeriod frame :=
  c2FiniteMatrixOperatorEquiv period hPeriod frame.count
    (globalCandidateAFiniteFrameExtendedSylvesterField
      period hPeriod geometry frame)
    (globalCandidateAFiniteFrameExtendedSylvesterField_bijective
      period hPeriod geometry frame hRegular)

theorem c2FiniteFrameExtendedSylvesterEquiv_forward_eq
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    (c2FiniteFrameExtendedSylvesterEquiv
        period hPeriod geometry frame hRegular :
      C2FrameMatrix period hPeriod frame →L[Real]
        C2FrameMatrix period hPeriod frame) =
      c2FiniteFrameExtendedSylvester period hPeriod geometry frame := by
  calc
    (c2FiniteFrameExtendedSylvesterEquiv
          period hPeriod geometry frame hRegular :
        C2FrameMatrix period hPeriod frame →L[Real]
          C2FrameMatrix period hPeriod frame) =
        c2FiniteMatrixOperator period hPeriod frame.count
          (globalCandidateAFiniteFrameExtendedSylvesterField
            period hPeriod geometry frame) := rfl
    _ = c2FiniteFrameExtendedSylvester period hPeriod geometry frame :=
      c2FiniteMatrixOperator_eq_extendedSylvester
        period hPeriod geometry frame

theorem c2FiniteFrameCornerSylvester_value
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root variation : C2FiniteFrameCorner period hPeriod frame metric) :
    (c2FiniteFrameCornerSylvester
      period hPeriod frame metric root variation).1 =
      c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          root.1 variation.1 +
        c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          variation.1 root.1 := by
  let cornerProduct := c2FiniteFrameCornerProduct
    period hPeriod frame metric
  have hSylvesterDef :
      c2FiniteFrameCornerSylvester period hPeriod frame metric root =
        cornerProduct root +
          (cornerProduct.flip root :
            C2FiniteFrameCorner period hPeriod frame metric →L[Real]
              C2FiniteFrameCorner period hPeriod frame metric) := rfl
  have hAddApply :
      ((cornerProduct root +
          (cornerProduct.flip root :
            C2FiniteFrameCorner period hPeriod frame metric →L[Real]
              C2FiniteFrameCorner period hPeriod frame metric)) variation).1 =
        (cornerProduct root variation).1 +
          (cornerProduct variation root).1 := rfl
  calc
    (c2FiniteFrameCornerSylvester
          period hPeriod frame metric root variation).1 =
        ((cornerProduct root +
          (cornerProduct.flip root :
            C2FiniteFrameCorner period hPeriod frame metric →L[Real]
              C2FiniteFrameCorner period hPeriod frame metric)) variation).1 := by
      exact congrArg (fun operator :
        C2FiniteFrameCorner period hPeriod frame metric →L[Real]
          C2FiniteFrameCorner period hPeriod frame metric =>
        (operator variation).1) hSylvesterDef
    _ = (cornerProduct root variation).1 +
          (cornerProduct variation root).1 := hAddApply
    _ = c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          root.1 variation.1 +
        c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) frame.count
          variation.1 root.1 := by
      exact congrArg₂ (fun first second => first + second)
        (c2FiniteFrameCornerProduct_apply
          period hPeriod frame metric root variation)
        (c2FiniteFrameCornerProduct_apply
          period hPeriod frame metric variation root)

theorem c2FiniteFrameExtendedSylvester_corner
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (variation : C2FiniteFrameCorner
      period hPeriod frame geometry.plusMetric) :
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame variation.1 =
      (c2FiniteFrameCornerSylvester
        period hPeriod frame geometry.plusMetric
        (c2GlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) variation).1 := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let corner := c2FiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  let root := c2GlobalCandidateAFiniteFrameRoot
    period hPeriod geometry frame
  let rootCorner := c2GlobalCandidateAFiniteFrameRootCorner
    period hPeriod geometry frame
  have hVariation : corner variation.1 = variation.1 :=
    (c2FiniteFrameCorner_mem_iff
      period hPeriod frame geometry.plusMetric variation.1).mp variation.2
  calc
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame variation.1 =
        product root (corner variation.1) +
          product (corner variation.1) root +
          (variation.1 - corner variation.1) :=
      c2FiniteFrameExtendedSylvester_apply
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
    _ = (c2FiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric rootCorner variation).1 :=
      (c2FiniteFrameCornerSylvester_value
        period hPeriod frame geometry.plusMetric rootCorner variation).symm

theorem c2FiniteFrameExtendedSylvester_commutes_cornerProjection
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (matrix : C2FrameMatrix period hPeriod frame) :
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame
        (c2FiniteFrameCornerProjection
          period hPeriod frame geometry.plusMetric matrix) =
      c2FiniteFrameCornerProjection
        period hPeriod frame geometry.plusMetric
        (c2FiniteFrameExtendedSylvester
          period hPeriod geometry frame matrix) := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) frame.count
  let corner := c2FiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  let root := c2GlobalCandidateAFiniteFrameRoot
    period hPeriod geometry frame
  let rootCorner := c2GlobalCandidateAFiniteFrameRootCorner
    period hPeriod geometry frame
  let cornerMatrix : C2FiniteFrameCorner
      period hPeriod frame geometry.plusMetric :=
    ⟨corner matrix,
      c2FiniteFrameCornerProjection_mem
        period hPeriod frame geometry.plusMetric matrix⟩
  let left := product root (corner matrix)
  let right := product (corner matrix) root
  have hCornerCorner : corner (corner matrix) = corner matrix :=
    c2FiniteFrameCornerProjection_idempotent
      period hPeriod frame geometry.plusMetric matrix
  have hLeft : corner left = left :=
    (c2FiniteFrameCorner_mem_iff
      period hPeriod frame geometry.plusMetric left).mp
        (c2FiniteFrameCorner_product_mem
          period hPeriod frame geometry.plusMetric rootCorner cornerMatrix)
  have hRight : corner right = right :=
    (c2FiniteFrameCorner_mem_iff
      period hPeriod frame geometry.plusMetric right).mp
        (c2FiniteFrameCorner_product_mem
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
    c2FiniteFrameExtendedSylvester period hPeriod geometry frame
          (corner matrix) =
        product root (corner (corner matrix)) +
          product (corner (corner matrix)) root +
          (corner matrix - corner (corner matrix)) := by
      simpa only [product, root, corner] using
        c2FiniteFrameExtendedSylvester_apply
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
    _ = corner (c2FiniteFrameExtendedSylvester
          period hPeriod geometry frame matrix) := by
      have hApply :
          c2FiniteFrameExtendedSylvester period hPeriod geometry frame matrix =
            left + right + (matrix - corner matrix) := by
        simpa only [left, right, product, root, corner] using
          c2FiniteFrameExtendedSylvester_apply
            period hPeriod geometry frame matrix
      exact congrArg corner hApply.symm

/-- Intrinsic pointwise regularity gives bijectivity of the exact C² corner
Sylvester derivative. -/
theorem c2FiniteFrameCornerSylvester_bijective_of_intrinsic
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    Function.Bijective
      (c2FiniteFrameCornerSylvester
        period hPeriod frame geometry.plusMetric
        (c2GlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame)) := by
  let ambientEquiv := c2FiniteFrameExtendedSylvesterEquiv
    period hPeriod geometry frame hRegular
  let ambient := c2FiniteFrameExtendedSylvester
    period hPeriod geometry frame
  let corner := c2FiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  have hForward :
      (ambientEquiv : C2FrameMatrix period hPeriod frame →L[Real]
        C2FrameMatrix period hPeriod frame) = ambient :=
    c2FiniteFrameExtendedSylvesterEquiv_forward_eq
      period hPeriod geometry frame hRegular
  have hAmbientInjective : Function.Injective ambient := by
    intro first second hEqual
    apply ambientEquiv.injective
    have hFirst := congrArg (fun operator :
      C2FrameMatrix period hPeriod frame →L[Real]
        C2FrameMatrix period hPeriod frame => operator first) hForward
    have hSecond := congrArg (fun operator :
      C2FrameMatrix period hPeriod frame →L[Real]
        C2FrameMatrix period hPeriod frame => operator second) hForward
    exact hFirst.trans (hEqual.trans hSecond.symm)
  constructor
  · intro first second hEqual
    apply Subtype.ext
    apply hAmbientInjective
    have hFirst := c2FiniteFrameExtendedSylvester_corner
      period hPeriod geometry frame first
    have hSecond := c2FiniteFrameExtendedSylvester_corner
      period hPeriod geometry frame second
    exact hFirst.trans ((congrArg Subtype.val hEqual).trans hSecond.symm)
  · intro target
    obtain ⟨preimage, hPreimage⟩ := ambientEquiv.surjective target.1
    have hAtPreimage := congrArg (fun operator :
      C2FrameMatrix period hPeriod frame →L[Real]
        C2FrameMatrix period hPeriod frame => operator preimage) hForward
    have hAmbient : ambient preimage = target.1 :=
      hAtPreimage.symm.trans hPreimage
    have hTargetCorner : corner target.1 = target.1 :=
      (c2FiniteFrameCorner_mem_iff
        period hPeriod frame geometry.plusMetric target.1).mp target.2
    have hSameOutput : ambient (corner preimage) = ambient preimage := by
      calc
        ambient (corner preimage) = corner (ambient preimage) :=
          c2FiniteFrameExtendedSylvester_commutes_cornerProjection
            period hPeriod geometry frame preimage
        _ = corner target.1 := congrArg corner hAmbient
        _ = target.1 := hTargetCorner
        _ = ambient preimage := hAmbient.symm
    have hPreimageCorner : corner preimage = preimage :=
      hAmbientInjective hSameOutput
    have hPreimageMem : preimage ∈ c2FiniteFrameCornerSubmodule
        period hPeriod frame geometry.plusMetric :=
      (c2FiniteFrameCorner_mem_iff
        period hPeriod frame geometry.plusMetric preimage).mpr hPreimageCorner
    let source : C2FiniteFrameCorner
        period hPeriod frame geometry.plusMetric :=
      ⟨preimage, hPreimageMem⟩
    refine ⟨source, ?_⟩
    apply Subtype.ext
    have hRestriction := c2FiniteFrameExtendedSylvester_corner
      period hPeriod geometry frame source
    exact hRestriction.symm.trans hAmbient

def c2FiniteFrameCornerSylvesterEquivOfBijective
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : C2FiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (c2FiniteFrameCornerSylvester period hPeriod frame metric root)) :
    C2FiniteFrameCorner period hPeriod frame metric ≃L[Real]
      C2FiniteFrameCorner period hPeriod frame metric :=
  ContinuousLinearEquiv.ofBijective
    (c2FiniteFrameCornerSylvester period hPeriod frame metric root)
    (LinearMap.ker_eq_bot.mpr hRegular.1)
    (LinearMap.range_eq_top.mpr hRegular.2)

theorem c2FiniteFrameCornerSylvesterEquiv_forward_eq
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : C2FiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (c2FiniteFrameCornerSylvester period hPeriod frame metric root)) :
    (c2FiniteFrameCornerSylvesterEquivOfBijective
        period hPeriod frame metric root hRegular :
      C2FiniteFrameCorner period hPeriod frame metric →L[Real]
        C2FiniteFrameCorner period hPeriod frame metric) =
      c2FiniteFrameCornerSylvester period hPeriod frame metric root :=
  rfl

def c2FiniteFrameCornerSylvesterFamily
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    C2FiniteFrameCorner period hPeriod frame metric →
      C2FiniteFrameCorner period hPeriod frame metric →L[Real]
        C2FiniteFrameCorner period hPeriod frame metric :=
  fun root => c2FiniteFrameCornerSylvester
    period hPeriod frame metric root

theorem c2FiniteFrameCornerSylvesterFamily_continuous
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Continuous (c2FiniteFrameCornerSylvesterFamily
      period hPeriod frame metric) := by
  change Continuous (fun root =>
    c2FiniteFrameCornerProduct period hPeriod frame metric root +
      (c2FiniteFrameCornerProduct
        period hPeriod frame metric).flip root)
  exact (c2FiniteFrameCornerProduct
    period hPeriod frame metric).continuous.add
      (c2FiniteFrameCornerProduct
        period hPeriod frame metric).flip.continuous

theorem c2FiniteFrameCornerSquare_contDiff_two
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (c2FiniteFrameCornerSquare period hPeriod frame metric) :=
  (c2FiniteFrameCornerSquare_contDiff period hPeriod frame metric).of_le
    (by norm_num)

/-- Final intrinsic C² local-root branch on the complete finite-frame corner. -/
def globalCandidateAC2FiniteFrameLocalRootBranch
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    LocalC2InverseOpenBranch
      (C2FiniteFrameCorner period hPeriod frame geometry.plusMetric)
      (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric)
      (c2GlobalCandidateAFiniteFrameRootCorner
        period hPeriod geometry frame) :=
  let root := c2GlobalCandidateAFiniteFrameRootCorner
    period hPeriod geometry frame
  let hCornerRegular := c2FiniteFrameCornerSylvester_bijective_of_intrinsic
    period hPeriod geometry frame hRegular
  let equiv := c2FiniteFrameCornerSylvesterEquivOfBijective
    period hPeriod frame geometry.plusMetric root hCornerRegular
  regularLocalC2InverseOpenBranch
    (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric) root
    (c2FiniteFrameCornerSylvesterFamily
      period hPeriod frame geometry.plusMetric)
    equiv
    (c2FiniteFrameCornerSylvesterEquiv_forward_eq
      period hPeriod frame geometry.plusMetric root hCornerRegular)
    (c2FiniteFrameCornerSquare_contDiff_two
      period hPeriod frame geometry.plusMetric)
    (c2FiniteFrameCornerSquare_hasFDerivAt
      period hPeriod frame geometry.plusMetric)
    (c2FiniteFrameCornerSylvesterFamily_continuous
      period hPeriod frame geometry.plusMetric)

theorem global_candidate_a_c2_finite_frame_sylvester_local_root_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    IsOpen (globalCandidateAC2FiniteFrameLocalRootBranch
        period hPeriod geometry frame hRegular).domain ∧
      (0 : C2FiniteFrameCorner
        period hPeriod frame geometry.plusMetric) ∈
        (globalCandidateAC2FiniteFrameLocalRootBranch
          period hPeriod geometry frame hRegular).domain ∧
      ContDiffOn Real 2
        (globalCandidateAC2FiniteFrameLocalRootBranch
          period hPeriod geometry frame hRegular).branch
        (globalCandidateAC2FiniteFrameLocalRootBranch
          period hPeriod geometry frame hRegular).domain ∧
      ∀ variation,
        variation ∈ (globalCandidateAC2FiniteFrameLocalRootBranch
            period hPeriod geometry frame hRegular).domain →
          c2FiniteFrameCornerSquare
              period hPeriod frame geometry.plusMetric
              ((globalCandidateAC2FiniteFrameLocalRootBranch
                period hPeriod geometry frame hRegular).branch variation) =
            c2FiniteFrameCornerSquare
                period hPeriod frame geometry.plusMetric
                (c2GlobalCandidateAFiniteFrameRootCorner
                  period hPeriod geometry frame) + variation := by
  let branch := globalCandidateAC2FiniteFrameLocalRootBranch
    period hPeriod geometry frame hRegular
  exact ⟨branch.domain_isOpen, branch.zero_mem_domain,
    branch.branch_contDiffOn, branch.branch_rightInverse⟩

end

end P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameSylvesterLocalRoot4D
end JanusFormal
