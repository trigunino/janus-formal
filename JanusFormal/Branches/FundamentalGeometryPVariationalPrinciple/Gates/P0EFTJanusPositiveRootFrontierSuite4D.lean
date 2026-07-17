import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalRootFrontierControl4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanMovingShearCollisionFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanDoubleCollisionZeroFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanSingularMovingSimilarityFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanTypeChangeFrontier4D

/-!
# Retained explicit positive-root frontier suite

This gate packages the explicit frontier families proved by the preceding
gates.  It records diagonal zero/infinity control, the canonical, fixed and
moving-shear Jordan obstructions, the double collision, the singular-frame
finite extension, and the two displayed Jordan-type changes.

This is an explicit retained suite, not a classification of arbitrary paths,
moving similarities, or Jordan types.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRootFrontierSuite4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D
open P0EFTJanusPositiveJordanCollisionZeroFrontier4D
open P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D
open P0EFTJanusPositiveJordanMovingShearCollisionFrontier4D
open P0EFTJanusPositiveJordanDoubleCollisionZeroFrontier4D
open P0EFTJanusPositiveJordanSingularMovingSimilarityFrontier4D
open P0EFTJanusPositiveJordanTypeChangeFrontier4D

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

/-- The two coordinate faces of the diagonal root have respectively zero and
infinite principal-root limits, while the root extends on the closed
numerator face. -/
def DiagonalZeroInfinityControl : Prop :=
  ContinuousOn principalRoot minusClosedDiagonalDomain ∧
    ∀ point ∈ globalDiagonalLorentzDomain, ∀ i,
      Tendsto
          (fun t => principalRootSpectrum
            (minusCoordinateApproach point i t) i)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Tendsto
          (fun t => principalRootSpectrum
            (plusCoordinateApproach point i t) i)
          (nhdsWithin 0 (Set.Ioi 0)) atTop

def CanonicalJordanNoExtension : Prop :=
  ¬ ∃ extension : Real → Matrix4,
      ContinuousAt extension 0 ∧
        ∀ parameter, 0 < parameter →
          extension parameter = jordanCollisionRoot parameter

def FixedJordanNoExtension : Prop :=
  ∀ data : FixedSimilarity4,
    ¬ ∃ extension : Real → Matrix4,
        ContinuousAt extension 0 ∧
          ∀ parameter, 0 < parameter →
            extension parameter = similarJordanCollisionRoot data parameter

def MovingShearJordanNoExtension : Prop :=
  ¬ ∃ extension : Real → Matrix4,
      ContinuousAt extension 0 ∧
        ∀ parameter, 0 < parameter →
          extension parameter = movingShearCollisionRoot parameter

def DoubleJordanNoExtension : Prop :=
  ¬ ∃ extension : (Real × Real) → Matrix4,
      ContinuousAt extension (0, 0) ∧
        ∀ first second, 0 < first → 0 < second →
          extension (first, second) =
            doubleJordanCollisionRoot first second

/-- A singular moving frame retains a finite root extension precisely while
its inverse frame blows up and has no finite limit. -/
def SingularMovingFiniteExtensionWithInverseBlowup : Prop :=
  (∃ extension : Real → Matrix4,
      ContinuousAt extension 0 ∧
        ∀ (parameter : Real) (hParameter : 0 < parameter),
          extension parameter =
            (singularMovingSimilarity parameter hParameter.ne').conjugate
              (jordanCollisionRoot (parameter ^ 2))) ∧
    Tendsto (fun parameter : Real => singularMovingInverse parameter 0 0)
      (nhdsWithin 0 (Set.Ioi 0)) atTop ∧
    ∀ candidate : Matrix4,
      ¬ Tendsto singularMovingInverse (nhdsWithin 0 (Set.Ioi 0))
          (nhds candidate)

/-- The explicit regular type change is smooth, squares exactly, changes
semisimplicity at zero, and keeps its Jordan Sylvester mode regular. -/
def RegularJordanTypeChange : Prop :=
  ContDiff Real ⊤ typeChangeTarget ∧
    ContDiff Real ⊤ typeChangeRoot ∧
    (∀ parameter, typeChangeRoot parameter * typeChangeRoot parameter =
      typeChangeTarget parameter) ∧
    IsSemisimpleMatrix (typeChangeTarget 0) ∧
    (∀ {parameter}, parameter ≠ 0 →
      ¬ IsSemisimpleMatrix (typeChangeTarget parameter)) ∧
    ∀ parameter,
      sylvesterOperator (typeChangeRoot parameter) jordanMode =
        (2 : Real) • jordanMode

/-- The contrasting zero type change has a finite exact root, but its
displayed Sylvester eigenvalue collapses to zero. -/
def ZeroTypeChangeSylvesterDegeneration : Prop :=
  (∀ {parameter}, 0 ≤ parameter →
      zeroFrontierRoot parameter * zeroFrontierRoot parameter =
        zeroFrontierTarget parameter) ∧
    Continuous zeroFrontierRoot ∧
    Tendsto zeroFrontierRoot (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ parameter,
      sylvesterOperator (zeroFrontierRoot parameter) jordanMode =
        (2 * Real.sqrt parameter) • jordanMode) ∧
    Tendsto (fun parameter : Real => 2 * Real.sqrt parameter)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- A single proof-carrying package for the retained explicit frontier
families. -/
structure PositiveRootFrontierSuite : Prop where
  diagonal : DiagonalZeroInfinityControl
  canonicalJordan : CanonicalJordanNoExtension
  fixedJordan : FixedJordanNoExtension
  movingShearJordan : MovingShearJordanNoExtension
  doubleJordan : DoubleJordanNoExtension
  singularMoving : SingularMovingFiniteExtensionWithInverseBlowup
  regularTypeChange : RegularJordanTypeChange
  zeroTypeChange : ZeroTypeChangeSylvesterDegeneration

/-- The retained explicit positive-root frontier certificate. -/
def positiveRootFrontierCertificate : PositiveRootFrontierSuite where
  diagonal := by
    refine ⟨global_diagonal_root_frontier_control_closure.1, ?_⟩
    exact global_diagonal_root_frontier_control_closure.2.2.1
  canonicalJordan := jordanCollisionRoot_no_continuous_extension
  fixedJordan := fun data =>
    similarJordanCollisionRoot_no_continuous_extension data
  movingShearJordan := movingShearCollisionRoot_no_continuous_extension
  doubleJordan := doubleJordanCollisionRoot_no_continuous_extension
  singularMoving := by
    exact ⟨singularMovingCollisionRoot_exists_continuous_extension,
      singularMovingInverse_leadingEntry_tendsto_atTop,
      singularMovingInverse_no_finite_limit⟩
  regularTypeChange := by
    exact ⟨typeChangeTarget_contDiff, typeChangeRoot_contDiff,
      typeChangeRoot_square, typeChangeTarget_zero_semisimple,
      fun hParameter => typeChangeTarget_not_semisimple hParameter,
      typeChangeSylvester_mode⟩
  zeroTypeChange := by
    exact ⟨zeroFrontierRoot_square, zeroFrontierRoot_continuous,
      zeroFrontierRoot_tendsto_zero, zeroFrontierSylvester_mode,
      zeroFrontierSylvesterEigenvalue_tendsto_zero⟩

end

end P0EFTJanusPositiveRootFrontierSuite4D
end JanusFormal
