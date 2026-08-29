import Mathlib.Analysis.InnerProductSpace.l2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D

/-!
# Joint geometric L2 isometry for the primitive SpinC blocks

Blockwise Parseval and the exact sector, circle-mode and sphere-level
orthogonality theorems combine into one Hilbert-sum isometry.  Its range is
the closed span of the explicit geometric eigensection blocks.  Surjectivity
is therefore exactly the remaining joint-density statement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- One complete finite geometric spectral block. -/
structure PrimitiveSpinCGeometricL2BlockIndex where
  sphereLevel : Nat
  sector : NormalRootChoice
  circleMode : Int
deriving DecidableEq

/-- Euclidean multiplicity coefficients carried by one block. -/
abbrev PrimitiveSpinCGeometricL2BlockCoefficients
    (block : PrimitiveSpinCGeometricL2BlockIndex) :=
  EuclideanSpace Complex
    (Fin (primitiveSphereModeDegeneracy block.sphereLevel))

/-- The exact block Parseval map into the smooth geometric core. -/
def primitiveSpinCGeometricL2SmoothBlockIsometry
    (block : PrimitiveSpinCGeometricL2BlockIndex) :
    PrimitiveSpinCGeometricL2BlockCoefficients block →ₗᵢ[Complex]
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter :=
  primitiveSpinCGeometricL2OrthonormalBlockLinearIsometry
    period hPeriod block.sphereLevel block.sector block.circleMode

/-- The same block map in the independent geometric Hilbert completion. -/
def primitiveSpinCGeometricL2CompletedBlockIsometry
    (block : PrimitiveSpinCGeometricL2BlockIndex) :
    PrimitiveSpinCGeometricL2BlockCoefficients block →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  UniformSpace.Completion.toComplₗᵢ.comp
    (primitiveSpinCGeometricL2SmoothBlockIsometry
      period hPeriod block)

@[simp]
theorem primitiveSpinCGeometricL2CompletedBlockIsometry_apply
    (block : PrimitiveSpinCGeometricL2BlockIndex)
    (coefficients : PrimitiveSpinCGeometricL2BlockCoefficients block) :
    primitiveSpinCGeometricL2CompletedBlockIsometry
        period hPeriod block coefficients =
      (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
        period hPeriod block.sphereLevel block.sector block.circleMode
        coefficients :
          D9PrimitiveSpinCGeometricL2Completion
            period hPeriod .positiveQuarter) := by
  rfl

/-- Distinct complete blocks have mutually orthogonal images. -/
theorem primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily :
    OrthogonalFamily Complex
      PrimitiveSpinCGeometricL2BlockCoefficients
      (primitiveSpinCGeometricL2CompletedBlockIsometry
        period hPeriod) := by
  rintro ⟨firstLevel, firstSector, firstMode⟩
    ⟨secondLevel, secondSector, secondMode⟩ hBlocks first second
  simp only [
    primitiveSpinCGeometricL2CompletedBlockIsometry_apply,
    UniformSpace.Completion.inner_coe]
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel firstSector firstMode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel secondSector secondMode second) =
      0
  by_cases hSectors : firstSector = secondSector
  · subst secondSector
    by_cases hModes : firstMode = secondMode
    · subst secondMode
      have hLevels : firstLevel ≠ secondLevel := by
        intro hLevels
        subst secondLevel
        exact hBlocks rfl
      exact
        primitiveSpinCGeometricL2OrthonormalBlockSynthesis_level_orthogonal
          period hPeriod firstLevel secondLevel hLevels firstSector firstMode
          first second
    · exact
        primitiveSpinCGeometricL2OrthonormalBlockSynthesis_circleMode_orthogonal
          period hPeriod firstLevel secondLevel firstSector firstMode
          secondMode hModes first second
  · cases firstSector <;> cases secondSector
    · exact (hSectors rfl).elim
    · exact
        primitiveSpinCGeometricL2OrthonormalBlockSynthesis_sectors_orthogonal
          period hPeriod firstLevel secondLevel firstMode secondMode
          first second
    · have hForward :
          d9PrimitiveSpinCGeometricL2Pairing
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
                period hPeriod secondLevel .positiveQuarter secondMode second)
              (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
                period hPeriod firstLevel .negativeQuarter firstMode first) =
            0 :=
        primitiveSpinCGeometricL2OrthonormalBlockSynthesis_sectors_orthogonal
          period hPeriod secondLevel firstLevel secondMode firstMode
          second first
      rw [← d9PrimitiveSpinCGeometricL2Pairing_conj_symm
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel .positiveQuarter secondMode second)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel .negativeQuarter firstMode first),
        hForward]
      simp
    · exact (hSectors rfl).elim

/-- Hilbert direct sum of all normalized geometric block coefficients. -/
abbrev PrimitiveSpinCGeometricL2JointCoefficients :=
  lp PrimitiveSpinCGeometricL2BlockCoefficients 2

/-- Canonical isometric synthesis of every square-summable block packet into
the independently constructed geometric completion. -/
def primitiveSpinCGeometricL2JointSynthesis :
    PrimitiveSpinCGeometricL2JointCoefficients →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  (primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
    period hPeriod).linearIsometry

@[simp]
theorem primitiveSpinCGeometricL2JointSynthesis_single
    (block : PrimitiveSpinCGeometricL2BlockIndex)
    (coefficients : PrimitiveSpinCGeometricL2BlockCoefficients block) :
    primitiveSpinCGeometricL2JointSynthesis period hPeriod
        (lp.single 2 block coefficients) =
      primitiveSpinCGeometricL2CompletedBlockIsometry
        period hPeriod block coefficients := by
  exact
    (primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
      period hPeriod).linearIsometry_apply_single coefficients

/-- The range is exactly the closed span of the explicit finite blocks. -/
theorem primitiveSpinCGeometricL2JointSynthesis_range :
    LinearMap.range
        (primitiveSpinCGeometricL2JointSynthesis
          period hPeriod).toLinearMap =
      (⨆ block : PrimitiveSpinCGeometricL2BlockIndex,
        LinearMap.range
          (primitiveSpinCGeometricL2CompletedBlockIsometry
            period hPeriod block).toLinearMap).topologicalClosure := by
  exact
    (primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
      period hPeriod).range_linearIsometry

/-- Exact residual statement: the proved joint isometry is unitary precisely
when its range is dense in the completion of all smooth sections. -/
def PrimitiveSpinCGeometricL2JointDensity : Prop :=
  DenseRange
    (primitiveSpinCGeometricL2JointSynthesis period hPeriod)

theorem primitiveSpinCGeometricL2JointSynthesis_denseRange_iff_surjective :
    PrimitiveSpinCGeometricL2JointDensity period hPeriod ↔
      Function.Surjective
        (primitiveSpinCGeometricL2JointSynthesis period hPeriod) := by
  constructor
  · intro hDense
    have hClosed :
        IsClosed
          (Set.range
            (primitiveSpinCGeometricL2JointSynthesis period hPeriod)) :=
      (primitiveSpinCGeometricL2JointSynthesis period hPeriod).isometry
        |>.isUniformInducing.isComplete_range.isClosed
    have hClosure :
        closure
            (Set.range
              (primitiveSpinCGeometricL2JointSynthesis period hPeriod)) =
          Set.univ :=
      dense_iff_closure_eq.mp hDense
    have hRange :
        Set.range
            (primitiveSpinCGeometricL2JointSynthesis period hPeriod) =
          Set.univ := by
      rw [← hClosed.closure_eq, hClosure]
    exact Set.range_eq_univ.mp hRange
  · exact Function.Surjective.denseRange

/-- The resulting global unitary, requiring only the still-open density
theorem and no additional analytic structure. -/
def primitiveSpinCGeometricL2JointUnitary
    (hDensity :
      PrimitiveSpinCGeometricL2JointDensity period hPeriod) :
    PrimitiveSpinCGeometricL2JointCoefficients ≃ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  LinearIsometryEquiv.ofSurjective
    (primitiveSpinCGeometricL2JointSynthesis period hPeriod)
    ((primitiveSpinCGeometricL2JointSynthesis_denseRange_iff_surjective
      period hPeriod).mp hDensity)

/-- Assumption-free certificate for the global block isometry and its exact
closed range. -/
structure ProgramPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D where
  blocksOrthogonal :
    OrthogonalFamily Complex
      PrimitiveSpinCGeometricL2BlockCoefficients
      (primitiveSpinCGeometricL2CompletedBlockIsometry period hPeriod)
  jointRange :
    LinearMap.range
        (primitiveSpinCGeometricL2JointSynthesis
          period hPeriod).toLinearMap =
      (⨆ block : PrimitiveSpinCGeometricL2BlockIndex,
        LinearMap.range
          (primitiveSpinCGeometricL2CompletedBlockIsometry
            period hPeriod block).toLinearMap).topologicalClosure

def programPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D
      period hPeriod where
  blocksOrthogonal :=
    primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
      period hPeriod
  jointRange :=
    primitiveSpinCGeometricL2JointSynthesis_range period hPeriod

theorem primitiveSpinCGeometricL2JointIsometry_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2JointIsometryCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D
end JanusFormal
