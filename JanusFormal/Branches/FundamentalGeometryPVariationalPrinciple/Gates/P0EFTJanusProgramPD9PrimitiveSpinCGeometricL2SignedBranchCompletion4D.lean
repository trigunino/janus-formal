import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D

/-!
# Geometric L² completion of each signed primitive SpinC branch

At every positive sphere level, root sector and circle mode, the genuine
smooth eigensections of one fixed Dirac sign span a finite-dimensional
complex subspace of the independently integrated geometric `L²` core.
This module chooses its canonical finite-dimensional orthonormal basis,
constructs the exact Parseval isometry into the geometric completion and
keeps the genuine first-order Dirac eigenvalue on the whole branch.

No orthogonality between the two opposite signs is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D

set_option autoImplicit false
noncomputable section

open InnerProductSpace
open Module
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- Complete signed coefficient label inside one fixed positive block. -/
def primitiveSpinCGeometricL2SignedBranchMode
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    PrimitiveSpinCGeometricSignedNonzeroMode :=
  (sector,
    { branch := branch
      level := positiveLevel
      multiplicity := multiplicity
      circleMode := circleMode })

/-- Genuine smooth family spanning one fixed signed branch. -/
def primitiveSpinCGeometricL2SignedBranchRawFamily
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    SmoothSection period hPeriod :=
  primitiveSpinCAllLevelSignedGeometricSection
    period hPeriod
    (primitiveSpinCGeometricL2SignedBranchMode
      positiveLevel branch sector circleMode multiplicity)

/-- Exact first-order eigenvalue shared by one signed multiplicity block. -/
def primitiveSpinCGeometricL2SignedBranchEigenvalue
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) : Complex :=
  ((primitiveSpinCDiracBranchSign branch *
      primitiveSpinCHarmonicDiracFrequency
        period positiveLevel sector circleMode : Real) : Complex)

/-- Every raw member satisfies the exact intrinsic first-order equation. -/
theorem primitiveSpinCGeometricL2SignedBranchRawFamily_dirac
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel branch sector circleMode
          multiplicity) =
      primitiveSpinCGeometricL2SignedBranchEigenvalue
          period positiveLevel branch sector circleMode •
        primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel branch sector circleMode
          multiplicity := by
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel branch sector circleMode
          multiplicity) =
      d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBranchEigenvalue
          period positiveLevel branch sector circleMode)
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel branch sector circleMode
          multiplicity)
  rw [primitiveSpinCGeometricL2SignedBranchEigenvalue,
    d9PrimitiveSpinCComplexScalarSection_ofReal]
  simpa [primitiveSpinCGeometricL2SignedBranchRawFamily,
    primitiveSpinCGeometricL2SignedBranchMode,
    primitiveSpinCGeometricSignedNonzeroEigenvalue,
    primitiveSpinCAllLevelSignedGeometricFrequency_eq] using
    primitiveSpinCAllLevelSignedGeometricSection_eigen
      period hPeriod
      (primitiveSpinCGeometricL2SignedBranchMode
        positiveLevel branch sector circleMode multiplicity)

/-- Complex span of one genuine signed multiplicity packet. -/
def primitiveSpinCGeometricL2SignedBranchBlock
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    Submodule Complex (SmoothSection period hPeriod) :=
  Submodule.span Complex
    (Set.range
      (primitiveSpinCGeometricL2SignedBranchRawFamily
        period hPeriod positiveLevel branch sector circleMode))

noncomputable instance primitiveSpinCGeometricL2SignedBranchBlock_finiteDimensional
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    FiniteDimensional Complex
      (primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel branch sector circleMode) :=
  FiniteDimensional.span_of_finite Complex
    (Set.finite_range
      (primitiveSpinCGeometricL2SignedBranchRawFamily
        period hPeriod positiveLevel branch sector circleMode))

/-- The whole complex branch span remains in the same first-order
eigenspace. -/
theorem primitiveSpinCGeometricL2SignedBranchBlock_le_eigenspace
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel branch sector circleMode ≤
      Module.End.eigenspace
        (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod)
        (primitiveSpinCGeometricL2SignedBranchEigenvalue
          period positiveLevel branch sector circleMode) := by
  rw [primitiveSpinCGeometricL2SignedBranchBlock, Submodule.span_le]
  rintro state ⟨multiplicity, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr
    (primitiveSpinCGeometricL2SignedBranchRawFamily_dirac
      period hPeriod positiveLevel branch sector circleMode multiplicity)

theorem primitiveSpinCGeometricL2SignedBranchBlock_dirac
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    {state : SmoothSection period hPeriod}
    (hState :
      state ∈
        primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode) :
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod state =
      primitiveSpinCGeometricL2SignedBranchEigenvalue
          period positiveLevel branch sector circleMode • state :=
  Module.End.mem_eigenspace_iff.mp
    (primitiveSpinCGeometricL2SignedBranchBlock_le_eigenspace
      period hPeriod positiveLevel branch sector circleMode hState)

/-- Squared eigenvalue common to the two opposite signed branches. -/
def primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) : Complex :=
  ((primitiveSpinCHarmonicDiracFrequency
      period positiveLevel sector circleMode ^ 2 : Real) : Complex)

/-- Every signed branch lies in the same genuine squared-Dirac block. -/
theorem primitiveSpinCGeometricL2SignedBranchBlock_dirac_sq
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    {state : SmoothSection period hPeriod}
    (hState :
      state ∈
        primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod state =
      primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
          period positiveLevel sector circleMode • state := by
  have hDirac :=
    primitiveSpinCGeometricL2SignedBranchBlock_dirac
      period hPeriod positiveLevel branch sector circleMode hState
  change
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (primitiveSpinCGeometricDiracComplexLinearMap period hPeriod state) =
      primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
          period positiveLevel sector circleMode • state
  rw [hDirac, map_smul, hDirac, smul_smul]
  congr 1
  cases branch <;>
    simp [primitiveSpinCGeometricL2SignedBranchEigenvalue,
      primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue,
      primitiveSpinCDiracBranchSign] <;>
    ring

/-- The two first-order eigenvalues in one positive block are distinct. -/
theorem primitiveSpinCGeometricL2SignedBranchEigenvalue_positive_ne_negative
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    primitiveSpinCGeometricL2SignedBranchEigenvalue
        period positiveLevel .positive sector circleMode ≠
      primitiveSpinCGeometricL2SignedBranchEigenvalue
        period positiveLevel .negative sector circleMode := by
  simp only [primitiveSpinCGeometricL2SignedBranchEigenvalue,
    primitiveSpinCDiracBranchSign_positive,
    primitiveSpinCDiracBranchSign_negative, one_mul, neg_one_mul]
  intro hEqual
  have hReal := Complex.ofReal_injective hEqual
  linarith
    [primitiveSpinCHarmonicDiracFrequency_pos
      period positiveLevel sector circleMode]

/-- Algebraic directness of the two complex signed branch spans. -/
theorem primitiveSpinCGeometricL2SignedBranchBlocks_disjoint
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Disjoint
      (primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel .positive sector circleMode)
      (primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel .negative sector circleMode) := by
  exact
    ((Module.End.eigenspaces_iSupIndep
        (primitiveSpinCGeometricDiracComplexLinearMap
          period hPeriod)).pairwiseDisjoint
      (primitiveSpinCGeometricL2SignedBranchEigenvalue_positive_ne_negative
        period positiveLevel sector circleMode)).mono
      (primitiveSpinCGeometricL2SignedBranchBlock_le_eigenspace
        period hPeriod positiveLevel .positive sector circleMode)
      (primitiveSpinCGeometricL2SignedBranchBlock_le_eigenspace
        period hPeriod positiveLevel .negative sector circleMode)

/-- Canonical orthonormal basis of the actual finite-dimensional branch
span.  Its index is the proved geometric finrank, so no unproved
multiplicity equality is hidden here. -/
def primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    OrthonormalBasis
      (Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBranchBlock
            period hPeriod positiveLevel branch sector circleMode)))
      Complex
      (primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel branch sector circleMode) :=
  stdOrthonormalBasis Complex
    (primitiveSpinCGeometricL2SignedBranchBlock
      period hPeriod positiveLevel branch sector circleMode)

/-- The branch basis viewed in the ambient smooth geometric core. -/
def primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (index :
      Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBranchBlock
            period hPeriod positiveLevel branch sector circleMode))) :
    SmoothSection period hPeriod :=
  primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
    period hPeriod positiveLevel branch sector circleMode index

theorem primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_orthonormal
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    Orthonormal Complex
      (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
        period hPeriod positiveLevel branch sector circleMode) := by
  change Orthonormal Complex
    ((primitiveSpinCGeometricL2SignedBranchBlock
      period hPeriod positiveLevel branch sector circleMode).subtypeₗᵢ ∘
      primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
        period hPeriod positiveLevel branch sector circleMode)
  exact
    (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
      period hPeriod positiveLevel branch sector circleMode).orthonormal
      |>.comp_linearIsometry
        (primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode).subtypeₗᵢ

/-- The orthonormal family spans exactly the raw signed branch. -/
theorem primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_span
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
            period hPeriod positiveLevel branch sector circleMode)) =
      primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel branch sector circleMode := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro state ⟨index, rfl⟩
    exact
      (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
        period hPeriod positiveLevel branch sector circleMode index).property
  · intro state hState
    obtain ⟨coefficients, hCoefficients⟩ :=
      (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
        period hPeriod positiveLevel branch sector circleMode).toBasis
        |>.mem_submodule_iff'.mp hState
    rw [hCoefficients]
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span
        (Set.mem_range_self index))

/-- Orthonormalization inside one branch preserves its exact first-order
eigenvalue. -/
theorem primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_dirac
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (index :
      Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBranchBlock
            period hPeriod positiveLevel branch sector circleMode))) :
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
          period hPeriod positiveLevel branch sector circleMode index) =
      primitiveSpinCGeometricL2SignedBranchEigenvalue
          period positiveLevel branch sector circleMode •
        primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
          period hPeriod positiveLevel branch sector circleMode index :=
  primitiveSpinCGeometricL2SignedBranchBlock_dirac
    period hPeriod positiveLevel branch sector circleMode
    (primitiveSpinCGeometricL2SignedBranchOrthonormalBasis
      period hPeriod positiveLevel branch sector circleMode index).property

/-- Standard Euclidean coefficient space of the actual branch span. -/
abbrev PrimitiveSpinCGeometricL2SignedBranchCoefficients
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :=
  EuclideanSpace Complex
    (Fin
      (finrank Complex
        (primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode)))

/-- Finite synthesis into one genuine signed branch. -/
def primitiveSpinCGeometricL2SignedBranchSynthesis
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCGeometricL2SignedBranchCoefficients
        period hPeriod positiveLevel branch sector circleMode →ₗ[Complex]
      SmoothSection period hPeriod where
  toFun coefficients :=
    ∑ index,
      coefficients index •
        primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
          period hPeriod positiveLevel branch sector circleMode index
  map_add' first second := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul, smul_smul, Finset.smul_sum]

/-- Exact Parseval identity for one genuine signed branch. -/
theorem primitiveSpinCGeometricL2SignedBranchSynthesis_inner
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (first second :
      PrimitiveSpinCGeometricL2SignedBranchCoefficients
        period hPeriod positiveLevel branch sector circleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBranchSynthesis
          period hPeriod positiveLevel branch sector circleMode first)
        (primitiveSpinCGeometricL2SignedBranchSynthesis
          period hPeriod positiveLevel branch sector circleMode second) =
      ∑ index, (starRingEnd Complex) (first index) * second index := by
  change
    inner Complex
        (∑ index,
          first index •
            primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode index)
        (∑ index,
          second index •
            primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode index) =
      _
  simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
    (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_orthonormal
      period hPeriod positiveLevel branch sector circleMode).inner_sum
        first second Finset.univ

/-- The signed branch synthesis is an isometry in the independent geometric
`L²` norm. -/
def primitiveSpinCGeometricL2SignedBranchLinearIsometry
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCGeometricL2SignedBranchCoefficients
        period hPeriod positiveLevel branch sector circleMode →ₗᵢ[Complex]
      SmoothSection period hPeriod :=
  (primitiveSpinCGeometricL2SignedBranchSynthesis
    period hPeriod positiveLevel branch sector circleMode).isometryOfInner (by
      intro first second
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2SignedBranchSynthesis
              period hPeriod positiveLevel branch sector circleMode first)
            (primitiveSpinCGeometricL2SignedBranchSynthesis
              period hPeriod positiveLevel branch sector circleMode second) =
          inner Complex first second
      rw [primitiveSpinCGeometricL2SignedBranchSynthesis_inner
        period hPeriod positiveLevel branch sector circleMode]
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro index _
      rw [RCLike.inner_apply, mul_comm])

/-- The finite signed synthesis still intertwines the true geometric Dirac
operator with its exact first-order eigenvalue. -/
theorem primitiveSpinCGeometricL2SignedBranchSynthesis_dirac
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int)
    (coefficients :
      PrimitiveSpinCGeometricL2SignedBranchCoefficients
        period hPeriod positiveLevel branch sector circleMode) :
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2SignedBranchSynthesis
          period hPeriod positiveLevel branch sector circleMode coefficients) =
      primitiveSpinCGeometricL2SignedBranchEigenvalue
          period positiveLevel branch sector circleMode •
        primitiveSpinCGeometricL2SignedBranchSynthesis
          period hPeriod positiveLevel branch sector circleMode
          coefficients := by
  change
    primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
        (∑ index,
          coefficients index •
            primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode index) =
      _ •
        ∑ index,
          coefficients index •
            primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode index
  rw [map_sum]
  simp_rw [map_smul,
    primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_dirac
      period hPeriod positiveLevel branch sector circleMode]
  rw [Finset.smul_sum]
  simp_rw [smul_smul, mul_comm]

/-- The same isometry into the independent complete geometric Hilbert
space. -/
def primitiveSpinCGeometricL2CompletedSignedBranchIsometry
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCGeometricL2SignedBranchCoefficients
        period hPeriod positiveLevel branch sector circleMode →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  UniformSpace.Completion.toComplₗᵢ.comp
    (primitiveSpinCGeometricL2SignedBranchLinearIsometry
      period hPeriod positiveLevel branch sector circleMode)

/-- The completed image of every finite signed branch is closed. -/
theorem primitiveSpinCGeometricL2CompletedSignedBranchIsometry_closedRange
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice) (circleMode : Int) :
    IsClosed
      (Set.range
        (primitiveSpinCGeometricL2CompletedSignedBranchIsometry
          period hPeriod positiveLevel branch sector circleMode)) :=
  (primitiveSpinCGeometricL2CompletedSignedBranchIsometry
    period hPeriod positiveLevel branch sector circleMode).isometry
      |>.isUniformInducing.isComplete_range.isClosed

/-! ## The complete positive signed block -/

/-- The full positive-level geometric block obtained from both signs. -/
def primitiveSpinCGeometricL2SignedBlock
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule Complex (SmoothSection period hPeriod) :=
  primitiveSpinCGeometricL2SignedBranchBlock
      period hPeriod positiveLevel .positive sector circleMode ⊔
    primitiveSpinCGeometricL2SignedBranchBlock
      period hPeriod positiveLevel .negative sector circleMode

noncomputable instance primitiveSpinCGeometricL2SignedBlock_finiteDimensional
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    FiniteDimensional Complex
      (primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode) := by
  unfold primitiveSpinCGeometricL2SignedBlock
  infer_instance

/-- Both signs together still lie in one exact squared-Dirac eigenspace. -/
theorem primitiveSpinCGeometricL2SignedBlock_le_squaredEigenspace
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode ≤
      Module.End.eigenspace
        (primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod)
        (primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
          period positiveLevel sector circleMode) := by
  unfold primitiveSpinCGeometricL2SignedBlock
  apply sup_le
  · intro state hState
    exact Module.End.mem_eigenspace_iff.mpr
      (primitiveSpinCGeometricL2SignedBranchBlock_dirac_sq
        period hPeriod positiveLevel .positive sector circleMode hState)
  · intro state hState
    exact Module.End.mem_eigenspace_iff.mpr
      (primitiveSpinCGeometricL2SignedBranchBlock_dirac_sq
        period hPeriod positiveLevel .negative sector circleMode hState)

theorem primitiveSpinCGeometricL2SignedBlock_dirac_sq
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) {state : SmoothSection period hPeriod}
    (hState :
      state ∈
        primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveLevel sector circleMode) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod state =
      primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
          period positiveLevel sector circleMode • state :=
  Module.End.mem_eigenspace_iff.mp
    (primitiveSpinCGeometricL2SignedBlock_le_squaredEigenspace
      period hPeriod positiveLevel sector circleMode hState)

/-- Canonical orthonormal basis of the actual two-sign block. -/
def primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    OrthonormalBasis
      (Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBlock
            period hPeriod positiveLevel sector circleMode)))
      Complex
      (primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode) :=
  stdOrthonormalBasis Complex
    (primitiveSpinCGeometricL2SignedBlock
      period hPeriod positiveLevel sector circleMode)

/-- The full signed-block basis in the ambient smooth core. -/
def primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (index :
      Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBlock
            period hPeriod positiveLevel sector circleMode))) :
    SmoothSection period hPeriod :=
  primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
    period hPeriod positiveLevel sector circleMode index

theorem primitiveSpinCGeometricL2SignedBlockOrthonormalFamily_orthonormal
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Orthonormal Complex
      (primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
        period hPeriod positiveLevel sector circleMode) := by
  change Orthonormal Complex
    ((primitiveSpinCGeometricL2SignedBlock
      period hPeriod positiveLevel sector circleMode).subtypeₗᵢ ∘
      primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
        period hPeriod positiveLevel sector circleMode)
  exact
    (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
      period hPeriod positiveLevel sector circleMode).orthonormal
      |>.comp_linearIsometry
        (primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveLevel sector circleMode).subtypeₗᵢ

theorem primitiveSpinCGeometricL2SignedBlockOrthonormalFamily_span
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
            period hPeriod positiveLevel sector circleMode)) =
      primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel sector circleMode := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro state ⟨index, rfl⟩
    exact
      (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
        period hPeriod positiveLevel sector circleMode index).property
  · intro state hState
    obtain ⟨coefficients, hCoefficients⟩ :=
      (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
        period hPeriod positiveLevel sector circleMode).toBasis
        |>.mem_submodule_iff'.mp hState
    rw [hCoefficients]
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self index))

/-- The complete orthonormal block preserves the exact squared equation. -/
theorem primitiveSpinCGeometricL2SignedBlockOrthonormalFamily_dirac_sq
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (index :
      Fin
        (finrank Complex
          (primitiveSpinCGeometricL2SignedBlock
            period hPeriod positiveLevel sector circleMode))) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
          period hPeriod positiveLevel sector circleMode index) =
      primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
          period positiveLevel sector circleMode •
        primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
          period hPeriod positiveLevel sector circleMode index :=
  primitiveSpinCGeometricL2SignedBlock_dirac_sq
    period hPeriod positiveLevel sector circleMode
    (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
      period hPeriod positiveLevel sector circleMode index).property

abbrev PrimitiveSpinCGeometricL2SignedBlockCoefficients
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :=
  EuclideanSpace Complex
    (Fin
      (finrank Complex
        (primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveLevel sector circleMode)))

/-- Parseval synthesis of the complete two-sign block. -/
def primitiveSpinCGeometricL2SignedBlockSynthesis
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    PrimitiveSpinCGeometricL2SignedBlockCoefficients
        period hPeriod positiveLevel sector circleMode →ₗ[Complex]
      SmoothSection period hPeriod where
  toFun coefficients :=
    ∑ index,
      coefficients index •
        primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
          period hPeriod positiveLevel sector circleMode index
  map_add' first second := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul, smul_smul, Finset.smul_sum]

theorem primitiveSpinCGeometricL2SignedBlockSynthesis_inner
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (first second :
      PrimitiveSpinCGeometricL2SignedBlockCoefficients
        period hPeriod positiveLevel sector circleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveLevel sector circleMode first)
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveLevel sector circleMode second) =
      ∑ index, (starRingEnd Complex) (first index) * second index := by
  change
    inner Complex
        (∑ index,
          first index •
            primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
              period hPeriod positiveLevel sector circleMode index)
        (∑ index,
          second index •
            primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
              period hPeriod positiveLevel sector circleMode index) =
      _
  simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
    (primitiveSpinCGeometricL2SignedBlockOrthonormalFamily_orthonormal
      period hPeriod positiveLevel sector circleMode).inner_sum
        first second Finset.univ

def primitiveSpinCGeometricL2SignedBlockLinearIsometry
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    PrimitiveSpinCGeometricL2SignedBlockCoefficients
        period hPeriod positiveLevel sector circleMode →ₗᵢ[Complex]
      SmoothSection period hPeriod :=
  (primitiveSpinCGeometricL2SignedBlockSynthesis
    period hPeriod positiveLevel sector circleMode).isometryOfInner (by
      intro first second
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2SignedBlockSynthesis
              period hPeriod positiveLevel sector circleMode first)
            (primitiveSpinCGeometricL2SignedBlockSynthesis
              period hPeriod positiveLevel sector circleMode second) =
          inner Complex first second
      rw [primitiveSpinCGeometricL2SignedBlockSynthesis_inner
        period hPeriod positiveLevel sector circleMode]
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro index _
      rw [RCLike.inner_apply, mul_comm])

theorem primitiveSpinCGeometricL2SignedBlockSynthesis_dirac_sq
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (coefficients :
      PrimitiveSpinCGeometricL2SignedBlockCoefficients
        period hPeriod positiveLevel sector circleMode) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveLevel sector circleMode coefficients) =
      primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
          period positiveLevel sector circleMode •
        primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveLevel sector circleMode coefficients := by
  change
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (∑ index,
          coefficients index •
            primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
              period hPeriod positiveLevel sector circleMode index) =
      _ •
        ∑ index,
          coefficients index •
            primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
              period hPeriod positiveLevel sector circleMode index
  rw [map_sum]
  simp_rw [map_smul,
    primitiveSpinCGeometricL2SignedBlockOrthonormalFamily_dirac_sq
      period hPeriod positiveLevel sector circleMode]
  rw [Finset.smul_sum]
  simp_rw [smul_smul, mul_comm]

def primitiveSpinCGeometricL2CompletedSignedBlockIsometry
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    PrimitiveSpinCGeometricL2SignedBlockCoefficients
        period hPeriod positiveLevel sector circleMode →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  UniformSpace.Completion.toComplₗᵢ.comp
    (primitiveSpinCGeometricL2SignedBlockLinearIsometry
      period hPeriod positiveLevel sector circleMode)

theorem primitiveSpinCGeometricL2CompletedSignedBlockIsometry_closedRange
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    IsClosed
      (Set.range
        (primitiveSpinCGeometricL2CompletedSignedBlockIsometry
          period hPeriod positiveLevel sector circleMode)) :=
  (primitiveSpinCGeometricL2CompletedSignedBlockIsometry
    period hPeriod positiveLevel sector circleMode).isometry
      |>.isUniformInducing.isComplete_range.isClosed

/-- Assumption-free certificate for the Hilbert realization of every
positive-level signed branch. -/
structure ProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
    where
  orthonormal :
    ∀ positiveLevel branch sector circleMode,
      Orthonormal Complex
        (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
          period hPeriod positiveLevel branch sector circleMode)
  exactSpan :
    ∀ positiveLevel branch sector circleMode,
      Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2SignedBranchOrthonormalFamily
              period hPeriod positiveLevel branch sector circleMode)) =
        primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel branch sector circleMode
  exactDirac :
    ∀ positiveLevel branch sector circleMode coefficients,
      primitiveSpinCGeometricDiracComplexLinearMap period hPeriod
          (primitiveSpinCGeometricL2SignedBranchSynthesis
            period hPeriod positiveLevel branch sector circleMode
            coefficients) =
        primitiveSpinCGeometricL2SignedBranchEigenvalue
            period positiveLevel branch sector circleMode •
          primitiveSpinCGeometricL2SignedBranchSynthesis
            period hPeriod positiveLevel branch sector circleMode
            coefficients
  closedCompletedRange :
    ∀ positiveLevel branch sector circleMode,
      IsClosed
        (Set.range
          (primitiveSpinCGeometricL2CompletedSignedBranchIsometry
            period hPeriod positiveLevel branch sector circleMode))
  branchesDisjoint :
    ∀ positiveLevel sector circleMode,
      Disjoint
        (primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel .positive sector circleMode)
        (primitiveSpinCGeometricL2SignedBranchBlock
          period hPeriod positiveLevel .negative sector circleMode)
  fullBlockOrthonormal :
    ∀ positiveLevel sector circleMode,
      Orthonormal Complex
        (primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
          period hPeriod positiveLevel sector circleMode)
  fullBlockExactSquaredDirac :
    ∀ positiveLevel sector circleMode coefficients,
      primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
          (primitiveSpinCGeometricL2SignedBlockSynthesis
            period hPeriod positiveLevel sector circleMode coefficients) =
        primitiveSpinCGeometricL2SignedBlockSquaredEigenvalue
            period positiveLevel sector circleMode •
          primitiveSpinCGeometricL2SignedBlockSynthesis
            period hPeriod positiveLevel sector circleMode coefficients
  fullBlockClosedCompletedRange :
    ∀ positiveLevel sector circleMode,
      IsClosed
        (Set.range
          (primitiveSpinCGeometricL2CompletedSignedBlockIsometry
            period hPeriod positiveLevel sector circleMode))

def programPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
      period hPeriod where
  orthonormal :=
    primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_orthonormal
      period hPeriod
  exactSpan :=
    primitiveSpinCGeometricL2SignedBranchOrthonormalFamily_span
      period hPeriod
  exactDirac :=
    primitiveSpinCGeometricL2SignedBranchSynthesis_dirac period hPeriod
  closedCompletedRange :=
    primitiveSpinCGeometricL2CompletedSignedBranchIsometry_closedRange
      period hPeriod
  branchesDisjoint :=
    primitiveSpinCGeometricL2SignedBranchBlocks_disjoint period hPeriod
  fullBlockOrthonormal :=
    primitiveSpinCGeometricL2SignedBlockOrthonormalFamily_orthonormal
      period hPeriod
  fullBlockExactSquaredDirac :=
    primitiveSpinCGeometricL2SignedBlockSynthesis_dirac_sq period hPeriod
  fullBlockClosedCompletedRange :=
    primitiveSpinCGeometricL2CompletedSignedBlockIsometry_closedRange
      period hPeriod

theorem primitiveSpinCGeometricL2SignedBranchCompletion_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2SignedBranchCompletionCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
end JanusFormal
