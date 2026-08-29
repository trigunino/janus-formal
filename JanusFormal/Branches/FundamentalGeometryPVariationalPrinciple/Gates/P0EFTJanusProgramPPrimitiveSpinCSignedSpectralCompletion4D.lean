import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalMaximalOperator4D

/-!
# Complete signed primitive SpinC spectral realization

The corrected internal Dirac branch is propagated from the algebraic labels
to a genuine diagonal Hilbert realization.  The zero sphere tower remains
undoubled, every positive level carries both internal signs, the coordinate
eigenvectors form a complete Hilbert basis, and the maximal operator is
self-adjoint and Fredholm in the physical quarter-twisted sector.

This closes the abstract analytic signed spectrum.  Identifying this Hilbert
basis with a complete family of smooth geometric eigensections remains a
separate geometric Fourier theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

deriving instance DecidableEq for PrimitiveSpinCSignedNonzeroMode
local instance primitiveSpinCSignedModeDecidableEq :
    DecidableEq PrimitiveSpinCSignedMode := inferInstance

/-- Corrected signed primitive spectral Hilbert space. -/
abbrev PrimitiveSpinCSignedL2 :=
  ComplexDiagonalHilbert PrimitiveSpinCSignedMode

/-- Maximal graph domain of the corrected signed Dirac operator. -/
abbrev PrimitiveSpinCSignedH1
    (fold : Fold) (twist : CircleTwist) :=
  complexDiagonalDomain PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist)

/-- Maximal corrected signed Dirac realization. -/
abbrev primitiveSpinCSignedUnboundedDirac
    (fold : Fold) (twist : CircleTwist) :=
  complexDiagonalOperator PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist)

/-- Canonical complete eigenbasis of the corrected signed realization. -/
abbrev primitiveSpinCSignedHilbertBasis :
    HilbertBasis PrimitiveSpinCSignedMode Complex PrimitiveSpinCSignedL2 :=
  complexDiagonalBasis PrimitiveSpinCSignedMode

theorem primitiveSpinCSignedHilbertBasis_mem_domain
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedMode) :
    primitiveSpinCSignedHilbertBasis mode ∈
      PrimitiveSpinCSignedH1 fold twist :=
  complexDiagonalBasis_mem_domain PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist) mode

/-- Every corrected signed mode is a genuine eigenvector of the maximal
diagonal operator. -/
theorem primitiveSpinCSignedUnboundedDirac_on_basis
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedMode) :
    primitiveSpinCSignedUnboundedDirac fold twist
        ⟨primitiveSpinCSignedHilbertBasis mode,
          primitiveSpinCSignedHilbertBasis_mem_domain fold twist mode⟩ =
      (primitiveSpinCSignedDiracEigenvalue fold twist mode : Complex) •
        primitiveSpinCSignedHilbertBasis mode :=
  complexDiagonalOperator_on_basis PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist) mode

/-- Spectral completeness in the exact Hilbert-space sense. -/
theorem primitiveSpinCSignedHilbertBasis_dense_span :
    (Submodule.span Complex
      (Set.range primitiveSpinCSignedHilbertBasis)).topologicalClosure = ⊤ :=
  HilbertBasis.dense_span primitiveSpinCSignedHilbertBasis

/-- The maximal corrected signed graph domain is dense. -/
theorem primitiveSpinCSignedH1_dense
    (fold : Fold) (twist : CircleTwist) :
    Dense (PrimitiveSpinCSignedH1 fold twist :
      Set PrimitiveSpinCSignedL2) :=
  complexDiagonalDomain_dense PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist)

/-- The corrected signed maximal operator is self-adjoint. -/
theorem primitiveSpinCSignedUnboundedDirac_isSelfAdjoint
    (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint (primitiveSpinCSignedUnboundedDirac fold twist) :=
  complexDiagonalOperator_isSelfAdjoint PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist)

/-- The corrected signed maximal operator is closed. -/
theorem primitiveSpinCSignedUnboundedDirac_isClosed
    (fold : Fold) (twist : CircleTwist) :
    (primitiveSpinCSignedUnboundedDirac fold twist).IsClosed :=
  complexDiagonalOperator_isClosed PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold twist)

/-- Forgetting the internal branch preserves the absolute eigenvalue. -/
theorem primitiveSpinCSignedDiracEigenvalue_abs_eq_full
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedMode) :
    |primitiveSpinCSignedDiracEigenvalue fold twist mode| =
      |primitiveSpinCFullDiracEigenvalue fold twist
        (primitiveSpinCSignedModeToFullMode mode)| := by
  cases mode with
  | inl mode =>
      rfl
  | inr mode =>
      rcases mode with ⟨branch, level, multiplicity, circleMode⟩
      cases branch <;>
        simp [primitiveSpinCSignedDiracEigenvalue,
          primitiveSpinCBranchedDiracEigenvalue,
          primitiveSpinCSignedNonzeroModeToFullMode,
          primitiveSpinCSignedModeToFullMode]

/-- The physical quarter-twisted gap survives the corrected internal branch
and every positive multiplicity. -/
theorem primitiveSpinCSigned_quarter_gap
    (fold : Fold) (mode : PrimitiveSpinCSignedMode) :
    (1 / 4 : Real) ≤
      |primitiveSpinCSignedDiracEigenvalue fold quarterTwist mode| := by
  rw [primitiveSpinCSignedDiracEigenvalue_abs_eq_full]
  exact primitiveSpinCFull_quarter_gap fold
    (primitiveSpinCSignedModeToFullMode mode)

/-- The physical corrected signed operator is bijective. -/
theorem primitiveSpinCSignedUnboundedDirac_quarter_bijective
    (fold : Fold) :
    Function.Bijective
      (primitiveSpinCSignedUnboundedDirac fold quarterTwist) :=
  ⟨complexDiagonalOperator_injective_of_gap
      PrimitiveSpinCSignedMode
      (primitiveSpinCSignedDiracEigenvalue fold quarterTwist)
      (1 / 4) (by norm_num)
      (primitiveSpinCSigned_quarter_gap fold),
    complexDiagonalOperator_surjective_of_gap
      PrimitiveSpinCSignedMode
      (primitiveSpinCSignedDiracEigenvalue fold quarterTwist)
      (1 / 4) (by norm_num)
      (primitiveSpinCSigned_quarter_gap fold)⟩

/-- Closed range and finite-dimensional kernel/cokernel for the complete
corrected signed operator. -/
theorem primitiveSpinCSignedUnboundedDirac_quarter_fredholm
    (fold : Fold) :
    IsClosed
        (LinearMap.range
            (primitiveSpinCSignedUnboundedDirac
              fold quarterTwist).toFun :
          Set PrimitiveSpinCSignedL2) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (primitiveSpinCSignedUnboundedDirac
            fold quarterTwist).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalCokernel PrimitiveSpinCSignedMode
          (primitiveSpinCSignedDiracEigenvalue fold quarterTwist)) :=
  complexDiagonalOperator_fredholm_of_gap
    PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold quarterTwist)
    (1 / 4) (by norm_num)
    (primitiveSpinCSigned_quarter_gap fold)

/-- The complete corrected signed Fredholm index vanishes on both PT
sheets. -/
theorem primitiveSpinCSignedUnboundedDirac_quarter_index_zero
    (fold : Fold) :
    complexDiagonalOperatorIndex PrimitiveSpinCSignedMode
      (primitiveSpinCSignedDiracEigenvalue fold quarterTwist) = 0 :=
  complexDiagonalOperatorIndex_zero_of_gap
    PrimitiveSpinCSignedMode
    (primitiveSpinCSignedDiracEigenvalue fold quarterTwist)
    (1 / 4) (by norm_num)
    (primitiveSpinCSigned_quarter_gap fold)

/-- Consolidated unconditional analytic certificate. -/
structure ProgramPPrimitiveSpinCSignedSpectralCompletionCertificate4D where
  basisComplete :
    (Submodule.span Complex
      (Set.range primitiveSpinCSignedHilbertBasis)).topologicalClosure = ⊤
  domainDense :
    ∀ fold twist,
      Dense (PrimitiveSpinCSignedH1 fold twist :
        Set PrimitiveSpinCSignedL2)
  selfAdjoint :
    ∀ fold twist,
      IsSelfAdjoint (primitiveSpinCSignedUnboundedDirac fold twist)
  physicalFredholm :
    ∀ fold,
      IsClosed
          (LinearMap.range
              (primitiveSpinCSignedUnboundedDirac
                fold quarterTwist).toFun :
            Set PrimitiveSpinCSignedL2) ∧
        FiniteDimensional Complex
          (LinearMap.ker
            (primitiveSpinCSignedUnboundedDirac
              fold quarterTwist).toFun) ∧
        FiniteDimensional Complex
          (ComplexDiagonalCokernel PrimitiveSpinCSignedMode
            (primitiveSpinCSignedDiracEigenvalue fold quarterTwist))
  physicalIndexZero :
    ∀ fold,
      complexDiagonalOperatorIndex PrimitiveSpinCSignedMode
        (primitiveSpinCSignedDiracEigenvalue fold quarterTwist) = 0

def programPPrimitiveSpinCSignedSpectralCompletionCertificate4D :
    ProgramPPrimitiveSpinCSignedSpectralCompletionCertificate4D where
  basisComplete := primitiveSpinCSignedHilbertBasis_dense_span
  domainDense := primitiveSpinCSignedH1_dense
  selfAdjoint := primitiveSpinCSignedUnboundedDirac_isSelfAdjoint
  physicalFredholm := primitiveSpinCSignedUnboundedDirac_quarter_fredholm
  physicalIndexZero :=
    primitiveSpinCSignedUnboundedDirac_quarter_index_zero

theorem programPPrimitiveSpinCSignedSpectralCompletionCertificate4D_nonempty :
    Nonempty ProgramPPrimitiveSpinCSignedSpectralCompletionCertificate4D :=
  ⟨programPPrimitiveSpinCSignedSpectralCompletionCertificate4D⟩

end

end P0EFTJanusProgramPPrimitiveSpinCSignedSpectralCompletion4D
end JanusFormal
