import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAZeroModeSector4D

/-!
# D10-free sector classification of actual Candidate-A zero modes

The named-mode frontier identifies the complete kernel of the augmented
Candidate-A Hessian.  This file adds only a physical classification of those
already identified modes.  It does not assume that the coupled Hessian is
block diagonal.

The five labels correspond to the actual D10-free tangent sectors:

* metric/diffeomorphism;
* paired Abelian gauge;
* primitive SpinC matter;
* longitudinal/LL;
* boundary and finite-BV.

The total kernel dimension is the sum of the five finite fiber cardinalities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteKernelNamedModeCoercivity4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

/-- A sector assignment for a finite family of genuine named zero modes. -/
structure CandidateAZeroModeSectorClassification
    (ZeroMode : Type*) [Fintype ZeroMode] where
  sectorOf : ZeroMode → CandidateAZeroModeSector

/-- Multiplicity of one physical sector. -/
def CandidateAZeroModeSectorClassification.multiplicity
    {ZeroMode : Type*} [Fintype ZeroMode]
    (classification : CandidateAZeroModeSectorClassification ZeroMode)
    (sector : CandidateAZeroModeSector) : Nat :=
  Fintype.card {mode : ZeroMode // classification.sectorOf mode = sector}

/-- The sector multiplicities partition the complete named-mode type. -/
theorem CandidateAZeroModeSectorClassification.sum_multiplicity
    {ZeroMode : Type*} [Fintype ZeroMode]
    (classification : CandidateAZeroModeSectorClassification ZeroMode) :
    ∑ sector : CandidateAZeroModeSector,
        classification.multiplicity sector =
      Fintype.card ZeroMode := by
  rw [show (∑ sector : CandidateAZeroModeSector,
      classification.multiplicity sector) =
      Fintype.card (Σ sector : CandidateAZeroModeSector,
        {mode : ZeroMode // classification.sectorOf mode = sector}) by
    simp [CandidateAZeroModeSectorClassification.multiplicity,
      Fintype.card_sigma]]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv classification.sectorOf)

/-- Named-kernel coercivity together with a physical sector assignment. -/
structure CandidateASectorClassifiedNamedKernelCoercivity
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  named : SelfAdjointNamedKernelCoercivityData operator hSelfAdjoint ZeroMode
  classification : CandidateAZeroModeSectorClassification ZeroMode

/-- The actual kernel dimension is the sum of physical sector multiplicities. -/
theorem CandidateASectorClassifiedNamedKernelCoercivity.kernel_finrank_eq_sum
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : CandidateASectorClassifiedNamedKernelCoercivity operator
      hSelfAdjoint ZeroMode) :
    Module.finrank Real operator.ker =
      ∑ sector : CandidateAZeroModeSector,
        data.classification.multiplicity sector := by
  rw [data.named.toBasisCoercivity.kernel_finrank_eq_card]
  exact data.classification.sum_multiplicity.symm

/-- Public physical zero-mode count checkpoint. -/
theorem global_candidateA_named_zero_mode_sector_gate
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : CandidateASectorClassifiedNamedKernelCoercivity operator
      hSelfAdjoint ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker =
        ∑ sector : CandidateAZeroModeSector,
          data.classification.multiplicity sector :=
  ⟨⟨data.named.toBasisCoercivity.toGapData⟩,
    data.kernel_finrank_eq_sum⟩

end
end P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
end JanusFormal
