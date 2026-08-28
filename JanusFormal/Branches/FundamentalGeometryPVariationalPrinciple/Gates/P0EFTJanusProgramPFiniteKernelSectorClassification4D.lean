import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModes4D

/-!
# Sectorwise classification of the actual finite kernel

Named zero modes may belong to different physical sectors.  This file adds a
finite sector map and proves that the actual kernel dimension is the sum of the
sector multiplicities.  The result is purely intrinsic to the named kernel
model and introduces no block-diagonal assumption on the Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelSectorClassification4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteKernelNamedModes4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
variable {operator : E →L[Real] E}
variable {ZeroMode : Type} {Sector : Type*}
  [Fintype ZeroMode] [DecidableEq ZeroMode]
  [Fintype Sector] [DecidableEq Sector]

/-- A named actual-kernel model together with a physical sector assigned to
every zero-mode label. -/
structure FiniteKernelSectorClassification
    (operator : E →L[Real] E)
    (ZeroMode : Type) (Sector : Type*)
    [Fintype ZeroMode] [DecidableEq ZeroMode]
    [Fintype Sector] [DecidableEq Sector] where
  family : FiniteKernelNamedModeFamily operator ZeroMode
  sector : ZeroMode → Sector

/-- Number of classified zero modes in one sector. -/
def FiniteKernelSectorClassification.multiplicity
    (classification : FiniteKernelSectorClassification operator ZeroMode Sector)
    (physicalSector : Sector) : Nat :=
  Fintype.card {index : ZeroMode // classification.sector index = physicalSector}

/-- Canonical equivalence between all labels and the disjoint union of their
sector fibers. -/
def FiniteKernelSectorClassification.sigmaFiberEquiv
    (classification : FiniteKernelSectorClassification operator ZeroMode Sector) :
    ZeroMode ≃
      Σ physicalSector : Sector,
        {index : ZeroMode // classification.sector index = physicalSector} where
  toFun index :=
    ⟨classification.sector index, ⟨index, rfl⟩⟩
  invFun classified := classified.2.1
  left_inv index := rfl
  right_inv := by
    intro classified
    rcases classified with ⟨physicalSector, index, hSector⟩
    dsimp
    subst physicalSector
    rfl

/-- The total number of labels is the sum of all sector multiplicities. -/
theorem FiniteKernelSectorClassification.card_eq_sum_multiplicity
    (classification : FiniteKernelSectorClassification operator ZeroMode Sector) :
    Fintype.card ZeroMode =
      ∑ physicalSector : Sector, classification.multiplicity physicalSector := by
  calc
    Fintype.card ZeroMode =
        Fintype.card
          (Σ physicalSector : Sector,
            {index : ZeroMode //
              classification.sector index = physicalSector}) :=
      Fintype.card_congr classification.sigmaFiberEquiv
    _ = ∑ physicalSector : Sector,
        Fintype.card
          {index : ZeroMode //
            classification.sector index = physicalSector} := by
      exact Fintype.card_sigma _
    _ = ∑ physicalSector : Sector,
        classification.multiplicity physicalSector := rfl

/-- The actual kernel dimension decomposes exactly into physical sector
multiplicities. -/
theorem FiniteKernelSectorClassification.kernel_finrank_eq_sum_multiplicity
    (classification : FiniteKernelSectorClassification operator ZeroMode Sector) :
    Module.finrank Real operator.ker =
      ∑ physicalSector : Sector, classification.multiplicity physicalSector := by
  rw [classification.family.kernel_finrank_eq_card,
    classification.card_eq_sum_multiplicity]

/-- Every sector-classified vector remains an actual zero mode. -/
theorem FiniteKernelSectorClassification.vector_mem_kernel
    (classification : FiniteKernelSectorClassification operator ZeroMode Sector)
    (index : ZeroMode) :
    operator (classification.family.vector index) = 0 :=
  classification.family.vector_mem_kernel index

/-- Public sector-count checkpoint. -/
theorem finite_kernel_sector_classification_gate
    (classification : FiniteKernelSectorClassification operator ZeroMode Sector) :
    Module.finrank Real operator.ker =
        ∑ physicalSector : Sector, classification.multiplicity physicalSector ∧
      (∀ index, operator (classification.family.vector index) = 0) :=
  ⟨classification.kernel_finrank_eq_sum_multiplicity,
    classification.vector_mem_kernel⟩

end
end P0EFTJanusProgramPFiniteKernelSectorClassification4D
end JanusFormal
