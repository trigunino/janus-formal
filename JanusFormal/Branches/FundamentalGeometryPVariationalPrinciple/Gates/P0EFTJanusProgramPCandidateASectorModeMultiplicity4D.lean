import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorModeAssembly4D

/-!
# Exact multiplicities of the assembled Candidate-A sectors

For the dependent total mode type `Σ sector, Mode sector`, the fiber of the
canonical sector classification over `sector` is equivalent to `Mode sector`.
Hence each physical multiplicity is exactly the cardinality of the supplied
sector-local mode type, not merely an abstract fiber cardinality.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateASectorModeMultiplicity4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D

local instance candidateASectorModeFintype
    (types : CandidateASectorModeTypes)
    (sector : CandidateAZeroModeSector) : Fintype (types.Mode sector) :=
  types.modeFintype sector

/-- The classification fiber over one sector is its original mode type. -/
def candidateASectorClassificationFiberEquiv
    (types : CandidateASectorModeTypes)
    (sector : CandidateAZeroModeSector) :
    {mode : types.GlobalMode //
      types.classification.sectorOf mode = sector} ≃
      types.Mode sector where
  toFun mode := by
    have hSector : mode.1.1 = sector := mode.2
    exact hSector ▸ mode.1.2
  invFun mode := ⟨⟨sector, mode⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨sourceSector, sourceMode⟩, hSector⟩
    simp only [CandidateASectorModeTypes.classification_sector] at hSector
    subst sourceSector
    rfl
  right_inv mode := rfl

/-- One sector multiplicity is exactly the size of its declared mode type. -/
theorem candidateASectorMultiplicity_eq_card
    (types : CandidateASectorModeTypes)
    (sector : CandidateAZeroModeSector) :
    types.classification.multiplicity sector =
      Fintype.card (types.Mode sector) := by
  unfold CandidateAZeroModeSectorClassification.multiplicity
  exact Fintype.card_congr
    (candidateASectorClassificationFiberEquiv types sector)

/-- The total assembled cardinality is the sum of the five explicit local
cardinalities. -/
theorem candidateASectorGlobalMode_card
    (types : CandidateASectorModeTypes) :
    Fintype.card types.GlobalMode =
      ∑ sector : CandidateAZeroModeSector,
        Fintype.card (types.Mode sector) := by
  rw [← types.classification.sum_multiplicity]
  apply Finset.sum_congr rfl
  intro sector _
  exact candidateASectorMultiplicity_eq_card types sector

/-- Public exact-multiplicity checkpoint. -/
theorem candidateA_sector_mode_multiplicity_gate
    (types : CandidateASectorModeTypes) :
    (∀ sector,
      types.classification.multiplicity sector =
        Fintype.card (types.Mode sector)) ∧
      Fintype.card types.GlobalMode =
        ∑ sector : CandidateAZeroModeSector,
          Fintype.card (types.Mode sector) :=
  ⟨candidateASectorMultiplicity_eq_card types,
    candidateASectorGlobalMode_card types⟩

end
end P0EFTJanusProgramPCandidateASectorModeMultiplicity4D
end JanusFormal
