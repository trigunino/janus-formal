import Mathlib

namespace JanusFormal
namespace P0EFTJanusLocalGRSourceDecoupling

set_option autoImplicit false

/-- Source coefficient of the massless diagonal mode. -/
noncomputable def diagonalSource (sourcePlus sourceMinus : ℝ) : ℝ :=
  (sourcePlus + sourceMinus) / 2

/-- Source coefficient of the massive relative mode. -/
noncomputable def relativeSource (sourcePlus sourceMinus : ℝ) : ℝ :=
  (sourcePlus - sourceMinus) / 2

/-- Exact decomposition of the two-sector linear source coupling. -/
theorem source_coupling_mode_decomposition
    (sourcePlus sourceMinus hPlus hMinus : ℝ) :
    sourcePlus * hPlus + sourceMinus * hMinus =
      diagonalSource sourcePlus sourceMinus * (hPlus + hMinus) +
        relativeSource sourcePlus sourceMinus * (hPlus - hMinus) := by
  unfold diagonalSource relativeSource
  ring

/-- Exact local-GR decoupling requires equal source coefficients. -/
theorem relative_mode_unsourced_iff_equal_sources
    (sourcePlus sourceMinus : ℝ) :
    relativeSource sourcePlus sourceMinus = 0 ↔
      sourcePlus = sourceMinus := by
  unfold relativeSource
  constructor <;> intro h <;> linarith

/-- A source placed on only one sheet excites the relative massive mode. -/
theorem single_sheet_source_excites_relative_mode
    (sourcePlus : ℝ) (hSource : sourcePlus ≠ 0) :
    relativeSource sourcePlus 0 ≠ 0 := by
  unfold relativeSource
  intro hZero
  apply hSource
  linarith

/-- Opposite PT source coefficients excite a pure relative mode. -/
theorem opposite_pt_sources_are_pure_relative
    (source : ℝ) :
    diagonalSource source (-source) = 0 ∧
      relativeSource source (-source) = source := by
  constructor
  · unfold diagonalSource
    ring
  · unfold relativeSource
    ring

/-- Equal source coefficients excite only the diagonal massless mode. -/
theorem equal_sources_are_pure_diagonal
    (source : ℝ) :
    diagonalSource source source = source ∧
      relativeSource source source = 0 := by
  constructor
  · unfold diagonalSource
    ring
  · unfold relativeSource
    ring

/--
Post-Newtonian closure must control the relative source rather than infer GR
from the existence of a massless eigenmode alone.
-/
structure LocalGRPPNClosureStatus where
  diagonalMasslessPropagatorDerived : Prop
  relativeMassivePropagatorDerived : Prop
  physicalMatterSourceMapDerived : Prop
  relativeSourceAbsentOrScreened : Prop
  effectiveNewtonConstantMatched : Prop
  ppnGammaBoundSatisfied : Prop
  preferredFrameBoundsSatisfied : Prop
  radiativeStabilityProved : Prop

def localGRPPNClosed (s : LocalGRPPNClosureStatus) : Prop :=
  s.diagonalMasslessPropagatorDerived ∧
  s.relativeMassivePropagatorDerived ∧
  s.physicalMatterSourceMapDerived ∧
  s.relativeSourceAbsentOrScreened ∧
  s.effectiveNewtonConstantMatched ∧
  s.ppnGammaBoundSatisfied ∧
  s.preferredFrameBoundsSatisfied ∧
  s.radiativeStabilityProved

end P0EFTJanusLocalGRSourceDecoupling
end JanusFormal
