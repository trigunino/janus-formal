import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9LinearBRSTBlock4D

/-! # Ordinary throat-ghost obstruction on the common D9 packet -/

namespace JanusFormal
namespace P0EFTJanusCommonPairedD9OrdinaryThroatGhostNoGo4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Ungraded reading of the nonlinear ghost formula on the genuine smooth
throat ghost stored in the common packet. -/
def ordinaryThroatQuadraticGhostBRST
    (ghost : CInfinityThroatGhost period hPeriod) :
    CInfinityThroatGhost period hPeriod :=
  (-((2 : Real)⁻¹)) • throatGhostLieBracket period hPeriod ghost ghost

theorem throatGhostLieBracket_self_zero
    (ghost : CInfinityThroatGhost period hPeriod) :
    throatGhostLieBracket period hPeriod ghost ghost =
      (0 : CInfinityThroatGhost period hPeriod) := by
  apply ContMDiffSection.ext
  intro point
  change VectorField.mlieBracket throatCoverModelWithCorners ghost ghost point = 0
  exact congrFun VectorField.mlieBracket_self point

@[simp]
theorem ordinaryThroatQuadraticGhostBRST_eq_zero
    (ghost : CInfinityThroatGhost period hPeriod) :
    ordinaryThroatQuadraticGhostBRST period hPeriod ghost = 0 := by
  rw [ordinaryThroatQuadraticGhostBRST, throatGhostLieBracket_self_zero]
  exact smul_zero _

/-- Exact pointwise compatibility: the linear common block's rule `s c = 0`
agrees with the ungraded quadratic formula on its genuine throat ghost. -/
theorem commonPairedD9LinearBRST_diffeomorphism_pointwise
    (state : CommonPairedD9LinearBRSTBlock period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (commonPairedD9LinearBRSTDifferential period hPeriod state).diffeomorphismGhost
        point =
      ordinaryThroatQuadraticGhostBRST period hPeriod
        state.diffeomorphismGhost point := by
  rw [ordinaryThroatQuadraticGhostBRST_eq_zero]
  rfl

/-- Consequently no ordinary real throat ghost in this packet can realize a
nonzero nonlinear quadratic BRST variation; graded coefficients are essential
for the nonabelian D8 complex already constructed elsewhere. -/
theorem no_nontrivial_ordinaryThroatQuadraticGhostBRST :
    ¬ ∃ ghost : CInfinityThroatGhost period hPeriod,
      ordinaryThroatQuadraticGhostBRST period hPeriod ghost ≠ 0 := by
  rintro ⟨ghost, hNonzero⟩
  exact hNonzero (ordinaryThroatQuadraticGhostBRST_eq_zero
    period hPeriod ghost)

end
end P0EFTJanusCommonPairedD9OrdinaryThroatGhostNoGo4D
end JanusFormal
