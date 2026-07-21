import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9LinearBRSTBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeGlobalH04D

/-!
# Global abelian H0 of the common paired D9 BRST block

The two potential slots of the actual paired linear BRST differential vanish
exactly when its two smooth global abelian ghosts are constant on D8.
-/

namespace JanusFormal
namespace P0EFTJanusCommonPairedD9GlobalAbelianH04D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D
open P0EFTJanusMappingTorusAbelianGaugeGlobalH04D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The genuine pair of global abelian ghosts occurring in the common D9
linear BRST block. -/
abbrev CommonPairedD9GlobalAbelianGhost :=
  SmoothQuotientField period hPeriod GaugeLieAlgebra ×
    SmoothQuotientField period hPeriod GaugeLieAlgebra

/-- Real-linear kernel of the actual paired global abelian gauge generator. -/
abbrev CommonPairedD9GlobalAbelianGhostZeroMode :=
  LinearMap.ker (abelianGaugePairGenerator period hPeriod)

/-- The two potential outputs of the paired BRST differential vanish exactly
for two constant smooth global ghosts. -/
theorem commonPairedD9LinearBRSTDifferential_potentials_eq_zero_iff_constants
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    ((commonPairedD9LinearBRSTDifferential period hPeriod state).firstU1.potential = 0 ∧
      (commonPairedD9LinearBRSTDifferential period hPeriod state).secondU1.potential = 0) ↔
      (∃ firstValue : GaugeLieAlgebra,
        ∀ point, state.firstU1.ghost point = firstValue) ∧
      (∃ secondValue : GaugeLieAlgebra,
        ∀ point, state.secondU1.ghost point = secondValue) := by
  change
    (exactGaugePotential period hPeriod state.firstU1.ghost = 0 ∧
      exactGaugePotential period hPeriod state.secondU1.ghost = 0) ↔ _
  constructor
  · intro hZero
    exact
      ⟨(exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
          state.firstU1.ghost).1 hZero.1,
        (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
          state.secondU1.ghost).1 hZero.2⟩
  · intro hConstant
    exact
      ⟨(exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
          state.firstU1.ghost).2 hConstant.1,
        (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
          state.secondU1.ghost).2 hConstant.2⟩

private def pairedZeroModeProductLinearEquiv :
    CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod ≃ₗ[Real]
      GlobalAbelianGaugeZeroMode period hPeriod ×
        GlobalAbelianGaugeZeroMode period hPeriod where
  toFun ghosts :=
    (⟨ghosts.1.1, congrArg Prod.fst ghosts.2⟩,
      ⟨ghosts.1.2, congrArg Prod.snd ghosts.2⟩)
  invFun ghosts :=
    ⟨(ghosts.1.1, ghosts.2.1), by
      apply Prod.ext
      · exact ghosts.1.2
      · exact ghosts.2.2⟩
  left_inv ghosts := by
    apply Subtype.ext
    rfl
  right_inv ghosts := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The real-linear kernel of the actual paired abelian generator is exactly
two copies of the abelian Lie algebra.  This is not a computation of the
kernel of the complete BRST state map. -/
def commonPairedD9GlobalAbelianGhostZeroModeLinearEquiv :
    CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod ≃ₗ[Real]
      GaugeLieAlgebra × GaugeLieAlgebra :=
  (pairedZeroModeProductLinearEquiv period hPeriod).trans
    (LinearEquiv.prodCongr
      (globalAbelianGaugeZeroModeLinearEquiv period hPeriod)
      (globalAbelianGaugeZeroModeLinearEquiv period hPeriod))

/-- Underlying equivalence of the paired global abelian zero modes. -/
def commonPairedD9GlobalAbelianGhostZeroModeEquiv :
    CommonPairedD9GlobalAbelianGhostZeroMode period hPeriod ≃
      GaugeLieAlgebra × GaugeLieAlgebra :=
  (commonPairedD9GlobalAbelianGhostZeroModeLinearEquiv period hPeriod).toEquiv

end

end P0EFTJanusCommonPairedD9GlobalAbelianH04D
end JanusFormal
