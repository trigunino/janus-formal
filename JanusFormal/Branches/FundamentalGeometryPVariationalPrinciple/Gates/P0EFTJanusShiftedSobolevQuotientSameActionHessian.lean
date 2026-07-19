import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevSameActionHessian
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevPhysicalQuotient

/-!
# The periodic coefficient action and Hessian on the physical quotient

The bounded splitting of the zero Fourier mode supplies a canonical zero-free
representative of every quotient class.  This gate defines `1/2 * ||J u||^2`
on those classes, computes its genuine second Frechet derivative, and proves
that the descended Hessian is nondegenerate.  The result remains confined to
the periodic coefficient model; it is not the global Janus action or quotient.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevQuotientSameActionHessian

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram
open P0EFTJanusShiftedSobolevPullbackHessian
open P0EFTJanusShiftedSobolevSameActionHessian
open P0EFTJanusShiftedSobolevPhysicalQuotient

/-- Canonical zero-free representative of a physical quotient class. -/
def physicalQuotientRepresentative
    (targetWeight : LatticeMode → Real) :
    PhysicalPotentialQuotient targetWeight →L[Real]
      ShiftedPotentialHilbert targetWeight :=
  (Submodule.subtypeL
      (ZeroFreePotentialSubspace targetWeight)).comp
    (physicalQuotientEquivZeroFree targetWeight).toContinuousLinearMap

theorem physicalQuotientRepresentative_injective
    (targetWeight : LatticeMode → Real) :
    Function.Injective (physicalQuotientRepresentative targetWeight) := by
  intro first second hRepresentative
  apply (physicalQuotientEquivZeroFree targetWeight).injective
  apply Subtype.ext
  exact hRepresentative

theorem physicalQuotientRepresentative_class
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) :
    Submodule.Quotient.mk
        (physicalQuotientRepresentative targetWeight state) = state := by
  change
    (physicalQuotientEquivZeroFree targetWeight).symm
        (physicalQuotientEquivZeroFree targetWeight state) = state
  exact (physicalQuotientEquivZeroFree targetWeight).symm_apply_apply state

/-- The shifted Lorentz--Gram symbol acting on canonical quotient
representatives. -/
def physicalQuotientSymbol
    (targetWeight : LatticeMode → Real) :
    PhysicalPotentialQuotient targetWeight →L[Real]
      SobolevMetricHilbert targetWeight :=
  (shiftedSobolevLorentzGram targetWeight).comp
    (physicalQuotientRepresentative targetWeight)

theorem physicalQuotientSymbol_mk
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    physicalQuotientSymbol targetWeight (Submodule.Quotient.mk potential) =
      shiftedSobolevLorentzGram targetWeight potential := by
  have hClass := physicalQuotientRepresentative_class targetWeight
    (Submodule.Quotient.mk potential : PhysicalPotentialQuotient targetWeight)
  have hDifference :
      physicalQuotientRepresentative targetWeight
          (Submodule.Quotient.mk potential) - potential ∈
        (potentialZeroModeProjection targetWeight).range :=
    QuotientAddGroup.eq_iff_sub_mem.mp hClass
  have hKernel :
      physicalQuotientRepresentative targetWeight
          (Submodule.Quotient.mk potential) - potential ∈
        (shiftedSobolevLorentzGram targetWeight).ker := by
    rw [← zeroModeProjection_range_eq_symbol_ker targetWeight]
    exact hDifference
  change shiftedSobolevLorentzGram targetWeight
      (physicalQuotientRepresentative targetWeight
        (Submodule.Quotient.mk potential) - potential) = 0 at hKernel
  change shiftedSobolevLorentzGram targetWeight
      (physicalQuotientRepresentative targetWeight
        (Submodule.Quotient.mk potential)) =
    shiftedSobolevLorentzGram targetWeight potential
  simpa using (sub_eq_zero.mp (by simpa using hKernel))

/-- The same periodic coefficient action, now as a function of a quotient
class. -/
def physicalQuotientAction
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) : Real :=
  (1 / 2 : Real) *
    ⟪physicalQuotientSymbol targetWeight state,
      physicalQuotientSymbol targetWeight state⟫_Real

theorem physicalQuotientAction_eq_sourceAction
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) :
    physicalQuotientAction targetWeight state =
      shiftedCoefficientAction targetWeight
        (physicalQuotientRepresentative targetWeight state) := rfl

theorem physicalQuotientAction_mk
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    physicalQuotientAction targetWeight (Submodule.Quotient.mk potential) =
      shiftedCoefficientAction targetWeight potential := by
  simp [physicalQuotientAction, shiftedCoefficientAction,
    physicalQuotientSymbol_mk]

/-- Continuous descended Hessian pairing on quotient classes. -/
def physicalQuotientActionHessian
    (targetWeight : LatticeMode → Real) :
    PhysicalPotentialQuotient targetWeight →L[Real]
      PhysicalPotentialQuotient targetWeight →L[Real] Real :=
  let symbol := physicalQuotientSymbol targetWeight
  let raw : PhysicalPotentialQuotient targetWeight →ₗ[Real]
      PhysicalPotentialQuotient targetWeight →ₗ[Real] Real :=
    LinearMap.mk₂ Real
      (fun first second => ⟪symbol first, symbol second⟫_Real)
      (by intros; simp [inner_add_left])
      (by intros; simp [real_inner_smul_left])
      (by intros; simp [inner_add_right])
      (by intros; simp [real_inner_smul_right])
  LinearMap.mkContinuous₂ raw (‖symbol‖ ^ 2) (fun first second => by
    calc
      ‖⟪symbol first, symbol second⟫_Real‖ ≤
          ‖symbol first‖ * ‖symbol second‖ := norm_inner_le_norm _ _
      _ ≤ (‖symbol‖ * ‖first‖) * (‖symbol‖ * ‖second‖) := by
        exact mul_le_mul (symbol.le_opNorm first) (symbol.le_opNorm second)
          (norm_nonneg (symbol second))
          (mul_nonneg (norm_nonneg symbol) (norm_nonneg first))
      _ = ‖symbol‖ ^ 2 * ‖first‖ * ‖second‖ := by ring)

@[simp]
theorem physicalQuotientActionHessian_apply_apply
    (targetWeight : LatticeMode → Real)
    (first second : PhysicalPotentialQuotient targetWeight) :
    physicalQuotientActionHessian targetWeight first second =
      ⟪physicalQuotientSymbol targetWeight first,
        physicalQuotientSymbol targetWeight second⟫_Real := rfl

/-- On arbitrary representatives, the quotient Hessian is exactly the source
pullback Hessian pairing.  Thus both the action and its Hessian descend through
the same quotient map. -/
theorem physicalQuotientActionHessian_mk_mk
    (targetWeight : LatticeMode → Real)
    (first second : ShiftedPotentialHilbert targetWeight) :
    physicalQuotientActionHessian targetWeight
        (Submodule.Quotient.mk first) (Submodule.Quotient.mk second) =
      ⟪shiftedPullbackHessian targetWeight first, second⟫_Real := by
  rw [physicalQuotientActionHessian_apply_apply,
    physicalQuotientSymbol_mk, physicalQuotientSymbol_mk]
  exact (shiftedPullbackHessian_pairing targetWeight first second).symm

theorem physicalQuotientAction_hasFDerivAt
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) :
    HasFDerivAt (physicalQuotientAction targetWeight)
      (physicalQuotientActionHessian targetWeight state) state := by
  have hComposite :=
    (shiftedCoefficientAction_hasFDerivAt targetWeight
      (physicalQuotientRepresentative targetWeight state)).comp state
        (physicalQuotientRepresentative targetWeight).hasFDerivAt
  apply hComposite.congr_fderiv
  ext direction
  change
    ⟪shiftedPullbackHessian targetWeight
        (physicalQuotientRepresentative targetWeight state),
      physicalQuotientRepresentative targetWeight direction⟫_Real =
      ⟪physicalQuotientSymbol targetWeight state,
        physicalQuotientSymbol targetWeight direction⟫_Real
  exact shiftedPullbackHessian_pairing targetWeight _ _

theorem physicalQuotientAction_fderiv
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) :
    fderiv Real (physicalQuotientAction targetWeight) state =
      physicalQuotientActionHessian targetWeight state :=
  (physicalQuotientAction_hasFDerivAt targetWeight state).fderiv

/-- The actual second derivative of the quotient action is its descended
continuous Hessian at every base point. -/
theorem physicalQuotientAction_second_fderiv
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) :
    fderiv Real
        (fun point => fderiv Real (physicalQuotientAction targetWeight) point)
        state =
      physicalQuotientActionHessian targetWeight := by
  have hFirstDerivative :
      (fun point => fderiv Real (physicalQuotientAction targetWeight) point) =
        physicalQuotientActionHessian targetWeight := by
    funext point
    exact physicalQuotientAction_fderiv targetWeight point
  rw [hFirstDerivative]
  exact (physicalQuotientActionHessian targetWeight).hasFDerivAt.fderiv

theorem physicalQuotientActionHessian_nondegenerate
    (targetWeight : LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight) :
    physicalQuotientActionHessian targetWeight state state = 0 ↔
      state = 0 := by
  constructor
  · intro hHessian
    have hNorm : ‖physicalQuotientSymbol targetWeight state‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hHessian
    have hSymbol : physicalQuotientSymbol targetWeight state = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hNorm)
    have hRepresentative :
        physicalQuotientRepresentative targetWeight state = 0 := by
      have hKernel :=
        (shiftedSobolevLorentzGram_eq_zero_iff targetWeight
          (physicalQuotientRepresentative targetWeight state)).mp hSymbol
      apply Subtype.ext
      funext mode
      by_cases hMode : mode = 0
      · subst mode
        have hZero :=
          (physicalQuotientEquivZeroFree targetWeight state).2
        exact (mem_zeroModeProjection_ker_iff targetWeight _).mp hZero
      · exact hKernel mode hMode
    exact physicalQuotientRepresentative_injective targetWeight
      (by simpa using hRepresentative)
  · rintro rfl
    simp

theorem shifted_sobolev_quotient_same_action_hessian_gate
    (targetWeight : LatticeMode → Real) :
    (∀ state : PhysicalPotentialQuotient targetWeight,
      fderiv Real
          (fun point =>
            fderiv Real (physicalQuotientAction targetWeight) point)
          state = physicalQuotientActionHessian targetWeight) ∧
    (∀ state : PhysicalPotentialQuotient targetWeight,
      physicalQuotientActionHessian targetWeight state state = 0 ↔
        state = 0) ∧
    (∀ first second : ShiftedPotentialHilbert targetWeight,
      physicalQuotientActionHessian targetWeight
          (Submodule.Quotient.mk first) (Submodule.Quotient.mk second) =
        ⟪shiftedPullbackHessian targetWeight first, second⟫_Real) := by
  exact ⟨physicalQuotientAction_second_fderiv targetWeight,
    physicalQuotientActionHessian_nondegenerate targetWeight,
    physicalQuotientActionHessian_mk_mk targetWeight⟩

end

end P0EFTJanusShiftedSobolevQuotientSameActionHessian
end JanusFormal
