import Mathlib.Topology.Algebra.Module.Complement
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevPullbackHessian

/-!
# Topological physical quotient of the shifted lattice-Sobolev symbol

The only kernel of the shifted Lorentz--Gram operator is its finite zero
Fourier mode.  A bounded idempotent projection splits that mode from the
closed zero-free subspace.  Consequently the actual normed quotient by
`ker J` is continuously linearly equivalent to the zero-free representatives,
where the pullback Hessian is positive definite.

This remains the periodic `Z^4` coefficient model, not the global Janus gauge
quotient.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevPhysicalQuotient

set_option autoImplicit false

noncomputable section

open scoped ENNReal lp InnerProductSpace
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusShiftedSobolevLatticeLorentzGram
open P0EFTJanusShiftedSobolevPullbackHessian

/-- Projection of a shifted potential onto its four-dimensional zero-mode
fiber. -/
def potentialZeroModeFiber
    {targetWeight : LatticeMode → Real}
    (potential : ShiftedPotentialHilbert targetWeight)
    (mode : LatticeMode) : PotentialFiber :=
  if mode = 0 then potential mode else 0

theorem potentialZeroModeFiber_norm_le
    {targetWeight : LatticeMode → Real}
    (potential : ShiftedPotentialHilbert targetWeight)
    (mode : LatticeMode) :
    ‖potentialZeroModeFiber potential mode‖ ≤ ‖potential mode‖ := by
  by_cases hMode : mode = 0 <;>
    simp [potentialZeroModeFiber, hMode]

theorem potentialZeroModeFiber_memℓp
    {targetWeight : LatticeMode → Real}
    (potential : ShiftedPotentialHilbert targetWeight) :
    Memℓp (potentialZeroModeFiber potential) 2 :=
  potential.2.mono' (potentialZeroModeFiber_norm_le potential)

/-- Bounded zero-mode projection. -/
def potentialZeroModeProjection
    (targetWeight : LatticeMode → Real) :
    ShiftedPotentialHilbert targetWeight →L[Real]
      ShiftedPotentialHilbert targetWeight :=
  LinearMap.mkContinuous
    { toFun := fun potential =>
        ⟨potentialZeroModeFiber potential,
          potentialZeroModeFiber_memℓp potential⟩
      map_add' := by
        intro first second
        ext mode index
        by_cases hMode : mode = 0
        · subst mode
          simp [potentialZeroModeFiber]
        · simp [potentialZeroModeFiber, hMode]
      map_smul' := by
        intro scalar potential
        ext mode index
        by_cases hMode : mode = 0
        · subst mode
          simp [potentialZeroModeFiber]
        · simp [potentialZeroModeFiber, hMode] }
    1 (fun potential => by
      change ‖(⟨potentialZeroModeFiber potential,
          potentialZeroModeFiber_memℓp potential⟩ :
        ShiftedPotentialHilbert targetWeight)‖ ≤ 1 * ‖potential‖
      have hBound :
          ‖(⟨potentialZeroModeFiber potential,
              potentialZeroModeFiber_memℓp potential⟩ :
            ShiftedPotentialHilbert targetWeight)‖ ≤ ‖potential‖ := by
        apply lp.norm_mono (by norm_num)
        exact potentialZeroModeFiber_norm_le potential
      simpa only [one_mul] using hBound)

theorem potentialZeroModeProjection_opNorm_le
    (targetWeight : LatticeMode → Real) :
    ‖potentialZeroModeProjection targetWeight‖ ≤ 1 := by
  unfold potentialZeroModeProjection
  apply LinearMap.mkContinuous_norm_le
  norm_num

theorem potentialZeroModeProjection_idempotent
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    potentialZeroModeProjection targetWeight
        (potentialZeroModeProjection targetWeight potential) =
      potentialZeroModeProjection targetWeight potential := by
  ext mode index
  by_cases hMode : mode = 0 <;>
    simp [potentialZeroModeProjection, potentialZeroModeFiber, hMode]

theorem potentialZeroModeProjection_isIdempotentElem
    (targetWeight : LatticeMode → Real) :
    IsIdempotentElem (potentialZeroModeProjection targetWeight) := by
  apply ContinuousLinearMap.ext
  intro potential
  exact potentialZeroModeProjection_idempotent targetWeight potential

/-- Closed topological complement: zero modes versus zero-free modes. -/
theorem zeroMode_range_isTopCompl_ker
    (targetWeight : LatticeMode → Real) :
    Submodule.IsTopCompl (potentialZeroModeProjection targetWeight).range
      (potentialZeroModeProjection targetWeight).ker :=
  ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (potentialZeroModeProjection_isIdempotentElem targetWeight)

/-- The complemented zero-mode range is closed.  Registering this proof makes
the quotient carry Mathlib's genuine `NormedAddCommGroup` structure, rather
than only its default seminormed quotient structure. -/
instance potentialZeroModeProjection_range_isClosed
    (targetWeight : LatticeMode → Real) :
    IsClosed ((potentialZeroModeProjection targetWeight).range :
      Set (ShiftedPotentialHilbert targetWeight)) :=
  (zeroMode_range_isTopCompl_ker targetWeight).isClosed

theorem mem_zeroModeProjection_ker_iff
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    potential ∈ (potentialZeroModeProjection targetWeight).ker ↔
      potential 0 = 0 := by
  change potentialZeroModeProjection targetWeight potential = 0 ↔
    potential 0 = 0
  constructor
  · intro hProjection
    have hZero := congrArg
      (fun state : ShiftedPotentialHilbert targetWeight => state 0) hProjection
    simpa [potentialZeroModeProjection, potentialZeroModeFiber] using hZero
  · intro hZero
    apply Subtype.ext
    funext mode
    by_cases hMode : mode = 0
    · subst mode
      simpa [potentialZeroModeProjection, potentialZeroModeFiber] using hZero
    · simp [potentialZeroModeProjection, potentialZeroModeFiber, hMode]

/-- The projected zero-mode range is exactly the kernel of the physical
shifted symbol. -/
theorem zeroModeProjection_range_eq_symbol_ker
    (targetWeight : LatticeMode → Real) :
    (potentialZeroModeProjection targetWeight).range =
      (shiftedSobolevLorentzGram targetWeight).ker := by
  ext potential
  constructor
  · rintro ⟨source, rfl⟩
    change shiftedSobolevLorentzGram targetWeight
      (potentialZeroModeProjection targetWeight source) = 0
    rw [shiftedSobolevLorentzGram_eq_zero_iff]
    intro mode hMode
    simp [potentialZeroModeProjection, potentialZeroModeFiber, hMode]
  · intro hKernel
    change shiftedSobolevLorentzGram targetWeight potential = 0 at hKernel
    have hModes :=
      (shiftedSobolevLorentzGram_eq_zero_iff targetWeight potential).mp hKernel
    refine ⟨potential, ?_⟩
    apply Subtype.ext
    funext mode
    by_cases hMode : mode = 0
    · subst mode
      simp [potentialZeroModeProjection, potentialZeroModeFiber]
    · simp [potentialZeroModeProjection, potentialZeroModeFiber, hMode,
        hModes mode hMode]

abbrev PhysicalPotentialQuotient
    (targetWeight : LatticeMode → Real) :=
  (ShiftedPotentialHilbert targetWeight) ⧸
    (potentialZeroModeProjection targetWeight).range

abbrev ZeroFreePotentialSubspace
    (targetWeight : LatticeMode → Real) :=
  (potentialZeroModeProjection targetWeight).ker

/-- The normed quotient by `ker J` is an actual topological vector space,
canonically represented by zero-free coefficients. -/
def physicalQuotientEquivZeroFree
    (targetWeight : LatticeMode → Real) :
    PhysicalPotentialQuotient targetWeight ≃L[Real]
      ZeroFreePotentialSubspace targetWeight :=
  Submodule.quotientEquivOfIsTopCompl
    (potentialZeroModeProjection targetWeight).range
    (potentialZeroModeProjection targetWeight).ker
    (zeroMode_range_isTopCompl_ker targetWeight)

/-- On the canonical representatives, the pullback Hessian is nondegenerate. -/
theorem pullbackHessian_nondegenerate_on_physical_representatives
    (targetWeight : LatticeMode → Real)
    (potential : ZeroFreePotentialSubspace targetWeight) :
    ⟪shiftedPullbackHessian targetWeight potential.1, potential.1⟫_Real = 0 ↔
      potential = 0 := by
  have hZero : potential.1 0 = 0 :=
    (mem_zeroModeProjection_ker_iff targetWeight potential.1).mp potential.2
  constructor
  · intro hHessian
    apply Subtype.ext
    exact (shiftedPullbackHessian_positiveDefinite_of_zeroModeFree
      targetWeight potential.1 hZero).mp hHessian
  · intro hPotential
    apply (shiftedPullbackHessian_positiveDefinite_of_zeroModeFree
      targetWeight potential.1 hZero).mpr
    exact congrArg Subtype.val hPotential

theorem shifted_sobolev_physical_quotient_gate
    (targetWeight : LatticeMode → Real) :
    Submodule.IsTopCompl (potentialZeroModeProjection targetWeight).range
        (potentialZeroModeProjection targetWeight).ker ∧
    (potentialZeroModeProjection targetWeight).range =
      (shiftedSobolevLorentzGram targetWeight).ker ∧
    Nonempty (PhysicalPotentialQuotient targetWeight ≃L[Real]
      ZeroFreePotentialSubspace targetWeight) ∧
    (∀ potential : ZeroFreePotentialSubspace targetWeight,
      ⟪shiftedPullbackHessian targetWeight potential.1, potential.1⟫_Real = 0 ↔
        potential = 0) := by
  exact ⟨zeroMode_range_isTopCompl_ker targetWeight,
    zeroModeProjection_range_eq_symbol_ker targetWeight,
    ⟨physicalQuotientEquivZeroFree targetWeight⟩,
    pullbackHessian_nondegenerate_on_physical_representatives targetWeight⟩

end

end P0EFTJanusShiftedSobolevPhysicalQuotient
end JanusFormal
