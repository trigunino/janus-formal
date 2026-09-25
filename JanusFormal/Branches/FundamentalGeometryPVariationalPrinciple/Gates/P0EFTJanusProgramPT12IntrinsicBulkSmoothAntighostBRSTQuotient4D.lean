import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The native smooth BRST differential descends through the pure antighost
subspace. This is an algebraic smooth-core quotient, not a continuous extension
of BRST to the completed C² bulk core or an assertion about cohomology. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostBRSTQuotient4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotient4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D

variable (period : Real) (hPeriod : period ≠ 0)
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod

def intrinsicBulkPureAntighostStateLinearMap :
    GlobalDiffeomorphismAntighostField period hPeriod →ₗ[Real] State where
  toFun := intrinsicBulkPureAntighostBRSTState period hPeriod
  map_add' _ _ := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (zero_add _).symm
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · exact (zero_add _).symm
      · rfl
      · exact (zero_add _).symm
  map_smul' scalar _ := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (smul_zero scalar).symm
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · exact (smul_zero scalar).symm
      · rfl
      · exact (smul_zero scalar).symm

def intrinsicBulkSmoothAntighostStateRadical : Submodule Real State :=
  (intrinsicBulkPureAntighostStateLinearMap period hPeriod).range

theorem intrinsicBulkSmoothAntighostStateRadical_mem_iff (state : State) :
    state ∈ intrinsicBulkSmoothAntighostStateRadical period hPeriod ↔
      ∃ antighost, state = intrinsicBulkPureAntighostBRSTState period hPeriod antighost := by
  constructor
  · rintro ⟨antighost, rfl⟩
    exact ⟨antighost, rfl⟩
  · rintro ⟨antighost, rfl⟩
    exact ⟨antighost, rfl⟩

def intrinsicBulkSmoothBRSTLinearMap : State →ₗ[Real] State :=
  diffeomorphismBRSTLinearMap period hPeriod (fun sector => match sector with
    | .plus => (intrinsicBulkGeometry period hPeriod).plusMetric
    | .minus => (intrinsicBulkGeometry period hPeriod).minusMetric)

@[simp] theorem intrinsicBulkSmoothBRSTLinearMap_apply (state : State) :
    intrinsicBulkSmoothBRSTLinearMap period hPeriod state =
      intrinsicBulkSmoothBRST period hPeriod state := rfl

theorem intrinsicBulkSmoothAntighostStateRadical_le_ker :
    intrinsicBulkSmoothAntighostStateRadical period hPeriod ≤
      (intrinsicBulkSmoothBRSTLinearMap period hPeriod).ker := by
  rintro _ ⟨antighost, rfl⟩
  exact intrinsicBulkSmoothBRST_pureAntighost period hPeriod antighost

theorem intrinsicBulkSmoothAntighostStateRadical_BRST_stable :
    intrinsicBulkSmoothAntighostStateRadical period hPeriod ≤
      (intrinsicBulkSmoothAntighostStateRadical period hPeriod).comap
        (intrinsicBulkSmoothBRSTLinearMap period hPeriod) := by
  intro state hState
  change intrinsicBulkSmoothBRSTLinearMap period hPeriod state ∈
    intrinsicBulkSmoothAntighostStateRadical period hPeriod
  have hZero : intrinsicBulkSmoothBRSTLinearMap period hPeriod state = 0 :=
    intrinsicBulkSmoothAntighostStateRadical_le_ker period hPeriod hState
  rw [hZero]
  exact (intrinsicBulkSmoothAntighostStateRadical period hPeriod).zero_mem

abbrev IntrinsicBulkSmoothAntighostBRSTQuotient :=
  State ⧸ intrinsicBulkSmoothAntighostStateRadical period hPeriod

def intrinsicBulkSmoothAntighostQuotientMap :
    State →ₗ[Real] IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod :=
  (intrinsicBulkSmoothAntighostStateRadical period hPeriod).mkQ

def intrinsicBulkSmoothAntighostQuotientBRST :
    IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod →ₗ[Real]
      IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod :=
  (intrinsicBulkSmoothAntighostStateRadical period hPeriod).mapQ
    (intrinsicBulkSmoothAntighostStateRadical period hPeriod)
    (intrinsicBulkSmoothBRSTLinearMap period hPeriod)
    (intrinsicBulkSmoothAntighostStateRadical_BRST_stable period hPeriod)

@[simp] theorem intrinsicBulkSmoothAntighostQuotientBRST_mk (state : State) :
    intrinsicBulkSmoothAntighostQuotientBRST period hPeriod
      (intrinsicBulkSmoothAntighostQuotientMap period hPeriod state) =
    intrinsicBulkSmoothAntighostQuotientMap period hPeriod
      (intrinsicBulkSmoothBRST period hPeriod state) := rfl

theorem intrinsicBulkSmoothAntighostQuotientBRST_intertwining :
    (intrinsicBulkSmoothAntighostQuotientBRST period hPeriod).comp
      (intrinsicBulkSmoothAntighostQuotientMap period hPeriod) =
    (intrinsicBulkSmoothAntighostQuotientMap period hPeriod).comp
      (intrinsicBulkSmoothBRSTLinearMap period hPeriod) :=
  Submodule.mapQ_mkQ _ _ _

theorem intrinsicBulkSmoothAntighostQuotientBRST_square_zero
    (state : IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod) :
    intrinsicBulkSmoothAntighostQuotientBRST period hPeriod
      (intrinsicBulkSmoothAntighostQuotientBRST period hPeriod state) = 0 := by
  obtain ⟨state, rfl⟩ :=
    (intrinsicBulkSmoothAntighostStateRadical period hPeriod).mkQ_surjective state
  change (intrinsicBulkSmoothAntighostStateRadical period hPeriod).mkQ
    (intrinsicBulkSmoothBRSTLinearMap period hPeriod
      (intrinsicBulkSmoothBRSTLinearMap period hPeriod state)) = 0
  have hSquare : intrinsicBulkSmoothBRSTLinearMap period hPeriod
      (intrinsicBulkSmoothBRSTLinearMap period hPeriod state) = 0 :=
    diffeomorphismBRSTLinearMap_square_zero period hPeriod _ state
  exact (congrArg (intrinsicBulkSmoothAntighostStateRadical period hPeriod).mkQ hSquare).trans
    (intrinsicBulkSmoothAntighostStateRadical period hPeriod).mkQ.map_zero

/-- The closed C² antighost block removes precisely the same smooth states. -/
theorem intrinsicBulkSmoothBRSTInsertion_mem_antighostRadical_iff
    (couplings : GlobalCandidateAActionCouplings) (state : State) :
    intrinsicBulkSmoothBRSTInsertion period hPeriod couplings state ∈
        intrinsicBulkAntighostRadical period hPeriod couplings ↔
      ∃ antighost, state = intrinsicBulkPureAntighostBRSTState period hPeriod antighost := by
  constructor
  · intro hState
    obtain ⟨coefficients, hEqual⟩ :=
      (intrinsicBulkAntighostRadical_mem_iff period hPeriod couplings _).mp hState
    refine ⟨state.nonminimal.antighost, ?_⟩
    apply intrinsicBulkSmoothBRSTInsertion_injective period hPeriod couplings
    have hCoefficient : intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod
        ⟨state.nonminimal.antighost.field⟩ = coefficients :=
      congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.2.2.2.1) hEqual
    exact hEqual.trans ((congrArg
      (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings)
      hCoefficient.symm).trans
        (intrinsicBulkSmoothAntighostInsertion_eq_coefficients period hPeriod couplings
          state.nonminimal.antighost).symm)
  · rintro ⟨antighost, rfl⟩
    exact (intrinsicBulkAntighostRadical_mem_iff period hPeriod couplings _).mpr
      ⟨intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod ⟨antighost.field⟩,
        intrinsicBulkSmoothAntighostInsertion_eq_coefficients period hPeriod couplings antighost⟩

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostBRSTQuotient4D
