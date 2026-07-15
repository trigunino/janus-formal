import Mathlib

namespace JanusFormal
namespace P0EFTJanusCoupledSectorHelmholtzSelection

set_option autoImplicit false

/--
Three-sector linear operator.  The fields are interpreted as an even normal
mode, an even trace/tensor mode and a PT-odd mode.  The interpretation is only
used by the PT theorem; the Helmholtz theorem is purely algebraic.
-/
@[ext] structure LinearOperator3 where
  nn : ℝ
  nt : ℝ
  no : ℝ
  tn : ℝ
  tt : ℝ
  trOdd : ℝ
  on : ℝ
  ot : ℝ
  oo : ℝ

/-- Pairwise reciprocity conditions for a Hessian. -/
def FormallySelfAdjoint
    (operator : LinearOperator3) : Prop :=
  operator.nt = operator.tn /\
  operator.no = operator.on /\
  operator.trOdd = operator.ot

/-- Quadratic potential for the three sectors. -/
@[ext] structure QuadraticPotential3 where
  nn : ℝ
  tt : ℝ
  oo : ℝ
  nt : ℝ
  no : ℝ
  trOdd : ℝ

/-- Value of the quadratic potential. -/
noncomputable def potentialValue
    (potential : QuadraticPotential3)
    (normal trace odd : ℝ) : ℝ :=
  potential.nn * normal ^ 2 / 2 +
    potential.tt * trace ^ 2 / 2 +
    potential.oo * odd ^ 2 / 2 +
    potential.nt * normal * trace +
    potential.no * normal * odd +
    potential.trOdd * trace * odd

/-- Hessian operator of the potential. -/
def hessianOperator
    (potential : QuadraticPotential3) : LinearOperator3 :=
  { nn := potential.nn
    nt := potential.nt
    no := potential.no
    tn := potential.nt
    tt := potential.tt
    trOdd := potential.trOdd
    on := potential.no
    ot := potential.trOdd
    oo := potential.oo }

/-- Every quadratic Hessian satisfies all reciprocity conditions. -/
theorem hessian_formally_self_adjoint
    (potential : QuadraticPotential3) :
    FormallySelfAdjoint (hessianOperator potential) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical zero-affine primitive of a self-adjoint three-sector operator. -/
def canonicalPotential
    (operator : LinearOperator3) : QuadraticPotential3 :=
  { nn := operator.nn
    tt := operator.tt
    oo := operator.oo
    nt := operator.nt
    no := operator.no
    trOdd := operator.trOdd }

/-- A self-adjoint operator is the Hessian of its canonical potential. -/
theorem canonical_potential_hessian
    (operator : LinearOperator3)
    (hSelfAdjoint : FormallySelfAdjoint operator) :
    hessianOperator (canonicalPotential operator) = operator := by
  rcases hSelfAdjoint with ⟨hNT, hNO, hTO⟩
  apply LinearOperator3.ext <;>
    simp [hessianOperator, canonicalPotential, hNT, hNO, hTO]

/-- Finite-dimensional three-sector Helmholtz theorem. -/
theorem helmholtz_realizability_iff
    (operator : LinearOperator3) :
    (∃ potential : QuadraticPotential3,
      hessianOperator potential = operator) ↔
      FormallySelfAdjoint operator := by
  constructor
  · rintro ⟨potential, rfl⟩
    exact hessian_formally_self_adjoint potential
  · intro hSelfAdjoint
    exact ⟨canonicalPotential operator,
      canonical_potential_hessian operator hSelfAdjoint⟩

/-- Failure of any reciprocal cross coupling blocks a variational origin. -/
theorem nonreciprocal_cross_coupling_not_variational
    (operator : LinearOperator3)
    (hFailure :
      operator.nt ≠ operator.tn \/
      operator.no ≠ operator.on \/
      operator.trOdd ≠ operator.ot) :
    Not (∃ potential : QuadraticPotential3,
      hessianOperator potential = operator) := by
  intro hPotential
  have hSelfAdjoint :=
    (helmholtz_realizability_iff operator).mp hPotential
  rcases hFailure with hFailure | hFailure | hFailure
  · exact hFailure hSelfAdjoint.1
  · exact hFailure hSelfAdjoint.2.1
  · exact hFailure hSelfAdjoint.2.2

/-- PT acts trivially on the first two sectors and reverses the third. -/
def PTInvariant
    (potential : QuadraticPotential3) : Prop :=
  ∀ normal trace odd : ℝ,
    potentialValue potential normal trace (-odd) =
      potentialValue potential normal trace odd

/-- Vanishing of the two even-odd couplings is sufficient for PT invariance. -/
theorem mixed_odd_couplings_zero_imply_pt_invariant
    (potential : QuadraticPotential3)
    (hNO : potential.no = 0)
    (hTO : potential.trOdd = 0) :
    PTInvariant potential := by
  intro normal trace odd
  unfold potentialValue
  rw [hNO, hTO]
  ring

/-- PT invariance forces the normal-odd coupling to vanish. -/
theorem pt_invariant_forces_normal_odd_zero
    (potential : QuadraticPotential3)
    (hPT : PTInvariant potential) :
    potential.no = 0 := by
  have hTest := hPT 1 0 1
  unfold potentialValue at hTest
  nlinarith

/-- PT invariance forces the trace-odd coupling to vanish. -/
theorem pt_invariant_forces_trace_odd_zero
    (potential : QuadraticPotential3)
    (hPT : PTInvariant potential) :
    potential.trOdd = 0 := by
  have hTest := hPT 0 1 1
  unfold potentialValue at hTest
  nlinarith

/-- Exact PT classification of the quadratic cross couplings. -/
theorem pt_invariant_iff_mixed_odd_couplings_zero
    (potential : QuadraticPotential3) :
    PTInvariant potential ↔
      potential.no = 0 /\ potential.trOdd = 0 := by
  constructor
  · intro hPT
    exact ⟨pt_invariant_forces_normal_odd_zero potential hPT,
      pt_invariant_forces_trace_odd_zero potential hPT⟩
  · rintro ⟨hNO, hTO⟩
    exact mixed_odd_couplings_zero_imply_pt_invariant
      potential hNO hTO

/--
Exact quadratic coupled-sector selection criterion: an operator is the Hessian
of a PT-invariant potential precisely when it is reciprocal and its two
even-to-odd entries vanish.
-/
theorem helmholtz_pt_realizability_iff
    (operator : LinearOperator3) :
    (∃ potential : QuadraticPotential3,
      hessianOperator potential = operator /\
      PTInvariant potential) ↔
      FormallySelfAdjoint operator /\
      operator.no = 0 /\ operator.trOdd = 0 := by
  constructor
  · rintro ⟨potential, rfl, hPT⟩
    exact ⟨hessian_formally_self_adjoint potential,
      pt_invariant_forces_normal_odd_zero potential hPT,
      pt_invariant_forces_trace_odd_zero potential hPT⟩
  · rintro ⟨hSelfAdjoint, hNO, hTO⟩
    refine ⟨canonicalPotential operator,
      canonical_potential_hessian operator hSelfAdjoint, ?_⟩
    exact mixed_odd_couplings_zero_imply_pt_invariant
      (canonicalPotential operator) hNO hTO

/-- Equality of the three diagonal/principal coefficients. -/
def SameDiagonal
    (first second : QuadraticPotential3) : Prop :=
  first.nn = second.nn /\
  first.tt = second.tt /\
  first.oo = second.oo

/-- Unmixed PT-even candidate. -/
def unmixedCandidate : QuadraticPotential3 :=
  { nn := 1
    tt := 1
    oo := 1
    nt := 0
    no := 0
    trOdd := 0 }

/-- Same diagonal and PT parity, but with an even-even interaction. -/
def evenMixedCandidate : QuadraticPotential3 :=
  { nn := 1
    tt := 1
    oo := 1
    nt := 1
    no := 0
    trOdd := 0 }

/-- Both candidates obey Helmholtz and PT, yet are different. -/
theorem fixed_diagonal_helmholtz_pt_data_do_not_select_unique_action :
    SameDiagonal unmixedCandidate evenMixedCandidate /\
    FormallySelfAdjoint (hessianOperator unmixedCandidate) /\
    FormallySelfAdjoint (hessianOperator evenMixedCandidate) /\
    PTInvariant unmixedCandidate /\
    PTInvariant evenMixedCandidate /\
    unmixedCandidate ≠ evenMixedCandidate := by
  constructor
  · exact ⟨rfl, rfl, rfl⟩
  · constructor
    · exact hessian_formally_self_adjoint unmixedCandidate
    · constructor
      · exact hessian_formally_self_adjoint evenMixedCandidate
      · constructor
        · exact mixed_odd_couplings_zero_imply_pt_invariant
            unmixedCandidate rfl rfl
        · constructor
          · exact mixed_odd_couplings_zero_imply_pt_invariant
              evenMixedCandidate rfl rfl
          · intro hEqual
            have hNT := congrArg QuadraticPotential3.nt hEqual
            norm_num [unmixedCandidate, evenMixedCandidate] at hNT

/--
P-C/P-D status.  Helmholtz reciprocity and PT remove non-variational and
opposite-parity couplings, but they leave diagonal masses/curvature couplings
and same-parity interactions free.  A parent action or microscopic matching law
must select those remaining coefficients.
-/
structure CoupledSectorPhysicalStatus where
  fieldSectorsDerived : Prop
  ptParitiesDerived : Prop
  fullLinearizedEulerOperatorDerived : Prop
  reciprocalCouplingsProved : Prop
  oppositeParityMixingExcluded : Prop
  sameParityCouplingsDerivedMicroscopically : Prop
  diagonalLowerOrderTermsDerived : Prop
  finiteCountertermsFixed : Prop
  nonlinearHelmholtzConditionsProved : Prop


def coupledSectorPhysicalClosure
    (s : CoupledSectorPhysicalStatus) : Prop :=
  s.fieldSectorsDerived /\
  s.ptParitiesDerived /\
  s.fullLinearizedEulerOperatorDerived /\
  s.reciprocalCouplingsProved /\
  s.oppositeParityMixingExcluded /\
  s.sameParityCouplingsDerivedMicroscopically /\
  s.diagonalLowerOrderTermsDerived /\
  s.finiteCountertermsFixed /\
  s.nonlinearHelmholtzConditionsProved

end P0EFTJanusCoupledSectorHelmholtzSelection
end JanusFormal
