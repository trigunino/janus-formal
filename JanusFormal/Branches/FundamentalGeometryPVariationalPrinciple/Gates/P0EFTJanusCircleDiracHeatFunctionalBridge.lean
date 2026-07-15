import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleUnboundedDiracDomain

/-!
# Spectral heat bridge for the unbounded circle Dirac operator

This gate connects the maximal-domain self-adjoint Fourier--Dirac operator to
the Gaussian sums in `P0EFTJanusCircleDiracHeatTraceCancellation`.  Every
Fourier basis vector lies in the domain, its first image lies in the domain
again, and applying the operator twice gives the derived squared eigenvalue.
Consequently the heat weight obtained from this genuine operator action is
exactly the previously defined algebraic weight.  Both finite cutoffs and the
summable diagonal spectral traces therefore agree with the existing sums.

The construction is deliberately spectral: it defines the heat action on
each Fourier eigenvector and sums its diagonal coefficients.  It does not
construct the global operator `exp (-t D^2)` by functional calculus, prove a
semigroup theorem on the full Hilbert space, or establish trace-class results
beyond the explicit summable diagonal series.
-/

namespace JanusFormal
namespace P0EFTJanusCircleDiracHeatFunctionalBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open scoped BigOperators ComplexConjugate LinearPMap

/-- A Fourier basis vector packaged in the maximal Dirac domain. -/
def circleDiracBasisDomainState
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    (circleUnboundedDirac fold twist).domain :=
  ⟨circleFourierBasis mode,
    circleFourierBasis_mem_domain fold twist mode⟩

@[simp]
theorem circleDiracBasisDomainState_coe
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ((circleDiracBasisDomainState fold twist mode :
      (circleUnboundedDirac fold twist).domain) : CircleHilbert) =
      circleFourierBasis mode :=
  rfl

/-- Applying the unbounded Dirac operator once to a Fourier vector remains in
its maximal domain, so the second application is legitimate. -/
theorem circleUnboundedDirac_basis_image_mem_domain
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleUnboundedDirac fold twist
        (circleDiracBasisDomainState fold twist mode) ∈
      circleDiracDomain fold twist := by
  rw [show circleUnboundedDirac fold twist
      (circleDiracBasisDomainState fold twist mode) =
        complexDiracEigenvalue fold twist mode • circleFourierBasis mode by
    simpa [circleDiracBasisDomainState] using
      circleUnboundedDirac_on_basis fold twist mode]
  exact (circleDiracDomain fold twist).smul_mem
    (complexDiracEigenvalue fold twist mode)
    (circleFourierBasis_mem_domain fold twist mode)

/-- The first Dirac image, packaged in the domain for a second application. -/
def circleDiracBasisImageDomainState
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    (circleUnboundedDirac fold twist).domain :=
  ⟨circleUnboundedDirac fold twist
      (circleDiracBasisDomainState fold twist mode),
    circleUnboundedDirac_basis_image_mem_domain fold twist mode⟩

/-- The genuine maximal-domain operator squares spectrally on every Fourier
mode. -/
theorem circleUnboundedDirac_squared_on_basis
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleUnboundedDirac fold twist
        (circleDiracBasisImageDomainState fold twist mode) =
      (complexDiracEigenvalue fold twist mode) ^ 2 •
        circleFourierBasis mode := by
  have hFirst :
      circleUnboundedDirac fold twist
          (circleDiracBasisDomainState fold twist mode) =
        complexDiracEigenvalue fold twist mode • circleFourierBasis mode := by
    simpa [circleDiracBasisDomainState] using
      circleUnboundedDirac_on_basis fold twist mode
  ext other
  rw [circleUnboundedDirac_apply]
  change complexDiracEigenvalue fold twist other *
      (circleUnboundedDirac fold twist
        (circleDiracBasisDomainState fold twist mode)) other =
      ((complexDiracEigenvalue fold twist mode) ^ 2 •
        circleFourierBasis mode) other
  rw [hFirst]
  by_cases hOther : other = mode
  · subst other
    simp [circleFourierBasis_eq_single]
    ring
  · simp [circleFourierBasis_eq_single, lp.single_apply, hOther]

/-- Squared eigenvalue read off from the diagonal matrix coefficient of the
actual twice-applied unbounded operator. -/
def circleOperatorSquaredEigenvalue
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℝ :=
  Complex.re (inner ℂ (circleFourierBasis mode)
    (circleUnboundedDirac fold twist
      (circleDiracBasisImageDomainState fold twist mode)))

theorem circleOperatorSquaredEigenvalue_eq_eigenvalueSq
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleOperatorSquaredEigenvalue fold twist mode =
      eigenvalueSq fold twist mode := by
  rw [circleOperatorSquaredEigenvalue,
    circleUnboundedDirac_squared_on_basis,
    circleFourierBasis_inner_left]
  simp [circleFourierBasis_eq_single, complexDiracEigenvalue, eigenvalueSq,
    pow_two]

/-- Gaussian weight derived from the squared spectral coefficient of the
unbounded operator. -/
def circleOperatorHeatWeight
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℝ :=
  Real.exp (-time.1 * circleOperatorSquaredEigenvalue fold twist mode)

@[simp]
theorem circleOperatorHeatWeight_eq_heatWeight
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleOperatorHeatWeight time fold twist mode =
      heatWeight time fold twist mode := by
  rw [circleOperatorHeatWeight,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  rfl

/-- Spectral heat action on one Fourier eigenvector.  This is not asserted to
be a globally constructed operator exponential. -/
def circleSpectralHeatMode
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    CircleHilbert :=
  (circleOperatorHeatWeight time fold twist mode : ℂ) •
    circleFourierBasis mode

theorem circleSpectralHeatMode_diagonal
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    Complex.re (inner ℂ (circleFourierBasis mode)
      (circleSpectralHeatMode time fold twist mode)) =
        circleOperatorHeatWeight time fold twist mode := by
  rw [circleFourierBasis_inner_left]
  change Complex.re ((circleOperatorHeatWeight time fold twist mode : ℂ) *
    circleFourierBasis mode mode) =
      circleOperatorHeatWeight time fold twist mode
  rw [circleFourierBasis_eq_single]
  simp

theorem circleOperatorHeatWeight_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (circleOperatorHeatWeight time fold twist) := by
  refine (heatWeight_summable time fold twist).congr (fun mode => ?_)
  exact (circleOperatorHeatWeight_eq_heatWeight time fold twist mode).symm

/-- Infinite diagonal spectral trace derived from the unbounded operator's
Fourier eigenvectors. -/
def circleOperatorEvenHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  ∑' mode : ℤ, Complex.re (inner ℂ (circleFourierBasis mode)
    (circleSpectralHeatMode time fold twist mode))

theorem circleOperatorEvenHeatTrace_eq_evenHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleOperatorEvenHeatTrace time fold twist =
      evenHeatTrace time fold twist := by
  unfold circleOperatorEvenHeatTrace evenHeatTrace
  apply tsum_congr
  intro mode
  rw [circleSpectralHeatMode_diagonal,
    circleOperatorHeatWeight_eq_heatWeight]

/-- Chiral diagonal spectral trace derived from the same eigenvectors. -/
def circleOperatorChiralHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  ∑' mode : ℤ, fold.chirality *
    Complex.re (inner ℂ (circleFourierBasis mode)
      (circleSpectralHeatMode time fold twist mode))

theorem circleOperatorChiralHeatTrace_eq_regulatedChiralTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleOperatorChiralHeatTrace time fold twist =
      regulatedChiralTrace time fold twist := by
  unfold circleOperatorChiralHeatTrace regulatedChiralTrace
  apply tsum_congr
  intro mode
  rw [circleSpectralHeatMode_diagonal,
    circleOperatorHeatWeight_eq_heatWeight]
  rfl

/-- Finite diagonal trace on the symmetric Fourier cutoff. -/
def circleOperatorCutoffEvenHeatTrace
    (cutoff : ℕ) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) : ℝ :=
  ∑ mode ∈ symmetricCutoff cutoff,
    Complex.re (inner ℂ (circleFourierBasis mode)
      (circleSpectralHeatMode time fold twist mode))

theorem circleOperatorCutoffEvenHeatTrace_eq_cutoffEvenHeatTrace
    (cutoff : ℕ) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) :
    circleOperatorCutoffEvenHeatTrace cutoff time fold twist =
      cutoffEvenHeatTrace cutoff time fold twist := by
  unfold circleOperatorCutoffEvenHeatTrace cutoffEvenHeatTrace
  apply Finset.sum_congr rfl
  intro mode hMode
  rw [circleSpectralHeatMode_diagonal,
    circleOperatorHeatWeight_eq_heatWeight]

/-- Finite chiral diagonal trace on the symmetric Fourier cutoff. -/
def circleOperatorCutoffChiralHeatTrace
    (cutoff : ℕ) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) : ℝ :=
  ∑ mode ∈ symmetricCutoff cutoff, fold.chirality *
    Complex.re (inner ℂ (circleFourierBasis mode)
      (circleSpectralHeatMode time fold twist mode))

theorem circleOperatorCutoffChiralHeatTrace_eq_cutoffChiralHeatTrace
    (cutoff : ℕ) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) :
    circleOperatorCutoffChiralHeatTrace cutoff time fold twist =
      cutoffChiralHeatTrace cutoff time fold twist := by
  unfold circleOperatorCutoffChiralHeatTrace cutoffChiralHeatTrace
  apply Finset.sum_congr rfl
  intro mode hMode
  rw [circleSpectralHeatMode_diagonal,
    circleOperatorHeatWeight_eq_heatWeight]
  rfl

/-- The operator-derived finite chiral cutoffs cancel between PT folds. -/
theorem circleOperatorCutoffChiralHeatTrace_positive_add_pt_eq_zero
    (cutoff : ℕ) (time : HeatTime) (twist : CircleTwist) :
    circleOperatorCutoffChiralHeatTrace cutoff time .positive twist +
      circleOperatorCutoffChiralHeatTrace cutoff time .pt twist = 0 := by
  rw [circleOperatorCutoffChiralHeatTrace_eq_cutoffChiralHeatTrace,
    circleOperatorCutoffChiralHeatTrace_eq_cutoffChiralHeatTrace]
  exact cutoffChiralHeatTrace_positive_add_pt_eq_zero cutoff time twist

/-- The operator-derived infinite chiral traces cancel between PT folds. -/
theorem circleOperatorChiralHeatTrace_positive_add_pt_eq_zero
    (time : HeatTime) (twist : CircleTwist) :
    circleOperatorChiralHeatTrace time .positive twist +
      circleOperatorChiralHeatTrace time .pt twist = 0 := by
  rw [circleOperatorChiralHeatTrace_eq_regulatedChiralTrace,
    circleOperatorChiralHeatTrace_eq_regulatedChiralTrace]
  exact pairedRegulatedChiralTrace_eq_zero time twist

end

end P0EFTJanusCircleDiracHeatFunctionalBridge
end JanusFormal
