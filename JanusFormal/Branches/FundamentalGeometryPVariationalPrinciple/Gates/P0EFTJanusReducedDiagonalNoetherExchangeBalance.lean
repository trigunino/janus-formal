import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedTwoMetricEulerNoether

namespace JanusFormal
namespace P0EFTJanusReducedDiagonalNoetherExchangeBalance

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedTwoMetricEulerNoether

variable {Configuration : Type*}
variable [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]

/--
Data needed to read a common reduced action as two bulk sectors plus a
possible boundary flux.  `boundaryEuler` is supplied reduced data; this
structure does not claim that it has already been obtained from a covariant
Stokes theorem.

The symmetry is translation along the common diagonal generator of the
reduced chart.  It is an exact finite-dimensional Noether model, not yet the
spacetime diffeomorphism symmetry or contracted Bianchi identity of Janus.
-/
structure TwoSectorActionBalance (Configuration : Type*)
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration] where
  chart : TwoMetricReducedChart Configuration
  action : Configuration → ℝ
  totalEuler : Configuration → Configuration →L[ℝ] ℝ
  plusBulkEuler : Configuration → Configuration →L[ℝ] ℝ
  minusBulkEuler : Configuration → Configuration →L[ℝ] ℝ
  boundaryEuler : Configuration → Configuration →L[ℝ] ℝ
  actualGradient : ∀ q, HasFDerivAt action (totalEuler q) q
  eulerDecomposition : ∀ q,
    totalEuler q = plusBulkEuler q + minusBulkEuler q + boundaryEuler q
  diagonalInvariant : DiagonalTranslationInvariant chart action

/-- Plus-sector diagonal balance. -/
def plusDiagonalBalance
    (data : TwoSectorActionBalance Configuration) (q : Configuration) : ℝ :=
  data.plusBulkEuler q (diagonalVariation data.chart)

/-- Minus-sector diagonal balance. -/
def minusDiagonalBalance
    (data : TwoSectorActionBalance Configuration) (q : Configuration) : ℝ :=
  data.minusBulkEuler q (diagonalVariation data.chart)

/-- Boundary contribution to the diagonal balance. -/
def boundaryDiagonalFlux
    (data : TwoSectorActionBalance Configuration) (q : Configuration) : ℝ :=
  data.boundaryEuler q (diagonalVariation data.chart)

/-- Total reduced diagonal balance. -/
def combinedDiagonalBalance
    (data : TwoSectorActionBalance Configuration) (q : Configuration) : ℝ :=
  plusDiagonalBalance data q + minusDiagonalBalance data q +
    boundaryDiagonalFlux data q

/-- The exchange residual entering the plus sector.  Choosing the plus
balance as the exchange convention fixes its sign; Noether alone does not
force this quantity to vanish. -/
def exchangeResidual
    (data : TwoSectorActionBalance Configuration) (q : Configuration) : ℝ :=
  plusDiagonalBalance data q

/--
Strongest identity supplied by the actual common-action symmetry: only the
sum of the two bulk balances and the boundary flux vanishes.
-/
theorem diagonal_noether_combined_balance
    (data : TwoSectorActionBalance Configuration) (q : Configuration) :
    combinedDiagonalBalance data q = 0 := by
  have hNoether := diagonal_noether_of_translation_invariance
    data.chart data.action data.totalEuler data.actualGradient
    data.diagonalInvariant q
  rw [data.eulerDecomposition q] at hNoether
  simpa [combinedDiagonalBalance, plusDiagonalBalance,
    minusDiagonalBalance, boundaryDiagonalFlux] using hNoether

theorem diagonal_noether_combined_balance_expanded
    (data : TwoSectorActionBalance Configuration) (q : Configuration) :
    plusDiagonalBalance data q + minusDiagonalBalance data q +
      boundaryDiagonalFlux data q = 0 := by
  simpa [combinedDiagonalBalance] using
    diagonal_noether_combined_balance data q

/-- The bulk pair balances the outgoing boundary contribution. -/
theorem combined_bulk_balance_eq_negative_boundary_flux
    (data : TwoSectorActionBalance Configuration) (q : Configuration) :
    plusDiagonalBalance data q + minusDiagonalBalance data q =
      -boundaryDiagonalFlux data q := by
  linarith [diagonal_noether_combined_balance_expanded data q]

/-- Once the plus balance is named as exchange, the minus balance is fixed by
the combined identity and the boundary flux. -/
theorem minus_balance_eq_negative_exchange_minus_boundary
    (data : TwoSectorActionBalance Configuration) (q : Configuration) :
    minusDiagonalBalance data q =
      -exchangeResidual data q - boundaryDiagonalFlux data q := by
  unfold exchangeResidual
  linarith [diagonal_noether_combined_balance_expanded data q]

/-- Separate bulk conservation requires both zero exchange and zero boundary
flux.  Conversely those two extra conditions are sufficient.  Neither is a
consequence of diagonal Noether symmetry alone. -/
theorem separate_conservation_iff_zero_exchange_and_boundary
    (data : TwoSectorActionBalance Configuration) (q : Configuration) :
    (plusDiagonalBalance data q = 0 ∧ minusDiagonalBalance data q = 0) ↔
      (exchangeResidual data q = 0 ∧ boundaryDiagonalFlux data q = 0) := by
  constructor
  · rintro ⟨hPlus, hMinus⟩
    constructor
    · exact hPlus
    · linarith [diagonal_noether_combined_balance_expanded data q]
  · rintro ⟨hExchange, hBoundary⟩
    have hPlus : plusDiagonalBalance data q = 0 := hExchange
    constructor
    · exact hPlus
    · linarith [diagonal_noether_combined_balance_expanded data q]

/-- With no boundary flux, the two sector balances are equal and opposite. -/
theorem zero_boundary_balances_are_equal_and_opposite
    (data : TwoSectorActionBalance Configuration) (q : Configuration)
    (hBoundary : boundaryDiagonalFlux data q = 0) :
    minusDiagonalBalance data q = -plusDiagonalBalance data q := by
  linarith [diagonal_noether_combined_balance_expanded data q]

/-- With no boundary flux, separate conservation is equivalent to zero
exchange. -/
theorem zero_boundary_separate_conservation_iff_zero_exchange
    (data : TwoSectorActionBalance Configuration) (q : Configuration)
    (hBoundary : boundaryDiagonalFlux data q = 0) :
    (plusDiagonalBalance data q = 0 ∧ minusDiagonalBalance data q = 0) ↔
      exchangeResidual data q = 0 := by
  rw [separate_conservation_iff_zero_exchange_and_boundary]
  simp [hBoundary]

/-- Two real amplitudes packaged in `ℂ`; this is only a convenient canonical
real normed space, not a physical complexification. -/
def exactTwoSectorChart : TwoMetricReducedChart ℂ where
  plusCoordinate := Complex.reCLM
  minusCoordinate := Complex.imCLM
  plusVariation := 1
  minusVariation := Complex.I
  plusCoordinate_plus := by simp
  plusCoordinate_minus := by simp
  minusCoordinate_plus := by simp
  minusCoordinate_minus := by simp

/-- Plus contribution to the explicit relative-mode Euler derivative. -/
def exactPlusBulkEuler (q : ℂ) : ℂ →L[ℝ] ℝ :=
  (plusEuler exactTwoSectorChart 1 q) • exactTwoSectorChart.plusCoordinate

/-- Minus contribution to the explicit relative-mode Euler derivative. -/
def exactMinusBulkEuler (q : ℂ) : ℂ →L[ℝ] ℝ :=
  (minusEuler exactTwoSectorChart 1 q) • exactTwoSectorChart.minusCoordinate

/-- The explicit common relative-mode action, with no boundary flux, as
two-sector Noether data. -/
def exactExchangeData : TwoSectorActionBalance ℂ where
  chart := exactTwoSectorChart
  action := reducedInteractionAction exactTwoSectorChart 1
  totalEuler := reducedEuler exactTwoSectorChart 1
  plusBulkEuler := exactPlusBulkEuler
  minusBulkEuler := exactMinusBulkEuler
  boundaryEuler := fun _ => 0
  actualGradient := reducedInteractionAction_hasFDerivAt exactTwoSectorChart 1
  eulerDecomposition := by
    intro q
    apply ContinuousLinearMap.ext
    intro variation
    simp [reducedEuler, exactPlusBulkEuler, exactMinusBulkEuler,
      plusEuler, minusEuler, relativeMode]
    ring
  diagonalInvariant :=
    reducedInteractionAction_diagonal_invariant exactTwoSectorChart 1

/-- At the exact configuration `(1,0)`, the plus sector carries nonzero
exchange while the minus sector carries the opposite exchange. -/
theorem exact_counterexample_sector_balances :
    plusDiagonalBalance exactExchangeData 1 = 1 ∧
      minusDiagonalBalance exactExchangeData 1 = -1 ∧
      boundaryDiagonalFlux exactExchangeData 1 = 0 := by
  norm_num [plusDiagonalBalance, minusDiagonalBalance, boundaryDiagonalFlux,
    exactExchangeData, exactPlusBulkEuler, exactMinusBulkEuler,
    diagonalVariation, exactTwoSectorChart, plusEuler, minusEuler,
    relativeMode]

/-- Exact counterexample to the invalid inference from common diagonal
Noether balance to separate sector conservation.  The action has a genuine
Fréchet derivative through `exactExchangeData.actualGradient`; its combined
balance vanishes, while both bulk sector balances are nonzero. -/
theorem combined_balance_does_not_imply_separate_conservation :
    ∃ (data : TwoSectorActionBalance ℂ) (q : ℂ),
      combinedDiagonalBalance data q = 0 ∧
        ¬ (plusDiagonalBalance data q = 0 ∧
          minusDiagonalBalance data q = 0) := by
  refine ⟨exactExchangeData, 1, diagonal_noether_combined_balance _ _, ?_⟩
  obtain ⟨hPlus, hMinus, _⟩ := exact_counterexample_sector_balances
  norm_num [hPlus, hMinus]

end

end P0EFTJanusReducedDiagonalNoetherExchangeBalance
end JanusFormal
