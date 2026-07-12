import Mathlib

namespace JanusFormal
namespace P0EFTJanusProductDiracPairing

set_option autoImplicit false

/-- Squared product eigenvalue from a sphere eigenvalue and circle momentum. -/
def productEigenvalueSquared (sphereEigenvalue circleMomentum : ℝ) : ℝ :=
  sphereEigenvalue ^ 2 + circleMomentum ^ 2

/-- Positive product branch. -/
noncomputable def positiveProductBranch
    (sphereEigenvalue circleMomentum : ℝ) : ℝ :=
  Real.sqrt (productEigenvalueSquared sphereEigenvalue circleMomentum)

/-- Negative product branch. -/
noncomputable def negativeProductBranch
    (sphereEigenvalue circleMomentum : ℝ) : ℝ :=
  -positiveProductBranch sphereEigenvalue circleMomentum

/-- Every nonzero two-sphere mode produces an exactly symmetric product pair. -/
theorem product_branches_cancel
    (sphereEigenvalue circleMomentum : ℝ) :
    positiveProductBranch sphereEigenvalue circleMomentum +
      negativeProductBranch sphereEigenvalue circleMomentum = 0 := by
  unfold negativeProductBranch
  ring

/-- Both product branches have the same squared eigenvalue. -/
theorem positive_branch_square
    (sphereEigenvalue circleMomentum : ℝ) :
    positiveProductBranch sphereEigenvalue circleMomentum ^ 2 =
      productEigenvalueSquared sphereEigenvalue circleMomentum := by
  unfold positiveProductBranch
  have hNonnegative :
      0 ≤ productEigenvalueSquared sphereEigenvalue circleMomentum := by
    unfold productEigenvalueSquared
    positivity
  exact Real.sq_sqrt hNonnegative

/-- The negative branch has the same square. -/
theorem negative_branch_square
    (sphereEigenvalue circleMomentum : ℝ) :
    negativeProductBranch sphereEigenvalue circleMomentum ^ 2 =
      productEigenvalueSquared sphereEigenvalue circleMomentum := by
  unfold negativeProductBranch
  rw [neg_sq, positive_branch_square]

/--
Abstract eta decomposition: paired nonzero modes cancel, so only the monopole
zero-mode tower can carry spectral asymmetry.
-/
structure EtaDecomposition where
  pairedNonzeroContribution : ℝ
  zeroModeTowerContribution : ℝ
  totalEta : ℝ
  pairedCancellation : pairedNonzeroContribution = 0
  decompositionLaw :
    totalEta = pairedNonzeroContribution + zeroModeTowerContribution

/-- Eta reduces to the zero-mode tower under exact product pairing. -/
theorem eta_reduces_to_zero_mode_tower
    (s : EtaDecomposition) :
    s.totalEta = s.zeroModeTowerContribution := by
  rw [s.decompositionLaw, s.pairedCancellation, zero_add]

/--
A complete operator theorem must prove the product formula, domains,
self-adjointness and multiplicities for the twisted Dirac operator on
`S2 x S1`, rather than only use the algebraic branch pairing.
-/
structure ProductDiracRealizationStatus where
  sphereDiracConstructed : Prop
  circleDiracConstructed : Prop
  gradedProductBundleConstructed : Prop
  productDiracConstructed : Prop
  productSquareFormulaProved : Prop
  domainsAndSelfAdjointnessProved : Prop
  nonzeroSpectrumPairingProved : Prop
  etaReductionToKernelProved : Prop


def productDiracRealizationClosed
    (s : ProductDiracRealizationStatus) : Prop :=
  s.sphereDiracConstructed /\
  s.circleDiracConstructed /\
  s.gradedProductBundleConstructed /\
  s.productDiracConstructed /\
  s.productSquareFormulaProved /\
  s.domainsAndSelfAdjointnessProved /\
  s.nonzeroSpectrumPairingProved /\
  s.etaReductionToKernelProved

end P0EFTJanusProductDiracPairing
end JanusFormal
