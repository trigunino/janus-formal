import Mathlib

namespace JanusFormal
namespace P0EFTJanusAbstractDiracPTFredholmFoundation

set_option autoImplicit false

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An abstract Dirac operator together with its linear PT symmetry. -/
structure DiracPTData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  dirac : V →ₗ[ℝ] V
  pt : V →ₗ[ℝ] V
  pt_involutive : pt.comp pt = LinearMap.id
  pt_anticommutes : pt.comp dirac = -(dirac.comp pt)

def IsEigenvector (D : V →ₗ[ℝ] V) (v : V) (eigenvalue : ℝ) : Prop :=
  v ≠ 0 ∧ D v = eigenvalue • v

/-- PT anticommutation pairs every nonzero eigenmode at `λ` with one at `-λ`. -/
theorem pt_pairs_dirac_eigenvalues
    (data : DiracPTData V) {v : V} {eigenvalue : ℝ}
    (hEigen : IsEigenvector data.dirac v eigenvalue) :
    IsEigenvector data.dirac (data.pt v) (-eigenvalue) := by
  constructor
  · intro hZero
    have hApply := congrArg (fun f : V →ₗ[ℝ] V => f v) data.pt_involutive
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hApply
    rw [hZero, map_zero] at hApply
    exact hEigen.1 hApply.symm
  · have hAnti := congrArg (fun f : V →ₗ[ℝ] V => f v) data.pt_anticommutes
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hAnti
    rw [hEigen.2, map_smul] at hAnti
    simpa [neg_smul] using (neg_eq_iff_eq_neg.mp hAnti.symm)

/-- Principal-symbol data, independent of all lower-order terms selected by an action. -/
structure AbstractDiracSymbol (T S : Type*)
    [AddCommGroup T] [Module ℝ T] [AddCommGroup S] [Module ℝ S] where
  symbol : T →ₗ[ℝ] (S →ₗ[ℝ] S)
  symbolSquareScalar : Prop
  nonzeroCovectorInvertible : Prop

/-- Formal self-adjointness is recorded against a chosen bilinear pairing. -/
def FormallySelfAdjoint
    (pairing : V → V → ℝ) (D : V →ₗ[ℝ] V) : Prop :=
  ∀ u v, pairing (D u) v = pairing u (D v)

/-- Analytic hypotheses needed to promote the symbolic operator to a Fredholm one. -/
structure FredholmRealizationStatus where
  compactBaseEstablished : Prop
  globalBundleConstructed : Prop
  ellipticPrincipalSymbolProved : Prop
  denseDomainSpecified : Prop
  boundaryConditionElliptic : Prop
  formalSelfAdjointnessProved : Prop
  closedSelfAdjointExtensionConstructed : Prop
  compactResolventProved : Prop
  finiteKernelAndCokernelProved : Prop

def fredholmRealizationClosed (s : FredholmRealizationStatus) : Prop :=
  s.compactBaseEstablished ∧ s.globalBundleConstructed ∧
  s.ellipticPrincipalSymbolProved ∧ s.denseDomainSpecified ∧
  s.boundaryConditionElliptic ∧ s.formalSelfAdjointnessProved ∧
  s.closedSelfAdjointExtensionConstructed ∧ s.compactResolventProved ∧
  s.finiteKernelAndCokernelProved

/-- One auditable certificate promoting the symbolic Dirac block to discrete Fredholm spectral data. -/
structure SelfAdjointCompactResolventCertificate where
  compactBaseEstablished : Prop
  globalBundleConstructed : Prop
  ellipticPrincipalSymbolProved : Prop
  denseSobolevDomainSpecified : Prop
  ellipticBoundaryConditionProved : Prop
  greenFormulaProved : Prop
  closedSelfAdjointRealizationConstructed : Prop
  compactSobolevEmbeddingProved : Prop
  compactResolventDerived : Prop
  fredholmKernelCokernelFinite : Prop

def analyticPromotionClosed
    (s : SelfAdjointCompactResolventCertificate) : Prop :=
  s.compactBaseEstablished ∧ s.globalBundleConstructed ∧
  s.ellipticPrincipalSymbolProved ∧ s.denseSobolevDomainSpecified ∧
  s.ellipticBoundaryConditionProved ∧ s.greenFormulaProved ∧
  s.closedSelfAdjointRealizationConstructed ∧
  s.compactSobolevEmbeddingProved ∧ s.compactResolventDerived ∧
  s.fredholmKernelCokernelFinite

/-- The consolidated analytic certificate supplies every field of the D7 Fredholm ledger. -/
def toFredholmRealizationStatus
    (s : SelfAdjointCompactResolventCertificate) : FredholmRealizationStatus :=
  { compactBaseEstablished := s.compactBaseEstablished
    globalBundleConstructed := s.globalBundleConstructed
    ellipticPrincipalSymbolProved := s.ellipticPrincipalSymbolProved
    denseDomainSpecified := s.denseSobolevDomainSpecified
    boundaryConditionElliptic := s.ellipticBoundaryConditionProved
    formalSelfAdjointnessProved := s.greenFormulaProved
    closedSelfAdjointExtensionConstructed :=
      s.closedSelfAdjointRealizationConstructed
    compactResolventProved := s.compactResolventDerived
    finiteKernelAndCokernelProved := s.fredholmKernelCokernelFinite }

theorem analytic_promotion_implies_fredholm_realization
    (s : SelfAdjointCompactResolventCertificate)
    (h : analyticPromotionClosed s) :
    fredholmRealizationClosed (toFredholmRealizationStatus s) := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem missing_domain_blocks_fredholm_realization
    (s : FredholmRealizationStatus) (h : Not s.denseDomainSpecified) :
    Not (fredholmRealizationClosed s) := by
  intro hs
  exact h hs.2.2.2.1

theorem missing_compact_resolvent_blocks_fredholm_realization
    (s : FredholmRealizationStatus) (h : Not s.compactResolventProved) :
    Not (fredholmRealizationClosed s) := by
  intro hs
  exact h hs.2.2.2.2.2.2.2.1

end P0EFTJanusAbstractDiracPTFredholmFoundation
end JanusFormal
