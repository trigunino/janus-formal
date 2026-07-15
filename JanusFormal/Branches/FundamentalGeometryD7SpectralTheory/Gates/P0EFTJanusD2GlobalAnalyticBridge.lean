import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusGlobalSeparatedDiracModel
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusAbstractDiracPTFredholmFoundation

namespace JanusFormal
namespace P0EFTJanusD2GlobalAnalyticBridge

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusAbstractDiracPTFredholmFoundation

/-- Inputs connecting the explicit D2 mode model to the abstract D7 analytic certificate. -/
structure D2ToD7AnalyticBridge where
  compactProductThroatEstablished : Prop
  globalSpinorBundleConstructed : Prop
  diracEllipticityProved : Prop
  d2Analytic : GlobalDiracAnalyticStatus
  d2AnalyticClosed : globalDiracAnalyticClosed d2Analytic
  ellipticBoundaryConditionProved : Prop
  greenFormulaProved : Prop
  compactSobolevEmbeddingProved : Prop
  cokernelIdentifiedWithKernel : Prop

def toD7AnalyticCertificate
    (s : D2ToD7AnalyticBridge) : SelfAdjointCompactResolventCertificate :=
  { compactBaseEstablished := s.compactProductThroatEstablished
    globalBundleConstructed := s.globalSpinorBundleConstructed
    ellipticPrincipalSymbolProved := s.diracEllipticityProved
    denseSobolevDomainSpecified := s.d2Analytic.diagonalOperatorDenselyDefined
    ellipticBoundaryConditionProved := s.ellipticBoundaryConditionProved
    greenFormulaProved := s.greenFormulaProved
    closedSelfAdjointRealizationConstructed := s.d2Analytic.selfAdjointnessProved
    compactSobolevEmbeddingProved := s.compactSobolevEmbeddingProved
    compactResolventDerived := s.d2Analytic.compactResolventProved
    fredholmKernelCokernelFinite :=
      s.d2Analytic.finiteMultiplicityProved ∧ s.cokernelIdentifiedWithKernel }

theorem bridge_closes_d7_certificate
    (s : D2ToD7AnalyticBridge)
    (hBase : s.compactProductThroatEstablished)
    (hBundle : s.globalSpinorBundleConstructed)
    (hElliptic : s.diracEllipticityProved)
    (hBoundary : s.ellipticBoundaryConditionProved)
    (hGreen : s.greenFormulaProved)
    (hEmbedding : s.compactSobolevEmbeddingProved)
    (hCokernel : s.cokernelIdentifiedWithKernel) :
    analyticPromotionClosed (toD7AnalyticCertificate s) := by
  rcases s.d2AnalyticClosed with ⟨_, hDense, _, hSelfAdjoint,
    hResolvent, _, hFinite⟩
  exact ⟨hBase, hBundle, hElliptic, hDense, hBoundary, hGreen,
    hSelfAdjoint, hEmbedding, hResolvent, hFinite, hCokernel⟩

end P0EFTJanusD2GlobalAnalyticBridge
end JanusFormal
