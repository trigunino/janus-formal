/-
Program D2: twisted Dirac spectral geometry on the canonical Janus throat.

The branch studies the SpinC Dirac operator on a primitive-monopole `S2`, its
product with the compact mapping-torus circle, the zero-mode eta invariant and
the induced LL charge normalization.

It deliberately separates:

1. exact finite algebra now proved in Lean;
2. explicit spectral formulas taken as operator-theorem targets;
3. physical vacuum and absolute-scale claims that remain open.
-/

import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusMonopoleDiracSpectrum
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusCircleHolonomyEta
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusProductDiracPairing
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiracSpectralGeometryLock
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusSpectralRatioCorrection
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusIndexParityAnomaly
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiracScaleOrbitNoGo

namespace JanusFormal
namespace JanusFundamentalGeometryDiracSpectral

set_option autoImplicit false

structure ProgramStatus where
  primitiveMonopoleIndexDerived : Prop
  twistedSphereDiracSpectrumDerived : Prop
  productDiracPairingDerived : Prop
  zeroModeEtaFormulaDerived : Prop
  halfHolonomyVacuumDerived : Prop
  oneEighthLLChargeLockDerived : Prop
  alphaEqualsSphereRadiusDerived : Prop
  circleToSphereRatioDerived : Prop
  parityAnomalyPairingDerived : Prop
  absoluteScaleOrbitIdentified : Prop
  renormalizedDeterminantDerived : Prop
  absoluteScaleBreakerDerived : Prop
  absoluteAlphaDerivedNoFit : Prop


def firstDiracSpectralMilestoneClosed (s : ProgramStatus) : Prop :=
  s.primitiveMonopoleIndexDerived /\
  s.twistedSphereDiracSpectrumDerived /\
  s.productDiracPairingDerived /\
  s.zeroModeEtaFormulaDerived /\
  s.halfHolonomyVacuumDerived /\
  s.oneEighthLLChargeLockDerived /\
  s.alphaEqualsSphereRadiusDerived /\
  s.circleToSphereRatioDerived /\
  s.parityAnomalyPairingDerived /\
  s.absoluteScaleOrbitIdentified


def fullDiracSpectralClosure (s : ProgramStatus) : Prop :=
  firstDiracSpectralMilestoneClosed s /\
  s.renormalizedDeterminantDerived /\
  s.absoluteScaleBreakerDerived /\
  s.absoluteAlphaDerivedNoFit

/-- The milestone fixes geometry ratios and charge relations, not an absolute length. -/
theorem milestone_without_scale_breaker_does_not_close_alpha
    (s : ProgramStatus)
    (hMilestone : firstDiracSpectralMilestoneClosed s)
    (hMissing : Not s.absoluteScaleBreakerDerived) :
    Not (fullDiracSpectralClosure s) := by
  intro h
  exact hMissing h.2.2.1

end JanusFundamentalGeometryDiracSpectral
end JanusFormal
