/-
Program D2: twisted Dirac spectral geometry on the canonical Janus throat.

The branch studies the SpinC Dirac operator on a monopole-twisted `S2`, its
product with the compact mapping-torus circle, the zero-mode eta invariant, the
full holonomy-dependent determinant kernel and the induced LL charge
normalization.

It deliberately separates:

1. exact finite algebra now proved in Lean;
2. explicit spectral formulas taken as operator-theorem targets;
3. physical vacuum and absolute-scale claims that remain open.
-/

import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusMonopoleDiracSpectrum
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusCircleHolonomyEta
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusProductDiracPairing
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusFullHolonomyDeterminant
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiracSpectralGeometryLock
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiracBimetricPrimitiveSelection
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusSpectralRatioCorrection
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusIndexParityAnomaly
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiracScaleOrbitNoGo
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusOddDimensionalDeterminantNoGo

namespace JanusFormal
namespace JanusFundamentalGeometryDiracSpectral

set_option autoImplicit false

structure ProgramStatus where
  twistedSphereDiracSpectrumDerived : Prop
  productDiracPairingDerived : Prop
  zeroModeEtaFormulaDerived : Prop
  fullModeDeterminantKernelDerived : Prop
  halfHolonomyVacuumDerived : Prop
  oneEighthLLChargeLockDerived : Prop
  primitiveMonopoleSelectedByBimetricMatch : Prop
  alphaEqualsSphereRadiusDerived : Prop
  circleToSphereRatioDerived : Prop
  oldScalarRatioReinterpreted : Prop
  parityAnomalyPairingDerived : Prop
  absoluteScaleOrbitIdentified : Prop
  oddDimensionalMasslessScaleNoGoDerived : Prop
  renormalizedInfiniteDeterminantDerived : Prop
  absoluteScaleBreakerDerived : Prop
  absoluteAlphaDerivedNoFit : Prop


def firstDiracSpectralMilestoneClosed (s : ProgramStatus) : Prop :=
  s.twistedSphereDiracSpectrumDerived /\
  s.productDiracPairingDerived /\
  s.zeroModeEtaFormulaDerived /\
  s.fullModeDeterminantKernelDerived /\
  s.halfHolonomyVacuumDerived /\
  s.oneEighthLLChargeLockDerived /\
  s.primitiveMonopoleSelectedByBimetricMatch /\
  s.alphaEqualsSphereRadiusDerived /\
  s.circleToSphereRatioDerived /\
  s.oldScalarRatioReinterpreted /\
  s.parityAnomalyPairingDerived /\
  s.absoluteScaleOrbitIdentified /\
  s.oddDimensionalMasslessScaleNoGoDerived


def fullDiracSpectralClosure (s : ProgramStatus) : Prop :=
  firstDiracSpectralMilestoneClosed s /\
  s.renormalizedInfiniteDeterminantDerived /\
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
