/-
PT-twisted real Hopf geometry for the resolved Janus topology.

The proposed smooth four-manifold is

`J(lambda,rho) = (R^4 \ {0}) / <x ~ lambda * rho(x)>`,

where `0 < lambda < 1` and `rho` is an orientation-reversing orthogonal
reflection.  In logarithmic polar coordinates it is the mapping torus of
`rho : S3 -> S3`.  Its orientation double cover is `S3 x S1`; the equatorial
fixed set of `rho` generates a canonical throat `Sigma = S2 x S1`.
-/

import JanusFormal.Branches.JanusTwistedHopfGeometry.Gates.P0EFTJanusTwistedHopfMonodromy
import JanusFormal.Branches.JanusTwistedHopfGeometry.Gates.P0EFTJanusTwistedHopfTopologyInvariants
import JanusFormal.Branches.JanusTwistedHopfGeometry.Gates.P0EFTJanusTwistedHopfScaleLaw
import JanusFormal.Branches.JanusTwistedHopfGeometry.Gates.P0EFTJanusTwistedHopfThroatGeometry

namespace JanusFormal
namespace JanusTwistedHopfGeometry

set_option autoImplicit false

structure ProgramStatus where
  realHopfQuotientConstructed : Prop
  reflectionMappingTorusIdentified : Prop
  orientationDoubleCoverS3TimesS1Proved : Prop
  twoFoldVolumeRatioProved : Prop
  canonicalS2TimesS1ThroatProved : Prop
  compactTransgressionCircleProved : Prop
  normalOrientationTwistProved : Prop
  twistedTopClassComputed : Prop
  monodromyParityComputed : Prop
  pinLiftedZ4Derived : Prop
  tunnelPeriodMatchedToRGExponent : Prop
  chargeNormalizationCompatibilityDerived : Prop
  lorentzianMetricAndJunctionDerived : Prop


def geometricCoreClosed (s : ProgramStatus) : Prop :=
  s.realHopfQuotientConstructed /\
  s.reflectionMappingTorusIdentified /\
  s.orientationDoubleCoverS3TimesS1Proved /\
  s.twoFoldVolumeRatioProved /\
  s.canonicalS2TimesS1ThroatProved /\
  s.compactTransgressionCircleProved /\
  s.normalOrientationTwistProved /\
  s.twistedTopClassComputed /\
  s.monodromyParityComputed


def fullGeometryPhysicsBridgeClosed (s : ProgramStatus) : Prop :=
  geometricCoreClosed s /\
  s.pinLiftedZ4Derived /\
  s.tunnelPeriodMatchedToRGExponent /\
  s.chargeNormalizationCompatibilityDerived /\
  s.lorentzianMetricAndJunctionDerived


theorem missing_charge_compatibility_blocks_full_bridge
    (s : ProgramStatus)
    (hMissing : Not s.chargeNormalizationCompatibilityDerived) :
    Not (fullGeometryPhysicsBridgeClosed s) := by
  intro h
  exact hMissing h.2.2.2.1

end JanusTwistedHopfGeometry
end JanusFormal
