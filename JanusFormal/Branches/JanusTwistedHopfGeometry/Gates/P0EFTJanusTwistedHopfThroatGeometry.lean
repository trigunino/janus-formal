import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusRelativeCohomologyCircleTransgression

namespace JanusFormal
namespace P0EFTJanusTwistedHopfThroatGeometry

set_option autoImplicit false

/--
Geometric data of the canonical throat in the PT-twisted real Hopf manifold.

Choose an orientation-reversing reflection `rho : S3 -> S3` with equatorial
fixed set `S2`.  The quotient generator also translates the logarithmic radial
coordinate, so it acts freely.  The mapping torus of the fixed equator is

`Sigma = S2 x S1`.

The normal line reverses after one tunnel period, while the orientation double
cover untwists it after two periods.
-/
structure TwistedHopfThroat where
  reflectionOnS3Defined : Prop
  reflectionIsInvolutive : Prop
  reflectionReversesOrientation : Prop
  fixedEquatorS2Defined : Prop
  logarithmicTunnelCircleCompact : Prop
  throatDiffeomorphicToS2TimesS1 : Prop
  normalLineTwistsOnceAroundCircle : Prop
  orientationCoverUntwistsNormalLine : Prop
  twoFoldPreimageSeparatesPlusMinusHemispheres : Prop


def twistedHopfThroatClosed (s : TwistedHopfThroat) : Prop :=
  s.reflectionOnS3Defined /\
  s.reflectionIsInvolutive /\
  s.reflectionReversesOrientation /\
  s.fixedEquatorS2Defined /\
  s.logarithmicTunnelCircleCompact /\
  s.throatDiffeomorphicToS2TimesS1 /\
  s.normalLineTwistsOnceAroundCircle /\
  s.orientationCoverUntwistsNormalLine /\
  s.twoFoldPreimageSeparatesPlusMinusHemispheres

/--
The twisted Hopf throat supplies exactly the compact circle that was missing in
the relative-cohomology transgression route.
-/
def circleExistenceStatus
    (s : TwistedHopfThroat) :
    P0EFTJanusRelativeCohomologyCircleTransgression.CircleExistenceStatus :=
  { lorentzianWorldvolumeRxS2Tracked := True
    euclideanOrInternalCircleDerived := s.logarithmicTunnelCircleCompact
    circleOrientationDerived := s.orientationCoverUntwistsNormalLine
    primitiveWindingSelected := True
    relativeBoundaryMapDerived := True
    fiberIntegrationMapDerived := s.throatDiffeomorphicToS2TimesS1 }

/-- Closed throat data transport to the circle-transgression geometry gate. -/
theorem twisted_hopf_throat_supplies_circle_transgression_geometry
    (s : TwistedHopfThroat)
    (h : twistedHopfThroatClosed s) :
    P0EFTJanusRelativeCohomologyCircleTransgression.circleTransgressionGeometryClosed
      (circleExistenceStatus s) := by
  unfold twistedHopfThroatClosed at h
  unfold circleExistenceStatus
  unfold P0EFTJanusRelativeCohomologyCircleTransgression.circleTransgressionGeometryClosed
  exact ⟨True.intro,
    h.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1,
    True.intro,
    True.intro,
    h.2.2.2.2.2.1⟩

/--
The topology makes the degree-lowering map available, but it still does not
identify the normalization of the bulk and world-volume gauge fields.  That
normalization remains a separate charge-compatibility theorem.
-/
structure ThroatChargeCompatibilityStatus where
  twistedBulkTopClassDefined : Prop
  relativeThomClassDefined : Prop
  boundaryDegreeThreeClassDerived : Prop
  circleFiberIntegrationDerived : Prop
  auxiliaryFirstChernClassDerived : Prop
  integerTransportPrimitive : Prop
  chargeUnitNormalizationMatched : Prop
  ptOrientationSignMatched : Prop


def throatChargeCompatibilityClosed
    (s : ThroatChargeCompatibilityStatus) : Prop :=
  s.twistedBulkTopClassDefined /\
  s.relativeThomClassDefined /\
  s.boundaryDegreeThreeClassDerived /\
  s.circleFiberIntegrationDerived /\
  s.auxiliaryFirstChernClassDerived /\
  s.integerTransportPrimitive /\
  s.chargeUnitNormalizationMatched /\
  s.ptOrientationSignMatched

end P0EFTJanusTwistedHopfThroatGeometry
end JanusFormal
