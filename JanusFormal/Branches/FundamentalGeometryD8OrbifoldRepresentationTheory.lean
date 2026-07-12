/-
Program D8: mapping-torus/orbifold terminology, one-sided throat topology and
representation-theoretic origin of the internal order-four sector.

D8 audits what can genuinely be derived from the current smooth mapping-torus
candidate before any field content is inserted:

1. the cyclic action is free, so the quotient is a smooth mapping-torus
   candidate rather than a singular reflection orbifold;
2. the equatorial throat is a one-sided hypersurface with normal holonomy `-1`;
3. the complexified normal line has exactly two finite-order square roots,
   exchanged by PT, giving a geometrically motivated quarter-holonomy pair;
4. cyclic holonomy data does not determine a rank-five multiplicity;
5. the three-dimensional trace/traceless symmetric-tensor split supplies a
   natural off-shell rank ratio `1:5`;
6. standard heat-kernel theory requires an auxiliary Euclidean metric, not the
   degenerate Lorentzian induced metric of a null world-volume.
-/

import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusSmoothMappingTorusOrbifoldAudit
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusOneSidedThroatNormalMonodromy
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusNormalOrientationZ4Lift
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusCyclicRepresentationMultiplicityNoGo
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusSymmetricTensorOneFiveCandidate
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusNormalRootTensorZ4Synthesis
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusNullWorldvolumeSpectralAudit

namespace JanusFormal
namespace JanusFundamentalGeometryD8OrbifoldRepresentationTheory

set_option autoImplicit false

structure ProgramStatus where
  nonzeroMappingPeriodDerived : Prop
  fullFreeIntegerActionConstructed : Prop
  smoothMappingTorusQuotientConstructed : Prop
  absenceOfLocalOrbifoldIsotropyProved : Prop
  equatorialThroatEmbedded : Prop
  oneSidedNormalLineConstructed : Prop
  normalHolonomyMinusOneProved : Prop
  complementConnectedProved : Prop
  orientationCoverNormalTrivialized : Prop
  complexNormalSquareRootConstructed : Prop
  exactlyTwoQuarterRootsClassified : Prop
  ptExchangeOfRootsProved : Prop
  actualFundamentalGroupProvedInfiniteCyclic : Prop
  flatBundleRepresentationClassificationApplied : Prop
  cyclicMultiplicityNoGoProved : Prop
  traceTracelessRankOneFiveDerived : Prop
  doubledTensorQuarterActionConstructed : Prop
  normalRootTensorCouplingDerived : Prop
  gaugeGhostSuperdeterminantComputed : Prop
  auxiliaryEuclideanMetricDerived : Prop
  nullToEuclideanContinuationDerived : Prop
  physicalOrbifoldInterpretationDerived : Prop
  stableModulusDerived : Prop
  absoluteScaleDerivedNoFit : Prop

/-- Topological/representation-theoretic D8 core. -/
def representationCoreClosed (s : ProgramStatus) : Prop :=
  s.nonzeroMappingPeriodDerived /\
  s.fullFreeIntegerActionConstructed /\
  s.smoothMappingTorusQuotientConstructed /\
  s.absenceOfLocalOrbifoldIsotropyProved /\
  s.equatorialThroatEmbedded /\
  s.oneSidedNormalLineConstructed /\
  s.normalHolonomyMinusOneProved /\
  s.complementConnectedProved /\
  s.orientationCoverNormalTrivialized /\
  s.complexNormalSquareRootConstructed /\
  s.exactlyTwoQuarterRootsClassified /\
  s.ptExchangeOfRootsProved /\
  s.actualFundamentalGroupProvedInfiniteCyclic /\
  s.flatBundleRepresentationClassificationApplied /\
  s.cyclicMultiplicityNoGoProved /\
  s.traceTracelessRankOneFiveDerived /\
  s.doubledTensorQuarterActionConstructed /\
  s.normalRootTensorCouplingDerived

/-- Full D8 physical closure. -/
def fullD8Closure (s : ProgramStatus) : Prop :=
  representationCoreClosed s /\
  s.gaugeGhostSuperdeterminantComputed /\
  s.auxiliaryEuclideanMetricDerived /\
  s.nullToEuclideanContinuationDerived /\
  s.physicalOrbifoldInterpretationDerived /\
  s.stableModulusDerived /\
  s.absoluteScaleDerivedNoFit

/-- A cyclic holonomy theorem without a multiplicity bundle cannot derive the rank-five sector. -/
theorem missing_tensor_multiplicity_blocks_representation_core
    (s : ProgramStatus)
    (hMissing : Not s.traceTracelessRankOneFiveDerived) :
    Not (representationCoreClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- A null induced metric without a derived Euclidean auxiliary metric blocks D8/D7 physics. -/
theorem missing_auxiliary_euclidean_metric_blocks_full_d8
    (s : ProgramStatus)
    (hMissing : Not s.auxiliaryEuclideanMetricDerived) :
    Not (fullD8Closure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

/-- A smooth free mapping torus does not by itself prove the physical singular-orbifold interpretation. -/
theorem missing_physical_orbifold_interpretation_blocks_full_d8
    (s : ProgramStatus)
    (hMissing : Not s.physicalOrbifoldInterpretationDerived) :
    Not (fullD8Closure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end JanusFundamentalGeometryD8OrbifoldRepresentationTheory
end JanusFormal
