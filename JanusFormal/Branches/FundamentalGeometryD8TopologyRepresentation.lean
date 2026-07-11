/-
Program D8: audit the topology/representation frontier before promoting the
Janus mapping-torus candidate to an orbifold or using its monodromy to select
field multiplicities.

The branch separates:

1. the free smooth mapping-torus quotient;
2. the one-sided equatorial throat and its orientation cover;
3. the infinite-cyclic loop group and its order-four holonomy images;
4. the Pin reflection-square convention;
5. genuinely additional internal symmetry or flavor data.
-/

import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusFreeActionAudit
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusCyclicHolonomyRepresentationAudit
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusPinReflectionSquareConventionAudit

namespace JanusFormal
namespace JanusFundamentalGeometryD8TopologyRepresentation

set_option autoImplicit false

structure ProgramStatus where
  nonzeroTranslationDerived : Prop
  integerActionFreeProved : Prop
  properDiscontinuityProved : Prop
  smoothMappingTorusConstructed : Prop
  noOrbifoldIsotropyProved : Prop
  equatorialThroatConstructed : Prop
  normalMonodromyMinusOneProved : Prop
  throatOneSidedProved : Prop
  orientationDoubleCoverConstructed : Prop
  twoCoverSidesExchangedProved : Prop
  coverToQuotientRatioTwoToOneProved : Prop
  worldAToWorldBRatioOneToOneProved : Prop
  sphereFiberBundleOverCircleConstructed : Prop
  fundamentalGroupIdentifiedWithIntegers : Prop
  orientationCharacterIdentifiedWithParity : Prop
  twoZ4OrientationLiftsClassified : Prop
  orderFourHolonomyDistinguishedFromFundamentalGroup : Prop
  cyclicHolonomyRankFreedomProved : Prop
  irreducibleCyclicRepresentationDimensionAudited : Prop
  rankFiveBundleDerivedFromAdditionalData : Prop
  pinReflectionSquareConventionFixed : Prop
  euclideanLorentzianPinDictionaryDerived : Prop
  internalSymmetryGeometricallyDerived : Prop

/-- Smooth topology and one-sided-throat milestone. -/
def smoothMappingTorusCoreClosed (s : ProgramStatus) : Prop :=
  s.nonzeroTranslationDerived /\
  s.integerActionFreeProved /\
  s.properDiscontinuityProved /\
  s.smoothMappingTorusConstructed /\
  s.noOrbifoldIsotropyProved /\
  s.equatorialThroatConstructed /\
  s.normalMonodromyMinusOneProved /\
  s.throatOneSidedProved /\
  s.orientationDoubleCoverConstructed /\
  s.twoCoverSidesExchangedProved /\
  s.coverToQuotientRatioTwoToOneProved /\
  s.worldAToWorldBRatioOneToOneProved

/-- Cyclic monodromy and representation milestone. -/
def cyclicRepresentationAuditClosed (s : ProgramStatus) : Prop :=
  s.sphereFiberBundleOverCircleConstructed /\
  s.fundamentalGroupIdentifiedWithIntegers /\
  s.orientationCharacterIdentifiedWithParity /\
  s.twoZ4OrientationLiftsClassified /\
  s.orderFourHolonomyDistinguishedFromFundamentalGroup /\
  s.cyclicHolonomyRankFreedomProved /\
  s.irreducibleCyclicRepresentationDimensionAudited /\
  s.rankFiveBundleDerivedFromAdditionalData

/-- Full D8 closure. -/
def fullD8Closure (s : ProgramStatus) : Prop :=
  smoothMappingTorusCoreClosed s /\
  cyclicRepresentationAuditClosed s /\
  s.pinReflectionSquareConventionFixed /\
  s.euclideanLorentzianPinDictionaryDerived /\
  s.internalSymmetryGeometricallyDerived

/-- A smooth free quotient does not yet provide an orbifold isotropy group. -/
theorem missing_internal_symmetry_blocks_full_d8
    (s : ProgramStatus)
    (hMissing : Not s.internalSymmetryGeometricallyDerived) :
    Not (fullD8Closure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, _, hInternal⟩
  exact hMissing hInternal

/-- Cyclic holonomy alone cannot close a rank-five field-content theorem. -/
theorem missing_rank_five_derivation_blocks_representation_closure
    (s : ProgramStatus)
    (hMissing : Not s.rankFiveBundleDerivedFromAdditionalData) :
    Not (cyclicRepresentationAuditClosed s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, _, _, _, _, hRankFive⟩
  exact hMissing hRankFive

/-- A convention-dependent Pin label cannot close the order-four physical claim. -/
theorem missing_pin_dictionary_blocks_full_d8
    (s : ProgramStatus)
    (hMissing : Not s.euclideanLorentzianPinDictionaryDerived) :
    Not (fullD8Closure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, hDictionary, _⟩
  exact hMissing hDictionary

end JanusFundamentalGeometryD8TopologyRepresentation
end JanusFormal
