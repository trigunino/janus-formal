/-
Program D8: audit the topology/representation frontier before promoting the
Janus mapping-torus candidate to an orbifold or using its monodromy to select
field multiplicities.

The branch separates:

1. the free smooth mapping-torus quotient;
2. the one-sided equatorial throat and its orientation cover;
3. the infinite-cyclic loop group and its order-four holonomy images;
4. a genuinely singular mirror-orbifold alternative;
5. the Pin reflection-square convention;
6. genuinely additional internal symmetry or flavor data.
-/

import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusFreeActionAudit
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusQuotient
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusPTInvolution
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalLine
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusOrientationDoubleCover
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusThroatComplementSides
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusThroatComplementConnected
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothAtlasFrontier
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotient
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothPTInvolution
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusIsSmoothEmbedding
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusGlobalNormalEquivalence
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalRootPTConjugation
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusCyclicHolonomyRepresentationAudit
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMirrorOrbifoldAlternative
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusPinReflectionSquareConventionAudit
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalLineClutching
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalBundleOrientationCover
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalPinLiftBoundaryConditions
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusZ4CocycleMonodromyBoundarySynthesis

namespace JanusFormal
namespace JanusFundamentalGeometryD8TopologyRepresentation

set_option autoImplicit false

structure ProgramStatus where
  effectiveTopologicalMappingTorusQuotientConstructed : Prop
  mappingTorusCoveringAndChartedSpaceProved : Prop
  fixedThroatQuotientInclusionInjectiveProved : Prop
  mappingTorusTimeReversalContinuousProved : Prop
  mappingTorusTimeReversalInvolutiveProved : Prop
  fixedThroatQuotientInclusionPTEquivariantProved : Prop
  associatedNormalLineOrbitQuotientConstructed : Prop
  associatedNormalLineProjectionContinuousSurjectiveProved : Prop
  associatedNormalLineZeroSectionConstructed : Prop
  associatedNormalLineOneLoopFlipProved : Prop
  associatedNormalLineTwoLoopRestorationProved : Prop
  effectiveThroatOrientationDoubleCoveringMapProved : Prop
  throatOrientationDoubleCoverFiberTwoProved : Prop
  throatOrientationDeckInvolutionFreeProved : Prop
  throatNormalPullbackTopologicallyTrivializedProved : Prop
  equatorialSphereComplementTwoOpenSidesProved : Prop
  reflectionAndDeckExchangeCoverSidesProved : Prop
  effectiveThroatComplementOneSidedImageProved : Prop
  effectiveThroatComplementPTInvariantProved : Prop
  positiveAndNegativeSphereSidesPathConnectedProved : Prop
  positiveCoverSidePathConnectedProved : Prop
  effectiveThroatComplementPathConnectedProved : Prop
  effectiveThroatComplementConnectedProved : Prop
  algebraicSphereCoversAnalyticManifoldsProved : Prop
  throatCoverTopologicalEmbeddingAndC0Proved : Prop
  effectiveMappingTorusTopologicalManifoldProved : Prop
  effectiveThroatTopologicalManifoldProved : Prop
  quotientProjectionLocalHomeomorphAndC0Proved : Prop
  smoothDeckActionsAndAtlasTransitionsProved : Prop
  effectiveMappingTorusSmoothQuotientManifoldProved : Prop
  effectiveThroatSmoothQuotientManifoldProved : Prop
  quotientProjectionLocalDiffeomorphProved : Prop
  fixedThroatQuotientInclusionContMDiffProved : Prop
  mappingTorusTimeReversalContMDiffProved : Prop
  mappingTorusTimeReversalDiffeomorphConstructed : Prop
  effectiveMappingTorusCompactProved : Prop
  effectiveThroatCompactProved : Prop
  fixedThroatQuotientInclusionIsClosedEmbeddingProved : Prop
  fixedThroatQuotientDifferentialInjectiveProved : Prop
  fixedThroatNormalQuotientFinrankOneProved : Prop
  fixedThroatQuotientInclusionIsImmersionOfComplementProved : Prop
  fixedThroatQuotientInclusionIsSmoothEmbeddingProved : Prop
  fixedThroatNormalVectorBundleConstructed : Prop
  fixedThroatNormalVectorBundleContMDiffProved : Prop
  fixedThroatNormalFiberPointwiseDifferentialEquivProved : Prop
  fixedThroatNormalOneLoopMinusIdentityProved : Prop
  fixedThroatNormalGlobalAlgebraicEquivProved : Prop
  fixedThroatNormalZ4RootComplexLineConstructed : Prop
  fixedThroatNormalZ4RootSmoothRealUnderlierProved : Prop
  fixedThroatNormalZ4RootSquaresToNormalSignProved : Prop
  fixedThroatNormalZ4RootPTConjugationProved : Prop
  fixedThroatNormalPinMinusPrincipalBundleConstructed : Prop
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
  mirrorOrbifoldAlternativeConstructed : Prop
  mirrorIsotropyAndGlideTranslationSeparated : Prop
  mirrorAndGlideLoopGroupsDistinguished : Prop
  singularAndSmoothSpectralTheoriesCompared : Prop
  pinReflectionSquareConventionFixed : Prop
  euclideanLorentzianPinDictionaryDerived : Prop
  internalSymmetryGeometricallyDerived : Prop

/-- Effective topological quotient, covering charts and the injected fixed throat. -/
def effectiveTopologicalMappingTorusCoreClosed (s : ProgramStatus) : Prop :=
  s.effectiveTopologicalMappingTorusQuotientConstructed /\
  s.mappingTorusCoveringAndChartedSpaceProved /\
  s.fixedThroatQuotientInclusionInjectiveProved

/-- Continuous involutive time reversal on the quotient and its fixed throat. -/
def effectiveMappingTorusPTCoreClosed (s : ProgramStatus) : Prop :=
  s.mappingTorusTimeReversalContinuousProved /\
  s.mappingTorusTimeReversalInvolutiveProved /\
  s.fixedThroatQuotientInclusionPTEquivariantProved

/-- Associated orbit quotient, projection, zero section and parity monodromy. -/
def associatedNormalLineQuotientCoreClosed (s : ProgramStatus) : Prop :=
  s.associatedNormalLineOrbitQuotientConstructed /\
  s.associatedNormalLineProjectionContinuousSurjectiveProved /\
  s.associatedNormalLineZeroSectionConstructed /\
  s.associatedNormalLineOneLoopFlipProved /\
  s.associatedNormalLineTwoLoopRestorationProved

/-- Effective two-sheeted orientation cover and trivial topological normal pullback. -/
def effectiveThroatOrientationDoubleCoverCoreClosed (s : ProgramStatus) : Prop :=
  s.effectiveThroatOrientationDoubleCoveringMapProved /\
  s.throatOrientationDoubleCoverFiberTwoProved /\
  s.throatOrientationDeckInvolutionFreeProved /\
  s.throatNormalPullbackTopologicallyTrivializedProved

/-- Exact topological side decomposition and its one-sided quotient image. -/
def effectiveThroatComplementSidesCoreClosed (s : ProgramStatus) : Prop :=
  s.equatorialSphereComplementTwoOpenSidesProved /\
  s.reflectionAndDeckExchangeCoverSidesProved /\
  s.effectiveThroatComplementOneSidedImageProved /\
  s.effectiveThroatComplementPTInvariantProved

/-- Path-connected sign sides and path-connected effective complement. -/
def effectiveThroatComplementConnectedCoreClosed (s : ProgramStatus) : Prop :=
  s.positiveAndNegativeSphereSidesPathConnectedProved /\
  s.positiveCoverSidePathConnectedProved /\
  s.effectiveThroatComplementPathConnectedProved /\
  s.effectiveThroatComplementConnectedProved

/-- Analytic cover atlases and the honest `C⁰` quotient-manifold frontier. -/
def mappingTorusSmoothAtlasFrontierCoreClosed (s : ProgramStatus) : Prop :=
  s.algebraicSphereCoversAnalyticManifoldsProved /\
  s.throatCoverTopologicalEmbeddingAndC0Proved /\
  s.effectiveMappingTorusTopologicalManifoldProved /\
  s.effectiveThroatTopologicalManifoldProved /\
  s.quotientProjectionLocalHomeomorphAndC0Proved

/-- Smooth deck maps, throat-cover inclusion and compatible local atlas
transitions. -/
def mappingTorusSmoothDeckDescentFrontierClosed (s : ProgramStatus) : Prop :=
  s.smoothDeckActionsAndAtlasTransitionsProved

/-- Installed analytic quotient manifolds, local-diffeomorphism projections
and smooth descended throat inclusion. -/
def mappingTorusSmoothQuotientManifoldCoreClosed (s : ProgramStatus) : Prop :=
  s.effectiveMappingTorusSmoothQuotientManifoldProved /\
  s.effectiveThroatSmoothQuotientManifoldProved /\
  s.quotientProjectionLocalDiffeomorphProved /\
  s.fixedThroatQuotientInclusionContMDiffProved

/-- Analytic PT diffeomorphisms on both effective quotient manifolds. -/
def mappingTorusSmoothPTCoreClosed (s : ProgramStatus) : Prop :=
  s.mappingTorusTimeReversalContMDiffProved /\
  s.mappingTorusTimeReversalDiffeomorphConstructed

/-- Checked smooth embedding: the inclusion is a closed topological embedding,
has a fixed one-dimensional immersion complement, is a manifold immersion and
satisfies Mathlib's global `IsSmoothEmbedding`.  Null/joint stratification is
not asserted here. -/
def fixedThroatSmoothEmbeddingFrontierClosed (s : ProgramStatus) : Prop :=
  s.fixedThroatQuotientInclusionIsClosedEmbeddingProved /\
  s.fixedThroatQuotientDifferentialInjectiveProved /\
  s.fixedThroatNormalQuotientFinrankOneProved /\
  s.fixedThroatQuotientInclusionIsImmersionOfComplementProved /\
  s.fixedThroatQuotientInclusionIsSmoothEmbeddingProved

/-- Actual analytic sign-clutched normal line bundle, its global algebraic
comparison with the differential normal family, and both global complex `Z4`
root lines with smooth real underliers.  A smooth atlas on the differential
quotient family, hence a smooth comparison with it, is not asserted. -/
def fixedThroatSmoothNormalBundleClosed (s : ProgramStatus) : Prop :=
  s.fixedThroatNormalVectorBundleConstructed /\
  s.fixedThroatNormalVectorBundleContMDiffProved /\
  s.fixedThroatNormalFiberPointwiseDifferentialEquivProved /\
  s.fixedThroatNormalOneLoopMinusIdentityProved /\
  s.fixedThroatNormalGlobalAlgebraicEquivProved /\
  s.fixedThroatNormalZ4RootComplexLineConstructed /\
  s.fixedThroatNormalZ4RootSmoothRealUnderlierProved /\
  s.fixedThroatNormalZ4RootSquaresToNormalSignProved /\
  s.fixedThroatNormalZ4RootPTConjugationProved /\
  s.fixedThroatNormalPinMinusPrincipalBundleConstructed

/-- Compactness of both actual effective quotient manifolds. -/
def effectiveQuotientCompactnessClosed (s : ProgramStatus) : Prop :=
  s.effectiveMappingTorusCompactProved /\
  s.effectiveThroatCompactProved

/-- Smooth topology and one-sided-throat milestone. -/
def smoothMappingTorusCoreClosed (s : ProgramStatus) : Prop :=
  effectiveTopologicalMappingTorusCoreClosed s /\
  effectiveMappingTorusPTCoreClosed s /\
  associatedNormalLineQuotientCoreClosed s /\
  effectiveThroatOrientationDoubleCoverCoreClosed s /\
  effectiveThroatComplementSidesCoreClosed s /\
  effectiveThroatComplementConnectedCoreClosed s /\
  mappingTorusSmoothAtlasFrontierCoreClosed s /\
  mappingTorusSmoothDeckDescentFrontierClosed s /\
  mappingTorusSmoothQuotientManifoldCoreClosed s /\
  mappingTorusSmoothPTCoreClosed s /\
  fixedThroatSmoothEmbeddingFrontierClosed s /\
  fixedThroatSmoothNormalBundleClosed s /\
  s.nonzeroTranslationDerived /\
  effectiveQuotientCompactnessClosed s /\
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

/-- The singular mirror quotient is a separate geometry, not a relabeling of the glide quotient. -/
def mirrorAlternativeAuditClosed (s : ProgramStatus) : Prop :=
  s.mirrorOrbifoldAlternativeConstructed /\
  s.mirrorIsotropyAndGlideTranslationSeparated /\
  s.mirrorAndGlideLoopGroupsDistinguished /\
  s.singularAndSmoothSpectralTheoriesCompared

/-- Full D8 closure. -/
def fullD8Closure (s : ProgramStatus) : Prop :=
  smoothMappingTorusCoreClosed s /\
  cyclicRepresentationAuditClosed s /\
  mirrorAlternativeAuditClosed s /\
  s.pinReflectionSquareConventionFixed /\
  s.euclideanLorentzianPinDictionaryDerived /\
  s.internalSymmetryGeometricallyDerived

/-- A smooth free quotient does not yet provide an orbifold isotropy group. -/
theorem missing_internal_symmetry_blocks_full_d8
    (s : ProgramStatus)
    (hMissing : Not s.internalSymmetryGeometricallyDerived) :
    Not (fullD8Closure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, _, _, _, hInternal⟩
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
  rcases hClosed with ⟨_, _, _, _, hDictionary, _⟩
  exact hMissing hDictionary

/-- The mirror-orbifold alternative must be recomputed rather than imported into the smooth model. -/
theorem missing_singular_smooth_comparison_blocks_full_d8
    (s : ProgramStatus)
    (hMissing : Not s.singularAndSmoothSpectralTheoriesCompared) :
    Not (fullD8Closure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, hMirror, _, _, _⟩
  exact hMissing hMirror.2.2.2

end JanusFundamentalGeometryD8TopologyRepresentation
end JanusFormal
