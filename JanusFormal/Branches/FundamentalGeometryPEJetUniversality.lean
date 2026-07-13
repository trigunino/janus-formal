/-
Program P.E-J: proof program for finite-jet universality of natural operators on
decorated SpinC immersions.

The original strong conjecture is corrected in five ways:

1. Peetre--Slovak gives a local finite-jet factorization under regularity and
   locality hypotheses;
2. naturality is equivalent to equivariance of the unique jet evaluator once
   holonomic jets are realizable/surjective;
3. the evaluator is smooth, not automatically polynomial;
4. a uniform global order, ellipticity and field-content selection require
   independent hypotheses;
5. the categorical morphism law is holonomic jet composition, not ordinary
   composition of maps between unprolonged representation fibers.

The head also contains exact algebraic cores for an action groupoid, orbitwise
descent, the second-immersion-jet normal slice, the abelian connection one-jet
curvature slice, their universal invariant-factorization properties, and
residual symmetry descent to the reduced data. The latest concrete gates derive
the normalized second-jet source action from the second-order chain-rule formula,
classify concrete abelian connection one-jets by curvature, construct the first
combined low-order quotient represented by `(B,F)`, prove the pointwise
orthogonal splitting of a linear isometric immersion derivative, identify the
reduced normal quadratic tensor with the normal projection of the
connection-corrected second derivative in the flat adapted model, prove its
residual `O(T) × O(N)` equivariance, prove smooth tangent/normal projector
fields, construct a smooth local adapted orthonormal frame by projected normal
seeds and Gram--Schmidt, prove the formal two-jet transformation law under a
moving adapted frame, construct canonical normal transport and moving-frame
equivariance of the second fundamental form, prove the Čech cocycle laws for
residual adapted-frame transitions, instantiate their determinant-one oriented
reduction `SO(T) × SO(N)`, formalize the central double-cover defect obstructing
a Spin lift, prove the abstract SpinC diagonal-cancellation theorem, show that
local square roots of a determinant-line cocycle have a two-torsion triple
defect, instantiate that two-torsion by `±1` in the complex circle, and construct
the concrete rank-two circle double cover with projection `z ↦ z²`, kernel
`{±1}`, an exact diagonal quotient and its specialized SpinC cocycle theorem.
They still do not identify the circle model with the matrix/Clifford definitions
of `SO(2)` and `Spin(2)`, instantiate the higher-dimensional Clifford Spin cover,
or prove the characteristic-class matching for the actual Janus determinant
line.
-/

import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteJetEquivariance
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteOrderUniformization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothNotPolynomial
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCorrectedJetUniversality
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusJetOperatorComposition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusStructuredJetActionGroupoid
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusOrbitwiseDescent
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondJetNormalForm
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAbelianConnectionJetNormalForm
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderJetQuotientUniversality
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusResidualJetSymmetry
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConcreteSecondJetChainRule
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConcreteAbelianConnectionJet
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderStructuredBackground
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAdaptedOrthogonalSplitting
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalFormJet
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalResidualEquivariance
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothProjectorField
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothAdaptedFrame
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusMovingAdaptedFrameSecondJet
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusMovingNormalTransport
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAdaptedFrameOverlapCocycle
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusDeterminantOrientedReduction
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCentralLiftCocycleObstruction
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSpinCDiagonalDefectCancellation
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusDeterminantSquareRootDefect
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCirclePhaseTwoTorsion
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSpin2CircleModel

namespace JanusFormal
namespace JanusFundamentalGeometryPEJetUniversality

set_option autoImplicit false

structure ProgramStatus where
  regularLocalOperatorSheafDefined : Prop
  peetreSlovakHypothesesVerified : Prop
  localFiniteJetFactorizationDerived : Prop
  finiteJetActionsConstructed : Prop
  holonomicJetRealizationProved : Prop
  naturalityEquivarianceIffProved : Prop
  evaluatorUniquenessProved : Prop
  holonomicJetCompositionProved : Prop
  actionGroupoidLawsProved : Prop
  orbitwiseDescentEquivalenceProved : Prop
  abstractSecondJetNormalFormProved : Prop
  abstractAbelianConnectionNormalFormProved : Prop
  lowOrderInvariantQuotientUniversalityProved : Prop
  abstractResidualEquivariantReductionProved : Prop
  concreteSecondJetChainRuleAndQuotientProved : Prop
  concreteAbelianConnectionOrbitClassificationProved : Prop
  combinedLowOrderStructuredQuotientProved : Prop
  pointwiseAdaptedOrthogonalSplittingProved : Prop
  pointwiseSecondFundamentalJetBridgeProved : Prop
  pointwiseResidualOrthogonalEquivarianceProved : Prop
  smoothProjectorFieldProved : Prop
  smoothAdaptedFrameProved : Prop
  movingAdaptedFrameSecondJetLawProved : Prop
  movingNormalTransportEquivarianceProved : Prop
  adaptedFrameOverlapCocycleProved : Prop
  abstractOrientedSubcocycleProved : Prop
  determinantOrientedResidualReductionProved : Prop
  centralDoubleCoverDefectTheoryProved : Prop
  spinCDiagonalDefectCancellationProved : Prop
  determinantSquareRootDefectTheoryProved : Prop
  circlePhaseTwoTorsionInstantiated : Prop
  spin2CircleDoubleCoverModelProved : Prop
  naiveRepresentationCategoryCorrected : Prop
  smoothNonpolynomialCounterexampleProved : Prop
  polynomialClaimCorrected : Prop
  finiteCoverUniformizationProved : Prop
  unboundedGlobalOrderCounterexampleProved : Prop
  correctedTheoremStated : Prop
  spinCImmersionJetGroupoidConstructed : Prop
  structuredJetNormalFormProved : Prop
  residualFrameActionsConstructed : Prop
  janusOrbitStrataClassified : Prop
  crossStratumExtensionProved : Prop
  actualJanusNaturalBundlesInserted : Prop
  ellipticSymbolsClassified : Prop
  globalUniformOrderRegionDerived : Prop

/-- Formal/logical theorem core, including orbitwise descent, concrete low-order
orbit reductions, the combined `(B,F)` quotient, pointwise orthogonal splitting,
the connection-corrected second fundamental-form bridge, residual orthogonal
equivariance, smooth projector fields, smooth adapted frames, moving-frame
second-jet and normal-transport laws, adapted-frame Čech cocycles,
determinant-one `SO(T) × SO(N)` reduction, central double-cover defects, SpinC
diagonal cancellation, determinant square-root defect matching, concrete circle
two-torsion and the rank-two circle double-cover/diagonal-quotient model. -/
def theoremCoreClosed (s : ProgramStatus) : Prop :=
  s.regularLocalOperatorSheafDefined /\
  s.peetreSlovakHypothesesVerified /\
  s.localFiniteJetFactorizationDerived /\
  s.finiteJetActionsConstructed /\
  s.holonomicJetRealizationProved /\
  s.naturalityEquivarianceIffProved /\
  s.evaluatorUniquenessProved /\
  s.holonomicJetCompositionProved /\
  s.actionGroupoidLawsProved /\
  s.orbitwiseDescentEquivalenceProved /\
  s.abstractSecondJetNormalFormProved /\
  s.abstractAbelianConnectionNormalFormProved /\
  s.lowOrderInvariantQuotientUniversalityProved /\
  s.abstractResidualEquivariantReductionProved /\
  s.concreteSecondJetChainRuleAndQuotientProved /\
  s.concreteAbelianConnectionOrbitClassificationProved /\
  s.combinedLowOrderStructuredQuotientProved /\
  s.pointwiseAdaptedOrthogonalSplittingProved /\
  s.pointwiseSecondFundamentalJetBridgeProved /\
  s.pointwiseResidualOrthogonalEquivarianceProved /\
  s.smoothProjectorFieldProved /\
  s.smoothAdaptedFrameProved /\
  s.movingAdaptedFrameSecondJetLawProved /\
  s.movingNormalTransportEquivarianceProved /\
  s.adaptedFrameOverlapCocycleProved /\
  s.abstractOrientedSubcocycleProved /\
  s.determinantOrientedResidualReductionProved /\
  s.centralDoubleCoverDefectTheoryProved /\
  s.spinCDiagonalDefectCancellationProved /\
  s.determinantSquareRootDefectTheoryProved /\
  s.circlePhaseTwoTorsionInstantiated /\
  s.spin2CircleDoubleCoverModelProved /\
  s.naiveRepresentationCategoryCorrected /\
  s.smoothNonpolynomialCounterexampleProved /\
  s.polynomialClaimCorrected /\
  s.finiteCoverUniformizationProved /\
  s.unboundedGlobalOrderCounterexampleProved /\
  s.correctedTheoremStated

/-- Full Janus specialization. -/
def fullJanusJetUniversalityClosed (s : ProgramStatus) : Prop :=
  theoremCoreClosed s /\
  s.spinCImmersionJetGroupoidConstructed /\
  s.structuredJetNormalFormProved /\
  s.residualFrameActionsConstructed /\
  s.janusOrbitStrataClassified /\
  s.crossStratumExtensionProved /\
  s.actualJanusNaturalBundlesInserted /\
  s.ellipticSymbolsClassified /\
  s.globalUniformOrderRegionDerived

/-- The abstract theorem does not close the Janus specialization without the
actual adapted SpinC structured-jet groupoid. -/
theorem missing_janus_jet_groupoid_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.spinCImmersionJetGroupoidConstructed) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hGroupoid

/-- The pointwise and coordinate-local frame theorems do not replace a full
manifold-level structured jet-isomorphism theorem. -/
theorem missing_structured_normal_form_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.structuredJetNormalFormProved) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hNormalForm

/-- The proved local frame, oriented-cocycle, circle two-torsion and rank-two
double-cover layers still require the matrix/Clifford identification of the
circle model, higher-dimensional Clifford Spin projections, geometric
characteristic-class matching, smooth principal bundles and their actions on all
Janus natural sectors. -/
theorem missing_residual_actions_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.residualFrameActionsConstructed) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hResidual

/-- Orbitwise descent does not solve extension between distinct isotropy strata. -/
theorem missing_cross_stratum_extension_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.crossStratumExtensionProved) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hExtension

/-- Natural finite-jet classification does not imply ellipticity. -/
theorem missing_symbol_classification_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.ellipticSymbolsClassified) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hSymbols

/-- One global jet order still requires a bounded configuration region. -/
theorem missing_uniform_region_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.globalUniformOrderRegionDerived) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hRegion

end JanusFundamentalGeometryPEJetUniversality
end JanusFormal
