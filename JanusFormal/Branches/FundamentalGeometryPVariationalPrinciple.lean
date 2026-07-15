/-
Program P: select or reconstruct the Janus action.

The branch separates four routes:

* P-A: a relative universal property for an action class, with bulk on-shell
  reduction as its strongest concrete realization;
* P-B: anomaly cancellation as a discrete selector and consistency filter;
* P-C: the inverse problem of the calculus of variations, using Helmholtz
  conditions to reconstruct a Lagrangian from Euler--Lagrange/Hessian data;
* P-E: classification of invariant bilinear pairings between the natural field
  sectors under tangent rotations, PT and the normal-root Z4.

The entry no-go proves that an L2, symplectic or Kahler-like geometry on moduli
cannot select a scalar functional by itself.
-/

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusModuliGeometryNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusUniversalActionProperty
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAnomalySelection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHessianHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPolynomialHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteRankPolynomialHelmholtz
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearGaugeNoetherReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonlinearGaugeFlowNoether
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeOrbitDescent
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeOrbitInvariantEquiv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBulkUniversalHelmholtzSynthesis
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoupledSectorHelmholtzSelection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkHelmholtzReciprocity
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteRankParentSchurHelmholtz
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedTwoMetricBoundaryFirstVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedTwoMetricEulerNoether
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedBimetricQuadraticFrechetSpectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProportionalBranchTransverseNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProportionalBranchHigherOrderNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAnomalyHelmholtzIndependence
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPEChargeSelection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPEInvariantPairings
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPETensorPairingFreedom

namespace JanusFormal
namespace JanusFundamentalGeometryPVariationalPrinciple

set_option autoImplicit false

structure ProgramStatus where
  moduliMetricNoGoProved : Prop
  moduliSymplecticNoGoProved : Prop
  kahlerGeometryNotSufficientProved : Prop
  paAffineHessianAmbiguityProved : Prop
  paRelativeUniversalSpecificationConstructed : Prop
  paUniqueExistenceRelativeToSpecificationProved : Prop
  paBulkOnShellReductionConstructed : Prop
  paDirichletToNeumannOrSchurHessianDerived : Prop
  paBoundaryActionUniqueRelativeToParentProved : Prop
  paParentBulkTwoSectorReciprocitySynthesized : Prop
  paFiniteRankCoefficientSchurHelmholtzSynthesized : Prop
  paFiniteRankSchurFrechetDerivativesProved : Prop
  paFiniteRankBulkSignStabilityClassified : Prop
  paPTFlatProportionalActualVariationalStabilityProved : Prop
  paReducedTwoMetricActualBoundaryVariationProved : Prop
  paConditionalReducedBimetricFrechetStabilityProved : Prop
  paReducedPublishedKappaMinusOneKineticNoGoProved : Prop
  paProportionalBranchTransverseNonuniquenessProved : Prop
  paProportionalBranchTransverseTwoJetNonuniquenessProved : Prop
  pbPTAnomalyCancellationProved : Prop
  pbParityEvenFreedomProved : Prop
  pbTrivializationFreedomProved : Prop
  pbDiscreteMultiplicitySelectorDerived : Prop
  pbAnomalyHelmholtzLogicalIndependenceProved : Prop
  pcFormalSelfAdjointnessNecessaryProved : Prop
  pcQuadraticHelmholtzIffProved : Prop
  pcQuadraticEulerCubicHelmholtzIffProved : Prop
  pcAffineReconstructionAmbiguityProved : Prop
  pcPTNormalizedUniqueReconstructionProved : Prop
  pcQuadraticCoupledSectorPTRealizabilityIffProved : Prop
  pcFiniteRankCoefficientHelmholtzIffProved : Prop
  pcFiniteRankPolynomialFrechetGradientProved : Prop
  pcFiniteRankPolynomialJacobianSelfAdjointProved : Prop
  pcFiniteRankActualHelmholtzIffActualPolynomialGradientProved : Prop
  pcConvexOpenHelmholtzReconstructionProved : Prop
  pcConditionalLinearGaugeNoetherReconstructionProved : Prop
  pcConditionalLinearGaugeNoetherIffProved : Prop
  pcConditionalNonlinearGaugeFlowNoetherIffProved : Prop
  pcConditionalNonlinearGaugeInvariantRadialReconstructionProved : Prop
  pcGaugeOrbitQuotientDescentProved : Prop
  pcGaugeOrbitInvariantFunctionEquivalenceProved : Prop
  pcReducedTwoMetricEulerNoetherProved : Prop
  peZ4ChargeNeutralityDerived : Prop
  peConjugateQuarterPairingUniqueUpToScale : Prop
  peUnchargedPTDoubletRetainsTwoCoefficients : Prop
  peVectorPairingUniqueUpToScale : Prop
  peScalarVectorPairingVanishing : Prop
  peScalarTracelessPairingVanishing : Prop
  peVectorTracelessPairingVanishing : Prop
  peCubicTensorPairingHasTwoScales : Prop
  peContinuousRotationForcesFrobeniusPairing : Prop
  peSpinorAndGaugePairingsClassified : Prop
  peMultiplicitySpacesComputed : Prop
  invariantLocalFunctionalBasisClassified : Prop
  fullEulerLagrangeOperatorDerived : Prop
  nonlinearHelmholtzConditionsProved : Prop
  variationalBicomplexObstructionVanishing : Prop
  nullLagrangiansAndBoundaryTermsClassified : Prop
  anomalyConstraintsApplied : Prop
  parentBulkOrMicroscopicSelectionPrincipleDerived : Prop
  actionNormalizationDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  globalActionClassReconstructed : Prop
  hessianMatchesNaturalFredholmFamily : Prop
  uniqueStableVacuumDerived : Prop
  absoluteScaleDerivedNoFit : Prop

/-- Algebraic and logical P-A/P-B/P-C foundation. -/
def programPFoundationClosed (s : ProgramStatus) : Prop :=
  s.moduliMetricNoGoProved /\
  s.moduliSymplecticNoGoProved /\
  s.kahlerGeometryNotSufficientProved /\
  s.paAffineHessianAmbiguityProved /\
  s.paRelativeUniversalSpecificationConstructed /\
  s.paUniqueExistenceRelativeToSpecificationProved /\
  s.paBulkOnShellReductionConstructed /\
  s.paDirichletToNeumannOrSchurHessianDerived /\
  s.paBoundaryActionUniqueRelativeToParentProved /\
  s.paParentBulkTwoSectorReciprocitySynthesized /\
  s.paFiniteRankCoefficientSchurHelmholtzSynthesized /\
  s.paFiniteRankSchurFrechetDerivativesProved /\
  s.paFiniteRankBulkSignStabilityClassified /\
  s.paPTFlatProportionalActualVariationalStabilityProved /\
  s.paReducedTwoMetricActualBoundaryVariationProved /\
  s.paConditionalReducedBimetricFrechetStabilityProved /\
  s.paReducedPublishedKappaMinusOneKineticNoGoProved /\
  s.paProportionalBranchTransverseNonuniquenessProved /\
  s.paProportionalBranchTransverseTwoJetNonuniquenessProved /\
  s.pbPTAnomalyCancellationProved /\
  s.pbParityEvenFreedomProved /\
  s.pbTrivializationFreedomProved /\
  s.pbDiscreteMultiplicitySelectorDerived /\
  s.pbAnomalyHelmholtzLogicalIndependenceProved /\
  s.pcFormalSelfAdjointnessNecessaryProved /\
  s.pcQuadraticHelmholtzIffProved /\
  s.pcQuadraticEulerCubicHelmholtzIffProved /\
  s.pcAffineReconstructionAmbiguityProved /\
  s.pcPTNormalizedUniqueReconstructionProved /\
  s.pcQuadraticCoupledSectorPTRealizabilityIffProved /\
  s.pcFiniteRankCoefficientHelmholtzIffProved /\
  s.pcFiniteRankPolynomialFrechetGradientProved /\
  s.pcFiniteRankPolynomialJacobianSelfAdjointProved /\
  s.pcFiniteRankActualHelmholtzIffActualPolynomialGradientProved /\
  s.pcConvexOpenHelmholtzReconstructionProved /\
  s.pcConditionalLinearGaugeNoetherReconstructionProved /\
  s.pcConditionalLinearGaugeNoetherIffProved /\
  s.pcConditionalNonlinearGaugeFlowNoetherIffProved /\
  s.pcConditionalNonlinearGaugeInvariantRadialReconstructionProved /\
  s.pcGaugeOrbitQuotientDescentProved /\
  s.pcGaugeOrbitInvariantFunctionEquivalenceProved /\
  s.pcReducedTwoMetricEulerNoetherProved

/-- P-E discrete and tangent-representation classification. -/
def invariantPairingFoundationClosed (s : ProgramStatus) : Prop :=
  s.peZ4ChargeNeutralityDerived /\
  s.peConjugateQuarterPairingUniqueUpToScale /\
  s.peUnchargedPTDoubletRetainsTwoCoefficients /\
  s.peVectorPairingUniqueUpToScale /\
  s.peScalarVectorPairingVanishing /\
  s.peScalarTracelessPairingVanishing /\
  s.peVectorTracelessPairingVanishing /\
  s.peCubicTensorPairingHasTwoScales /\
  s.peContinuousRotationForcesFrobeniusPairing /\
  s.peSpinorAndGaugePairingsClassified /\
  s.peMultiplicitySpacesComputed

/-- Nonlinear variational reconstruction. -/
def nonlinearReconstructionClosed (s : ProgramStatus) : Prop :=
  s.invariantLocalFunctionalBasisClassified /\
  s.fullEulerLagrangeOperatorDerived /\
  s.nonlinearHelmholtzConditionsProved /\
  s.variationalBicomplexObstructionVanishing /\
  s.nullLagrangiansAndBoundaryTermsClassified /\
  s.anomalyConstraintsApplied /\
  s.parentBulkOrMicroscopicSelectionPrincipleDerived /\
  s.actionNormalizationDerived /\
  s.finiteCountertermsFixedMicroscopically /\
  s.globalActionClassReconstructed /\
  s.hessianMatchesNaturalFredholmFamily

/-- Predictive physical closure. -/
def fullProgramPClosure (s : ProgramStatus) : Prop :=
  programPFoundationClosed s /\
  invariantPairingFoundationClosed s /\
  nonlinearReconstructionClosed s /\
  s.uniqueStableVacuumDerived /\
  s.absoluteScaleDerivedNoFit

/-- P-A alone is only relative: without a parent or microscopic selector it cannot close. -/
theorem missing_parent_selection_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.parentBulkOrMicroscopicSelectionPrincipleDerived) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, hNonlinear, _, _⟩
  rcases hNonlinear with ⟨_, _, _, _, _, _, hParent, _⟩
  exact hMissing hParent

/-- P-B anomaly cancellation cannot replace parity-even Euler--Lagrange dynamics. -/
theorem missing_euler_lagrange_operator_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.fullEulerLagrangeOperatorDerived) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, hNonlinear, _, _⟩
  exact hMissing hNonlinear.2.1

/-- P-C requires the nonlinear Helmholtz theorem, not merely a symmetric quadratic proxy. -/
theorem missing_nonlinear_helmholtz_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.nonlinearHelmholtzConditionsProved) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, hNonlinear, _, _⟩
  exact hMissing hNonlinear.2.2.1

/-- P-E cannot be closed from finite monodromy alone: continuous rotations are required in the tensor sector. -/
theorem missing_continuous_rotation_classification_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.peContinuousRotationForcesFrobeniusPairing) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, hPairing, _, _, _⟩
  exact hMissing hPairing.2.2.2.2.2.2.2.2.1

/-- Spinor and gauge multiplicity spaces remain an explicit P-E obligation. -/
theorem missing_spinor_pairing_classification_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.peSpinorAndGaugePairingsClassified) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, hPairing, _, _, _⟩
  exact hMissing hPairing.2.2.2.2.2.2.2.2.2.1

/-- Scheme-independent prediction requires a microscopic finite-part law. -/
theorem missing_finite_counterterm_law_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.finiteCountertermsFixedMicroscopically) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, _, hNonlinear, _, _⟩
  rcases hNonlinear with ⟨_, _, _, _, _, _, _, _, hCounterterm, _⟩
  exact hMissing hCounterterm

/--
Program-P verdict:

* P-A is canonical only relative to a specification or parent theory;
* P-B is an anomaly/discrete consistency filter;
* P-C reconstructs an action class only after Helmholtz and variational
  cohomology close;
* P-E turns residual quadratic couplings into invariant-pairing dimensions.
  It proves multiplicity zero/one for several low-rank sectors, shows that the
  normal-root Z4 removes same-charge masses, and proves that finite cubic
  symmetry is insufficient for the traceless-tensor pairing.
-/
structure ProgramPVerdict where
  moduliGeometryAloneInsufficient : Prop
  universalPropertyRelativeNotAbsolute : Prop
  bulkOnShellActionCanonicalRelativeToParent : Prop
  anomalyCancellationConstraintNotFullSelection : Prop
  helmholtzRouteNecessaryForInverseProblem : Prop
  z4ConjugatePairingMultiplicityOne : Prop
  unchargedPTMultiplicityFreedomRemains : Prop
  vectorAndCrossPairingClassificationDerived : Prop
  finiteSymmetryInsufficientForTensorUniqueness : Prop
  continuousRotationRestoresTensorMultiplicityOne : Prop
  spinorAndRepeatedIrrepMultiplicitiesRemain : Prop
  ptAndNormalizationRemoveAffineAmbiguity : Prop
  parentOrMicroscopicPrincipleStillRequired : Prop
  finiteRenormalizationStillRequired : Prop


def programPVerdictClosed (s : ProgramPVerdict) : Prop :=
  s.moduliGeometryAloneInsufficient /\
  s.universalPropertyRelativeNotAbsolute /\
  s.bulkOnShellActionCanonicalRelativeToParent /\
  s.anomalyCancellationConstraintNotFullSelection /\
  s.helmholtzRouteNecessaryForInverseProblem /\
  s.z4ConjugatePairingMultiplicityOne /\
  s.unchargedPTMultiplicityFreedomRemains /\
  s.vectorAndCrossPairingClassificationDerived /\
  s.finiteSymmetryInsufficientForTensorUniqueness /\
  s.continuousRotationRestoresTensorMultiplicityOne /\
  s.spinorAndRepeatedIrrepMultiplicitiesRemain /\
  s.ptAndNormalizationRemoveAffineAmbiguity /\
  s.parentOrMicroscopicPrincipleStillRequired /\
  s.finiteRenormalizationStillRequired

end JanusFundamentalGeometryPVariationalPrinciple
end JanusFormal
