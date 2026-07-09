import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4APSIndexPackageObligationGate
import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4OrbifoldCoverRatioObligationGate
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTDiracCartanAPSPTReduction
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxIntegerTheorem
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldHolonomyFluxQuantization
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldEulerCharacteristic
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldVolumeDerivation
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTThinShellTetradChirality
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryFactorizationAPSBridge
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryCoefficientsLichnerowicz
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTPinAnomalySelection
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldIntegerFluxLaw
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxOrientationRule
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldJanusOrientationRule
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxQuantizationLaw

namespace JanusFormal
namespace P0EFTJanusZ4HardGlobalAtomicFrontierGate

set_option autoImplicit false

structure APSPinFrontier where
  pinMinusLiftConstructed : Prop
  apsFredholmDomainConstructed : Prop
  ptSpectralEtaCancellationConstructed : Prop
  parityAnomalyCancelled : Prop
  traceRegularizationConstructed : Prop

def apsFrontierClosed (f : APSPinFrontier) : Prop :=
  f.pinMinusLiftConstructed /\
  f.apsFredholmDomainConstructed /\
  f.ptSpectralEtaCancellationConstructed /\
  f.parityAnomalyCancelled /\
  f.traceRegularizationConstructed

theorem aps_pt_chain_transports_to_frontier
    (f : APSPinFrontier)
    (domain : P0EFTDiracCartanAPSPTReduction.DiracCartanAPSDomain)
    (pt : P0EFTDiracCartanAPSPTReduction.PTSpectralAction)
    (hLift : f.pinMinusLiftConstructed)
    (hFredholm : f.apsFredholmDomainConstructed)
    (hEta :
      P0EFTDiracCartanAPSPTReduction.etaCancelsConditionally domain pt ->
        f.ptSpectralEtaCancellationConstructed)
    (hConditionalEta :
      P0EFTDiracCartanAPSPTReduction.etaCancelsConditionally domain pt)
    (hParity : f.parityAnomalyCancelled)
    (hTrace : f.traceRegularizationConstructed) :
    apsFrontierClosed f := by
  exact And.intro hLift
    (And.intro hFredholm
      (And.intro (hEta hConditionalEta)
        (And.intro hParity hTrace)))

theorem aps_boundary_geometry_chain_transports_to_frontier
    (f : APSPinFrontier)
    (s : P0EFTThinShellTetradChirality.OrbifoldTetradSoldering)
    (shell : P0EFTThinShellTetradChirality.TraceTorsionThinShell)
    (bf : P0EFTBoundaryFactorizationAPSBridge.BoundaryFactorization)
    (bridge : P0EFTBoundaryFactorizationAPSBridge.APSBridge)
    (coeff : P0EFTBoundaryCoefficientsLichnerowicz.BoundaryCoefficientMatching)
    (zero : P0EFTBoundaryCoefficientsLichnerowicz.LichnerowiczZeroModeCheck)
    (anom : P0EFTPinAnomalySelection.PinAnomalyData)
    (hSolder :
      P0EFTThinShellTetradChirality.tetradSignFromSoldering s)
    (hShell :
      P0EFTThinShellTetradChirality.chiralityFromTraceTorsionShell shell)
    (hSpectral :
      P0EFTBoundaryFactorizationAPSBridge.finalBoundarySpectralClosure bf bridge)
    (hCoeff :
      P0EFTBoundaryCoefficientsLichnerowicz.coefficientMatchingClosed coeff)
    (hZero :
      P0EFTBoundaryCoefficientsLichnerowicz.zeroModesClosedConditionally zero)
    (hAnomaly :
      P0EFTPinAnomalySelection.anomalyFreeChoice
        anom P0EFTPinAnomalySelection.PinChoice.pinMinus)
    (hPin :
      s.tetradSignTransition ->
      shell.chiralBoundaryProjectorDerived ->
      coeff.gammaFiveMatchesOrientedNormal ->
      f.pinMinusLiftConstructed)
    (hFredholm :
      bridge.apsOperatorIsGammaNormalTangentialDirac ->
      bridge.chiralHalfSpaceMatchesAPSSpectralHalfSpace ->
      f.apsFredholmDomainConstructed)
    (hEta :
      zero.zeroModesAbsent ->
      bridge.zeroModesEvenOrAbsent ->
      f.ptSpectralEtaCancellationConstructed)
    (hParity :
      P0EFTPinAnomalySelection.anomalyFreeChoice
        anom P0EFTPinAnomalySelection.PinChoice.pinMinus ->
      f.parityAnomalyCancelled)
    (hTrace :
      coeff.janusPinGammaFiveCoeffKnown ->
      coeff.gammaFiveMatchesOrientedNormal ->
      f.traceRegularizationConstructed) :
    apsFrontierClosed f := by
  exact And.intro
    (hPin hSolder.right.right.right hShell.right.right.right.right.left
      hCoeff.right.right.right.right.right.right.right)
    (And.intro
      (hFredholm hSpectral.right.left hSpectral.right.right.right.left)
      (And.intro
        (hEta hZero.right.right.right.right hSpectral.right.right.right.right)
        (And.intro
          (hParity hAnomaly)
          (hTrace hCoeff.right.right.left
            hCoeff.right.right.right.right.right.right.right))))

theorem aps_frontier_closes_refined_gate
    (g : P0EFTJanusZ4APSIndexPackageObligationGate.APSIndexPackageObligationGate)
    (hLocal : P0EFTJanusZ4APSIndexPackageObligationGate.apsLocalInterfacesReady g)
    (hPin : g.pinMinusLiftSquaredMinusOne)
    (hFredholm : g.apsBoundaryProjectorFredholm)
    (hEta : g.etaZeroModeCancellationGlobal)
    (hParity : g.noParityAnomalyGlobal)
    (hTrace : g.traceRegularizationStandardGlobal) :
    P0EFTJanusZ4APSIndexPackageObligationGate.apsGlobalAtomicObligationsClosed g := by
  exact And.intro hLocal
    (And.intro hPin
      (And.intro hFredholm
        (And.intro hEta (And.intro hParity hTrace))))

theorem aps_frontier_transports_to_refined_gate
    (f : APSPinFrontier)
    (g : P0EFTJanusZ4APSIndexPackageObligationGate.APSIndexPackageObligationGate)
    (hClosed : apsFrontierClosed f)
    (hLocal : P0EFTJanusZ4APSIndexPackageObligationGate.apsLocalInterfacesReady g)
    (hPin :
      f.pinMinusLiftConstructed -> g.pinMinusLiftSquaredMinusOne)
    (hFredholm :
      f.apsFredholmDomainConstructed -> g.apsBoundaryProjectorFredholm)
    (hEta :
      f.ptSpectralEtaCancellationConstructed -> g.etaZeroModeCancellationGlobal)
    (hParity :
      f.parityAnomalyCancelled -> g.noParityAnomalyGlobal)
    (hTrace :
      f.traceRegularizationConstructed -> g.traceRegularizationStandardGlobal) :
    P0EFTJanusZ4APSIndexPackageObligationGate.apsGlobalAtomicObligationsClosed g := by
  exact aps_frontier_closes_refined_gate g hLocal
    (hPin hClosed.left)
    (hFredholm hClosed.right.left)
    (hEta hClosed.right.right.left)
    (hParity hClosed.right.right.right.left)
    (hTrace hClosed.right.right.right.right)

structure OrbifoldCoverFrontier where
  integerFluxTheoremClosed : Prop
  branchIndicesComputed : Prop
  eulerCoverDataClosed : Prop
  volumeRatioTwoToOneDerived : Prop
  uniquenessOfTwoToOneRatio : Prop

def orbifoldFrontierClosed (f : OrbifoldCoverFrontier) : Prop :=
  f.integerFluxTheoremClosed /\
  f.branchIndicesComputed /\
  f.eulerCoverDataClosed /\
  f.volumeRatioTwoToOneDerived /\
  f.uniquenessOfTwoToOneRatio

structure HardGlobalFrontierClosurePolicy where
  apsDirectWitnessRequired : Prop
  orbifoldDirectWitnessRequired : Prop
  syntheticTrueClosureForbidden : Prop
  importedTheoremMustMatchTarget : Prop
  noFitPromotionRequiresClosedFrontier : Prop

def frontierClosurePolicyReady
    (p : HardGlobalFrontierClosurePolicy) : Prop :=
  p.apsDirectWitnessRequired /\
  p.orbifoldDirectWitnessRequired /\
  p.syntheticTrueClosureForbidden /\
  p.importedTheoremMustMatchTarget /\
  p.noFitPromotionRequiresClosedFrontier

theorem frontier_policy_ready_enforces_no_synthetic_closure
    (p : HardGlobalFrontierClosurePolicy)
    (h : frontierClosurePolicyReady p) :
    p.syntheticTrueClosureForbidden /\
    p.importedTheoremMustMatchTarget /\
    p.noFitPromotionRequiresClosedFrontier := by
  exact And.intro h.right.right.left
    (And.intro h.right.right.right.left h.right.right.right.right)

theorem orbifold_flux_chain_transports_to_frontier
    (f : OrbifoldCoverFrontier)
    (t : P0EFTOrbifoldFluxIntegerTheorem.OrbifoldFluxIntegerTheorem)
    (q : P0EFTOrbifoldHolonomyFluxQuantization.OrbifoldHolonomyFluxQuantization)
    (e : P0EFTOrbifoldEulerCharacteristic.OrbifoldEulerCharacteristic)
    (d : P0EFTOrbifoldVolumeDerivation.OrbifoldVolumeDerivation)
    (hInteger :
      P0EFTOrbifoldFluxIntegerTheorem.janusBranchIndicesForced t ->
        f.integerFluxTheoremClosed)
    (hForced :
      P0EFTOrbifoldFluxIntegerTheorem.janusBranchIndicesForced t)
    (hBranch :
      P0EFTOrbifoldHolonomyFluxQuantization.branchIndicesComputed q ->
        f.branchIndicesComputed)
    (hBranchComputed :
      P0EFTOrbifoldHolonomyFluxQuantization.branchIndicesComputed q)
    (hEuler :
      P0EFTOrbifoldEulerCharacteristic.eulerCoverDataClosed e ->
        f.eulerCoverDataClosed)
    (hEulerClosed :
      P0EFTOrbifoldEulerCharacteristic.eulerCoverDataClosed e)
    (hRatio :
      P0EFTOrbifoldVolumeDerivation.orbifoldVolumeRatioTwoToOneDerived d ->
        f.volumeRatioTwoToOneDerived)
    (hRatioDerived :
      P0EFTOrbifoldVolumeDerivation.orbifoldVolumeRatioTwoToOneDerived d)
    (hUnique : f.uniquenessOfTwoToOneRatio) :
    orbifoldFrontierClosed f := by
  exact And.intro (hInteger hForced)
    (And.intro (hBranch hBranchComputed)
      (And.intro (hEuler hEulerClosed)
        (And.intro (hRatio hRatioDerived) hUnique)))

theorem orbifold_integer_flux_orientation_chain_transports_to_frontier
    (f : OrbifoldCoverFrontier)
    (law : P0EFTOrbifoldIntegerFluxLaw.IntegerFluxLaw)
    (orient : P0EFTOrbifoldFluxOrientationRule.OrbifoldFluxOrientationRule)
    (t : P0EFTOrbifoldFluxIntegerTheorem.OrbifoldFluxIntegerTheorem)
    (q : P0EFTOrbifoldHolonomyFluxQuantization.OrbifoldHolonomyFluxQuantization)
    (e : P0EFTOrbifoldEulerCharacteristic.OrbifoldEulerCharacteristic)
    (d : P0EFTOrbifoldVolumeDerivation.OrbifoldVolumeDerivation)
    (hLaw : P0EFTOrbifoldIntegerFluxLaw.integerFluxLawDerived law)
    (hOrient : P0EFTOrbifoldFluxOrientationRule.orientationRuleClosed orient)
    (hInteger :
      P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed t ->
        f.integerFluxTheoremClosed)
    (hCycle : t.singularCycleDefined)
    (hFlux : t.normalizedSpinConnectionFluxDefined)
    (hIntegerLaw : t.integerFluxLawProved)
    (hPositiveOrientation : t.janusOrientationSelectsPositiveDoubleCover)
    (hNegativeOrientation : t.mirrorOrientationSelectsNegativeSingleCover)
    (hBranch :
      P0EFTOrbifoldHolonomyFluxQuantization.branchIndicesComputed q ->
        f.branchIndicesComputed)
    (hBranchComputed :
      P0EFTOrbifoldHolonomyFluxQuantization.branchIndicesComputed q)
    (hEuler :
      P0EFTOrbifoldEulerCharacteristic.eulerCoverDataClosed e ->
        f.eulerCoverDataClosed)
    (hEulerClosed :
      P0EFTOrbifoldEulerCharacteristic.eulerCoverDataClosed e)
    (hRatio :
      P0EFTOrbifoldVolumeDerivation.orbifoldVolumeRatioTwoToOneDerived d ->
        f.volumeRatioTwoToOneDerived)
    (hRatioDerived :
      P0EFTOrbifoldVolumeDerivation.orbifoldVolumeRatioTwoToOneDerived d)
    (hUnique : f.uniquenessOfTwoToOneRatio) :
    orbifoldFrontierClosed f := by
  have hIntegerData :
      P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed t :=
    P0EFTOrbifoldIntegerFluxLaw.integer_flux_law_supplies_integer_flux_data
      law t hLaw hCycle hFlux hIntegerLaw
  have hForced :
      P0EFTOrbifoldFluxIntegerTheorem.janusBranchIndicesForced t :=
    P0EFTOrbifoldFluxOrientationRule.orientation_rule_supplies_janus_cover_selection
      orient t hOrient hCycle hFlux hIntegerLaw
      hPositiveOrientation hNegativeOrientation
  exact And.intro
    (hInteger hIntegerData)
    (And.intro
      (hBranch hBranchComputed)
      (And.intro
        (hEuler hEulerClosed)
        (And.intro (hRatio hRatioDerived) hUnique)))

theorem orbifold_frontier_closes_refined_gate
    (g : P0EFTJanusZ4OrbifoldCoverRatioObligationGate.OrbifoldCoverRatioObligationGate)
    (hLocal : P0EFTJanusZ4OrbifoldCoverRatioObligationGate.orbifoldLocalInterfacesReady g)
    (hEulerHolonomy : g.globalEulerHolonomyClassComputed)
    (hRatio : g.volumeCoverRatioTwoToOne)
    (hUnique : g.globalVolumeRatioUniqueTwoToOne) :
    P0EFTJanusZ4OrbifoldCoverRatioObligationGate.orbifoldGlobalAtomicObligationsClosed g := by
  exact And.intro hLocal
    (And.intro hEulerHolonomy (And.intro hRatio hUnique))

theorem orbifold_frontier_transports_to_refined_gate
    (f : OrbifoldCoverFrontier)
    (g : P0EFTJanusZ4OrbifoldCoverRatioObligationGate.OrbifoldCoverRatioObligationGate)
    (hClosed : orbifoldFrontierClosed f)
    (hLocal : P0EFTJanusZ4OrbifoldCoverRatioObligationGate.orbifoldLocalInterfacesReady g)
    (hEuler :
      f.eulerCoverDataClosed -> g.globalEulerHolonomyClassComputed)
    (hRatio :
      f.volumeRatioTwoToOneDerived -> g.volumeCoverRatioTwoToOne)
    (hUnique :
      f.uniquenessOfTwoToOneRatio -> g.globalVolumeRatioUniqueTwoToOne) :
    P0EFTJanusZ4OrbifoldCoverRatioObligationGate.orbifoldGlobalAtomicObligationsClosed g := by
  exact orbifold_frontier_closes_refined_gate g hLocal
    (hEuler hClosed.right.right.left)
    (hRatio hClosed.right.right.right.left)
    (hUnique hClosed.right.right.right.right)

theorem missing_trace_regularization_blocks_aps_frontier
    (f : APSPinFrontier)
    (hMissing : Not f.traceRegularizationConstructed) :
    Not (apsFrontierClosed f) := by
  intro h
  exact hMissing h.right.right.right.right

theorem missing_uniqueness_blocks_orbifold_frontier
    (f : OrbifoldCoverFrontier)
    (hMissing : Not f.uniquenessOfTwoToOneRatio) :
    Not (orbifoldFrontierClosed f) := by
  intro h
  exact hMissing h.right.right.right.right

end P0EFTJanusZ4HardGlobalAtomicFrontierGate
end JanusFormal
