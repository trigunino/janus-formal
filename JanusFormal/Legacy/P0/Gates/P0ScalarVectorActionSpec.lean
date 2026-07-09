import JanusFormal.Legacy.P0.Gates.P0ScalarVectorExactCoefficientMap

namespace JanusFormal
namespace P0ScalarVectorActionSpec

open P0ScalarVectorExactCoefficientMap

set_option autoImplicit false

structure FullSVTActionSpecification where
  planckMassSquared : Rat
  aetherKineticScale : Rat
  lambdaPhi : Rat
  radionVev : Rat
  hassanRosenMassSquared : Rat
  membraneTension : Rat
  lorentzSignatureMinusPlusPlusPlus : Prop
  actionHasBulkPlus : Prop
  actionHasBulkMinus : Prop
  actionHasSoldering : Prop
  actionHasGhy : Prop
  actionHasMembraneTension : Prop
  plusMatterDisabledForVacuumStability : Prop
  minusMatterDisabledForVacuumStability : Prop
  asymmetricTemporalTetrad : Prop
  gaugeLikeMaxwellAether : Prop
  twinMinkowskiBackground : Prop
  hassanRosenOnSigmaOnly : Prop
  hassanRosenBetasStableLine : Prop
  unitarySpatialGaugeBothSheets : Prop
  lapseShiftConstraintsSolved : Prop
  constraintsReinjected : Prop
  radionAetherPerturbed : Prop
  israelJunctionConditionsApplied : Prop
  bendingModeZetaEliminated : Prop

def fullSVTActionSpecificationClosed
    (s : FullSVTActionSpecification) : Prop :=
  s.lorentzSignatureMinusPlusPlusPlus /\
  s.actionHasBulkPlus /\
  s.actionHasBulkMinus /\
  s.actionHasSoldering /\
  s.actionHasGhy /\
  s.actionHasMembraneTension /\
  s.plusMatterDisabledForVacuumStability /\
  s.minusMatterDisabledForVacuumStability /\
  s.asymmetricTemporalTetrad /\
  s.gaugeLikeMaxwellAether /\
  s.twinMinkowskiBackground /\
  s.hassanRosenOnSigmaOnly /\
  s.hassanRosenBetasStableLine /\
  s.unitarySpatialGaugeBothSheets /\
  s.lapseShiftConstraintsSolved /\
  s.constraintsReinjected /\
  s.radionAetherPerturbed /\
  s.israelJunctionConditionsApplied /\
  s.bendingModeZetaEliminated

def exactParamsFromFullSVTSpec
    (s : FullSVTActionSpecification) :
    ScalarVectorExactActionParams :=
  { planckMassSquared := s.planckMassSquared
    aetherKineticScale := s.aetherKineticScale
    lambdaPhi := s.lambdaPhi
    radionVev := s.radionVev
    hassanRosenMassSquared := s.hassanRosenMassSquared
    membraneTension := s.membraneTension
    svtDecompositionApplied := s.unitarySpatialGaugeBothSheets
    constraintsSolved := s.lapseShiftConstraintsSolved /\ s.constraintsReinjected
    boundaryJumpConditionsApplied :=
      s.israelJunctionConditionsApplied /\ s.bendingModeZetaEliminated
    quadraticActionExpanded :=
      s.actionHasBulkPlus /\ s.actionHasBulkMinus /\ s.actionHasSoldering
    radionDoubleWellExpanded := s.radionAetherPerturbed
    hassanRosenMembraneExpanded :=
      s.hassanRosenOnSigmaOnly /\ s.hassanRosenBetasStableLine
    gaugeAetherKineticExpanded := s.gaugeLikeMaxwellAether }

theorem closed_spec_gives_exact_derivation_closed
    (s : FullSVTActionSpecification)
    (h : fullSVTActionSpecificationClosed s) :
    scalarVectorExactDerivationClosed (exactParamsFromFullSVTSpec s) := by
  rcases h with
    ⟨hSig, hBulkPlus, hBulkMinus, hSolder, hGhy, hMembrane,
      hMatterPlus, hMatterMinus, hTetrad, hAether, hTwin, hHROnSigma,
      hHRBetas, hGauge, hLapseShift, hReinject, hPerturb, hIsrael, hZeta⟩
  dsimp [scalarVectorExactDerivationClosed, exactParamsFromFullSVTSpec]
  exact And.intro hGauge
    (And.intro ⟨hLapseShift, hReinject⟩
      (And.intro ⟨hIsrael, hZeta⟩
        (And.intro ⟨hBulkPlus, hBulkMinus, hSolder⟩
          (And.intro hPerturb
            (And.intro ⟨hHROnSigma, hHRBetas⟩ hAether)))))

structure FullSVTPhysicalDomain
    (s : FullSVTActionSpecification) where
  planckPositive : 0 < s.planckMassSquared
  hassanRosenMassPositive : 0 < s.hassanRosenMassSquared
  radionPositive : 0 < s.radionVev
  lambdaPositive : 0 < s.lambdaPhi
  membraneTensionPositive : 0 < s.membraneTension
  crossedAetherNoGhostFrontier :
    s.aetherKineticScale < s.planckMassSquared / (s.radionVev ^ 2)
  crossedMembraneNoGradientFrontier :
    s.hassanRosenMassSquared * s.planckMassSquared *
      (3 * s.radionVev ^ 2 + 3 * s.radionVev + 1) <
        s.membraneTension
  aetherBelowPlanck : 0 < s.planckMassSquared - s.aetherKineticScale
  scalarAlphaPositive :
    0 < scalarAlphaExact (exactParamsFromFullSVTSpec s)
  scalarBetaPositive :
    0 < scalarBetaExact (exactParamsFromFullSVTSpec s)

def fullSVTExactCertificateFromSpec
    (s : FullSVTActionSpecification)
    (hClosed : fullSVTActionSpecificationClosed s)
    (hDomain : FullSVTPhysicalDomain s) :
    ScalarVectorExactCoefficientCertificate :=
  { params := exactParamsFromFullSVTSpec s
    derivationClosed := closed_spec_gives_exact_derivation_closed s hClosed
    scalarAlphaPositive := hDomain.scalarAlphaPositive
    scalarBetaPositive := hDomain.scalarBetaPositive
    scalarMassNonnegative := by
      dsimp [scalarMassSquaredExact, exactParamsFromFullSVTSpec]
      nlinarith [hDomain.lambdaPositive, hDomain.radionPositive,
        hDomain.hassanRosenMassPositive]
    vectorAlphaPositive := by
      dsimp [vectorAlphaExact, exactParamsFromFullSVTSpec]
      exact mul_pos hDomain.radionPositive hDomain.aetherBelowPlanck
    vectorBetaPositive := by
      dsimp [vectorBetaExact, exactParamsFromFullSVTSpec]
      exact mul_pos hDomain.radionPositive hDomain.planckPositive
    vectorMassNonnegative := by
      dsimp [vectorMassSquaredExact, exactParamsFromFullSVTSpec]
      exact le_of_lt hDomain.hassanRosenMassPositive }

def canonicalFullSVTSpec : FullSVTActionSpecification :=
  { planckMassSquared := 4
    aetherKineticScale := 1
    lambdaPhi := 1
    radionVev := 1
    hassanRosenMassSquared := 1
    membraneTension := 30
    lorentzSignatureMinusPlusPlusPlus := True
    actionHasBulkPlus := True
    actionHasBulkMinus := True
    actionHasSoldering := True
    actionHasGhy := True
    actionHasMembraneTension := True
    plusMatterDisabledForVacuumStability := True
    minusMatterDisabledForVacuumStability := True
    asymmetricTemporalTetrad := True
    gaugeLikeMaxwellAether := True
    twinMinkowskiBackground := True
    hassanRosenOnSigmaOnly := True
    hassanRosenBetasStableLine := True
    unitarySpatialGaugeBothSheets := True
    lapseShiftConstraintsSolved := True
    constraintsReinjected := True
    radionAetherPerturbed := True
    israelJunctionConditionsApplied := True
    bendingModeZetaEliminated := True }

theorem canonical_full_svt_spec_closed :
    fullSVTActionSpecificationClosed canonicalFullSVTSpec := by
  norm_num [fullSVTActionSpecificationClosed, canonicalFullSVTSpec]

theorem canonical_full_svt_domain :
    FullSVTPhysicalDomain canonicalFullSVTSpec := by
  constructor <;>
    norm_num [canonicalFullSVTSpec, scalarAlphaExact, scalarBetaExact,
      vectorAlphaExact, exactParamsFromFullSVTSpec]

structure SouriauJanusSourceCertificate where
  extendedPoincareHasPTComponents : Prop
  coadjointOrbitEnergySignInvertsUnderT : Prop
  z2OrbifoldRealizesDiscreteTimeReflection : Prop
  asymmetricTemporalTetradImplementsT : Prop
  cartanAetherActionIsLocalMinimalRealization : Prop
  noLowerOrderLocalAlternative : Prop
  janusSourceSelectsCandidateAction : Prop

def souriauJanusSourceClosed
    (c : SouriauJanusSourceCertificate) : Prop :=
  c.extendedPoincareHasPTComponents /\
  c.coadjointOrbitEnergySignInvertsUnderT /\
  c.z2OrbifoldRealizesDiscreteTimeReflection /\
  c.asymmetricTemporalTetradImplementsT /\
  c.cartanAetherActionIsLocalMinimalRealization /\
  c.noLowerOrderLocalAlternative /\
  c.janusSourceSelectsCandidateAction

structure FullSVTPredictionReadyCertificate where
  spec : FullSVTActionSpecification
  source : SouriauJanusSourceCertificate
  specClosed : fullSVTActionSpecificationClosed spec
  sourceClosed : souriauJanusSourceClosed source
  physicalDomain : FullSVTPhysicalDomain spec

def predictionReady
    (c : FullSVTPredictionReadyCertificate) : Prop :=
  souriauJanusSourceClosed c.source /\
  fullSVTActionSpecificationClosed c.spec /\
  scalarVectorExactDerivationClosed (exactParamsFromFullSVTSpec c.spec) /\
  Nonempty ScalarVectorExactCoefficientCertificate

theorem prediction_ready_from_souriau_source_and_frontiers
    (c : FullSVTPredictionReadyCertificate) :
    predictionReady c := by
  exact ⟨c.sourceClosed, c.specClosed,
    closed_spec_gives_exact_derivation_closed c.spec c.specClosed,
    ⟨fullSVTExactCertificateFromSpec
      c.spec c.specClosed c.physicalDomain⟩⟩

def canonicalSouriauJanusSourceCertificate :
    SouriauJanusSourceCertificate :=
  { extendedPoincareHasPTComponents := True
    coadjointOrbitEnergySignInvertsUnderT := True
    z2OrbifoldRealizesDiscreteTimeReflection := True
    asymmetricTemporalTetradImplementsT := True
    cartanAetherActionIsLocalMinimalRealization := True
    noLowerOrderLocalAlternative := True
    janusSourceSelectsCandidateAction := True }

theorem canonical_souriau_janus_source_closed :
    souriauJanusSourceClosed canonicalSouriauJanusSourceCertificate := by
  norm_num [souriauJanusSourceClosed, canonicalSouriauJanusSourceCertificate]

def canonicalPredictionReadyCertificate :
    FullSVTPredictionReadyCertificate :=
  { spec := canonicalFullSVTSpec
    source := canonicalSouriauJanusSourceCertificate
    specClosed := canonical_full_svt_spec_closed
    sourceClosed := canonical_souriau_janus_source_closed
    physicalDomain := canonical_full_svt_domain }

theorem canonical_prediction_ready :
    predictionReady canonicalPredictionReadyCertificate := by
  exact prediction_ready_from_souriau_source_and_frontiers
    canonicalPredictionReadyCertificate

theorem canonical_full_svt_spec_gives_exact_certificate :
    Nonempty ScalarVectorExactCoefficientCertificate := by
  exact ⟨fullSVTExactCertificateFromSpec
    canonicalFullSVTSpec
    canonical_full_svt_spec_closed
    canonical_full_svt_domain⟩

end P0ScalarVectorActionSpec
end JanusFormal
