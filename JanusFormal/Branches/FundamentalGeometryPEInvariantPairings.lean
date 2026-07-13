/-
Program P-D / P-E-Pairings: pointwise invariant pairing and graded-selection
models for the natural Janus field sectors.

This head collects the independent representation-theory gates. It does not
claim that the exact global SpinC/PT/Z4/BRST symmetry group or all multiplicity
spaces have been constructed. Pointwise multiplicity one is also not a global
uniqueness theorem: natural pairing families form a module over invariant scalar
functions on the structured-jet base, and invariant ranks can jump between
isotropy strata.
-/

import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSectorQuantumNumbers
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusGradedFusionRules
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusVectorInvariantPairing
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSpinTwoInvariantPairing
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusMultiplicitySpaceFreedom
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusInvariantCoefficientModule
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusIsotropyStratification

namespace JanusFormal
namespace JanusFundamentalGeometryPEInvariantPairings

set_option autoImplicit false

structure ProgramStatus where
  sectorLabelsDefined : Prop
  z4AndGaugeNeutralityRulesDerived : Prop
  gradedFusionRulesDerived : Prop
  vectorPairingClassified : Prop
  spinTwoPairingAudited : Prop
  multiplicitySpaceFreedomExhibited : Prop
  invariantCoefficientModuleExhibited : Prop
  isotropyStratificationCounterexampleProved : Prop
  continuousRotationClassificationDerived : Prop
  spinorPairingsClassified : Prop
  ghostAndBRSTPairingsClassified : Prop
  janusIsotropyStratificationClassified : Prop
  pointwisePairingsGlobalized : Prop
  survivingNormalizationsDerived : Prop

/-- Finite pointwise pairing foundation, including the obstructions from
background-dependent invariant scalar coefficients and isotropy jumps. -/
def finitePairingFoundationClosed (s : ProgramStatus) : Prop :=
  s.sectorLabelsDefined /\
  s.z4AndGaugeNeutralityRulesDerived /\
  s.gradedFusionRulesDerived /\
  s.vectorPairingClassified /\
  s.spinTwoPairingAudited /\
  s.multiplicitySpaceFreedomExhibited /\
  s.invariantCoefficientModuleExhibited /\
  s.isotropyStratificationCounterexampleProved

/-- Full physical/global pairing classification. -/
def fullPairingClassificationClosed (s : ProgramStatus) : Prop :=
  finitePairingFoundationClosed s /\
  s.continuousRotationClassificationDerived /\
  s.spinorPairingsClassified /\
  s.ghostAndBRSTPairingsClassified /\
  s.janusIsotropyStratificationClassified /\
  s.pointwisePairingsGlobalized /\
  s.survivingNormalizationsDerived

/-- A pointwise finite-group audit cannot substitute for the global bundle theorem. -/
theorem missing_globalization_blocks_full_pairing_classification
    (s : ProgramStatus)
    (hMissing : Not s.pointwisePairingsGlobalized) :
    Not (fullPairingClassificationClosed s) := by
  rintro ⟨hFinite, hRotation, hSpinor, hGhost, hStrata,
    hGlobalized, hNormalization⟩
  exact hMissing hGlobalized

/-- The finite jump witness does not classify the actual Janus orbit types or
prove smooth extension across their singular strata. -/
theorem missing_janus_stratification_blocks_full_pairing_classification
    (s : ProgramStatus)
    (hMissing : Not s.janusIsotropyStratificationClassified) :
    Not (fullPairingClassificationClosed s) := by
  rintro ⟨hFinite, hRotation, hSpinor, hGhost, hStrata,
    hGlobalized, hNormalization⟩
  exact hMissing hStrata

/-- Multiplicity-one pairings still require a physical normalization and control
of invariant coefficient functions. -/
theorem missing_normalization_blocks_full_pairing_classification
    (s : ProgramStatus)
    (hMissing : Not s.survivingNormalizationsDerived) :
    Not (fullPairingClassificationClosed s) := by
  rintro ⟨hFinite, hRotation, hSpinor, hGhost, hStrata,
    hGlobalized, hNormalization⟩
  exact hMissing hNormalization

end JanusFundamentalGeometryPEInvariantPairings
end JanusFormal
