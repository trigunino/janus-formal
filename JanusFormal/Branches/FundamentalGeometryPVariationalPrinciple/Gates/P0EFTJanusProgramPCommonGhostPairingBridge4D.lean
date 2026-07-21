import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonSpinTwoPairingBridge4D
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSectorQuantumNumbers

/-! # Common-domain ghost pairing selection -/

namespace JanusFormal
namespace P0EFTJanusProgramPCommonGhostPairingBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonSpinTwoPairingBridge4D
open P0EFTJanusSectorQuantumNumbers

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Column zero is the U(1) ghost and column one its antighost. -/
def u1GhostColumnLabel (column : Fin 2) : SectorLabel :=
  if column = 0 then u1Ghost else u1Antighost

@[simp] theorem u1GhostColumnLabel_zero :
    u1GhostColumnLabel 0 = u1Ghost := by
  simp [u1GhostColumnLabel]

@[simp] theorem u1GhostColumnLabel_one :
    u1GhostColumnLabel 1 = u1Antighost := by
  simp [u1GhostColumnLabel]

abbrev GhostBilinear2 := Fin 2 → Fin 2 → Real

/-- A coefficient can survive only in a pairing block allowed by all discrete
P-D quantum numbers. -/
def RespectsU1GhostSelection (pairing : GhostBilinear2) : Prop :=
  ∀ first second,
    Not (PairingAllowed (u1GhostColumnLabel first)
      (u1GhostColumnLabel second)) →
      pairing first second = 0

/-- The selected normal form retains the two directed ghost-antighost
coefficients and removes both forbidden diagonal blocks. -/
def selectedU1GhostPairing (pairing : GhostBilinear2) : GhostBilinear2 :=
  fun first second =>
    if first = 0 ∧ second = 1 then pairing 0 1
    else if first = 1 ∧ second = 0 then pairing 1 0
    else 0

theorem u1GhostPairing_selection_classification
    (pairing : GhostBilinear2)
    (hSelection : RespectsU1GhostSelection pairing) :
    pairing = selectedU1GhostPairing pairing := by
  funext first second
  fin_cases first <;> fin_cases second
  · simpa [selectedU1GhostPairing] using
      hSelection 0 0 (by native_decide)
  · simp [selectedU1GhostPairing]
  · simp [selectedU1GhostPairing]
  · simpa [selectedU1GhostPairing] using
      hSelection 1 1 (by native_decide)

/-- Bilinear value on the two actual U(1) ghost columns of complete global
variations at a point of the true throat. -/
def completeVariationU1GhostPairingAt
    (pairing : GhostBilinear2)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : Real :=
  pairing 0 0 *
      d9U1Ghost period hPeriod first.independent sector 0 point *
      d9U1Ghost period hPeriod second.independent sector 0 point +
    pairing 0 1 *
      d9U1Ghost period hPeriod first.independent sector 0 point *
      d9U1Ghost period hPeriod second.independent sector 1 point +
    pairing 1 0 *
      d9U1Ghost period hPeriod first.independent sector 1 point *
      d9U1Ghost period hPeriod second.independent sector 0 point +
    pairing 1 1 *
      d9U1Ghost period hPeriod first.independent sector 1 point *
      d9U1Ghost period hPeriod second.independent sector 1 point

theorem completeVariationU1GhostPairingAt_classified
    (pairing : GhostBilinear2)
    (hSelection : RespectsU1GhostSelection pairing)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    completeVariationU1GhostPairingAt period hPeriod pairing first second
        sector point =
      pairing 0 1 *
          d9U1Ghost period hPeriod first.independent sector 0 point *
          d9U1Ghost period hPeriod second.independent sector 1 point +
        pairing 1 0 *
          d9U1Ghost period hPeriod first.independent sector 1 point *
          d9U1Ghost period hPeriod second.independent sector 0 point := by
  have hPairing := u1GhostPairing_selection_classification pairing hSelection
  have h00 := congrFun (congrFun hPairing 0) 0
  have h11 := congrFun (congrFun hPairing 1) 1
  simp [selectedU1GhostPairing] at h00 h11
  simp [completeVariationU1GhostPairingAt, h00, h11]

structure ProgramPCommonGhostPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  spinTwoCertificate :
    ProgramPCommonSpinTwoPairingCertificate4D period hPeriod domain
  ghost_pairing_classified :
    ∀ pairing, RespectsU1GhostSelection pairing →
      ∀ first second sector point,
        completeVariationU1GhostPairingAt period hPeriod pairing first second
            sector point =
          pairing 0 1 *
              d9U1Ghost period hPeriod first.independent sector 0 point *
              d9U1Ghost period hPeriod second.independent sector 1 point +
            pairing 1 0 *
              d9U1Ghost period hPeriod first.independent sector 1 point *
              d9U1Ghost period hPeriod second.independent sector 0 point

def programPCommonGhostPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProgramPCommonGhostPairingCertificate4D period hPeriod domain where
  spinTwoCertificate :=
    programPCommonSpinTwoPairingCertificate4D period hPeriod domain
  ghost_pairing_classified := by
    intro pairing hSelection first second sector point
    exact completeVariationU1GhostPairingAt_classified period hPeriod pairing
      hSelection first second sector point

theorem canonicalProgramPCommonGhostPairingCertificate4D_nonempty :
    Nonempty
      (ProgramPCommonGhostPairingCertificate4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)) :=
  ⟨programPCommonGhostPairingCertificate4D period hPeriod _⟩

end
end P0EFTJanusProgramPCommonGhostPairingBridge4D
end JanusFormal
