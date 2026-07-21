import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonVectorPairingBridge4D
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSpinTwoInvariantPairing

/-! # Common-domain spin-two pairing certificate -/

namespace JanusFormal
namespace P0EFTJanusProgramPCommonSpinTwoPairingBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonVectorPairingBridge4D
open P0EFTJanusSpinTwoInvariantPairing

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Exact change of coordinates from the genuine D9 traceless tensor to the
spin-two representation basis used by the classification theorem. -/
def tracelessTensorSpinTwoEquiv : TracelessTensor3 ≃ SpinTwoVector where
  toFun tensor :=
    { a := (tensor.xx - tensor.yy) / 2
      b := (tensor.xx + tensor.yy) / 2
      c := tensor.xy
      d := tensor.xz
      e := tensor.yz }
  invFun vector :=
    { xx := vector.a + vector.b
      yy := vector.b - vector.a
      xy := vector.c
      xz := vector.d
      yz := vector.e }
  left_inv tensor := by
    rcases tensor with ⟨xx, yy, xy, xz, yz⟩
    ext <;> simp <;> ring
  right_inv vector := by
    rcases vector with ⟨a, b, c, d, e⟩
    ext <;> simp <;> ring

/-- Frobenius contraction including the dependent `zz = -xx - yy`
component of a traceless symmetric tensor. -/
def tracelessTensorFrobenius
    (first second : TracelessTensor3) : Real :=
  first.xx * second.xx + first.yy * second.yy +
    (-first.xx - first.yy) * (-second.xx - second.yy) +
    2 * (first.xy * second.xy + first.xz * second.xz +
      first.yz * second.yz)

def tracelessTensorPairing
    (pairing : SymmetricPairing5)
    (first second : TracelessTensor3) : Real :=
  pairingValue pairing
    (tracelessTensorSpinTwoEquiv first)
    (tracelessTensorSpinTwoEquiv second)

/-- The abstract spin-two classification becomes the Frobenius contraction
on the actual D9 traceless tensor, up to its single normalization. -/
theorem tracelessTensorPairing_classified
    (pairing : SymmetricPairing5)
    (hInvariant : LieGeneratorInvariant pairing)
    (first second : TracelessTensor3) :
    tracelessTensorPairing pairing first second =
      (pairing.q44 / 2) * tracelessTensorFrobenius first second := by
  rw [spin_two_invariant_pairing_classification pairing hInvariant]
  rcases first with ⟨firstXX, firstYY, firstXY, firstXZ, firstYZ⟩
  rcases second with ⟨secondXX, secondYY, secondXY, secondXZ, secondYZ⟩
  simp [tracelessTensorPairing, tracelessTensorSpinTwoEquiv,
    tracelessTensorFrobenius, pairingValue, canonicalSpinTwoPairing]
  ring

/-- Evaluation on the traceless parts of the genuine global metric
variations at one point of the effective throat. -/
def completeVariationSpinTwoPairingAt
    (pairing : SymmetricPairing5)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : Real :=
  tracelessTensorPairing pairing
    (tracelessPart (first.metricPerturbationAt period hPeriod sector point))
    (tracelessPart (second.metricPerturbationAt period hPeriod sector point))

theorem completeVariationSpinTwoPairingAt_classified
    (pairing : SymmetricPairing5)
    (hInvariant : LieGeneratorInvariant pairing)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    completeVariationSpinTwoPairingAt period hPeriod pairing first second
        sector point =
      (pairing.q44 / 2) * tracelessTensorFrobenius
        (tracelessPart (first.metricPerturbationAt period hPeriod sector point))
        (tracelessPart
          (second.metricPerturbationAt period hPeriod sector point)) :=
  tracelessTensorPairing_classified pairing hInvariant _ _

/-- The common-domain certificate now contains both actual vector and
spin-two pairing classifications. -/
structure ProgramPCommonSpinTwoPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  vectorCertificate :
    ProgramPCommonVectorPairingCertificate4D period hPeriod domain
  spinTwo_pairing_classified :
    ∀ pairing, LieGeneratorInvariant pairing →
      ∀ first second sector point,
        completeVariationSpinTwoPairingAt period hPeriod pairing first second
            sector point =
          (pairing.q44 / 2) * tracelessTensorFrobenius
            (tracelessPart
              (first.metricPerturbationAt period hPeriod sector point))
            (tracelessPart
              (second.metricPerturbationAt period hPeriod sector point))

def programPCommonSpinTwoPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProgramPCommonSpinTwoPairingCertificate4D period hPeriod domain where
  vectorCertificate :=
    programPCommonVectorPairingCertificate4D period hPeriod domain
  spinTwo_pairing_classified := by
    intro pairing hInvariant first second sector point
    exact completeVariationSpinTwoPairingAt_classified period hPeriod pairing
      hInvariant first second sector point

theorem canonicalProgramPCommonSpinTwoPairingCertificate4D_nonempty :
    Nonempty
      (ProgramPCommonSpinTwoPairingCertificate4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)) :=
  ⟨programPCommonSpinTwoPairingCertificate4D period hPeriod _⟩

end
end P0EFTJanusProgramPCommonSpinTwoPairingBridge4D
end JanusFormal
