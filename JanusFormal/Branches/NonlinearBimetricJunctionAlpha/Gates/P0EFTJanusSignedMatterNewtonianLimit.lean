import Mathlib

namespace JanusFormal
namespace P0EFTJanusSignedMatterNewtonianLimit

set_option autoImplicit false

/-- The two PT-related matter sectors. -/
inductive JanusSector where
  | positive
  | negative
  deriving DecidableEq

/-- Signed gravitational charge carried by matter, not by the graviton kinetic term. -/
def gravitationalCharge : JanusSector → ℝ
  | JanusSector.positive => 1
  | JanusSector.negative => -1

/-- Reduced coefficient of the Newtonian potential `V = coefficient * G m1 m2/r`. -/
def newtonianPotentialCoefficient
    (first second : JanusSector) : ℝ :=
  -(gravitationalCharge first * gravitationalCharge second)

/-- Positive-sector sources attract one another. -/
@[simp] theorem positive_positive_coefficient :
    newtonianPotentialCoefficient
      JanusSector.positive JanusSector.positive = -1 := by
  rfl

/-- Negative-sector sources also attract one another. -/
@[simp] theorem negative_negative_coefficient :
    newtonianPotentialCoefficient
      JanusSector.negative JanusSector.negative = -1 := by
  norm_num [newtonianPotentialCoefficient, gravitationalCharge]

/-- Opposite sectors repel. -/
@[simp] theorem positive_negative_coefficient :
    newtonianPotentialCoefficient
      JanusSector.positive JanusSector.negative = 1 := by
  norm_num [newtonianPotentialCoefficient, gravitationalCharge]

/-- Opposite sectors repel in the reverse ordering as well. -/
@[simp] theorem negative_positive_coefficient :
    newtonianPotentialCoefficient
      JanusSector.negative JanusSector.positive = 1 := by
  norm_num [newtonianPotentialCoefficient, gravitationalCharge]

/-- The interaction sign depends only on whether the sectors agree. -/
theorem potential_sign_by_sector_equality
    (first second : JanusSector) :
    newtonianPotentialCoefficient first second =
      if first = second then -1 else 1 := by
  cases first <;> cases second <;> simp

/-- PT exchanges the two signed matter charges. -/
def ptSector : JanusSector → JanusSector
  | JanusSector.positive => JanusSector.negative
  | JanusSector.negative => JanusSector.positive

@[simp] theorem pt_sector_involutive (sector : JanusSector) :
    ptSector (ptSector sector) = sector := by
  cases sector <;> rfl

@[simp] theorem charge_is_pt_odd (sector : JanusSector) :
    gravitationalCharge (ptSector sector) =
      -gravitationalCharge sector := by
  cases sector <;> norm_num [ptSector, gravitationalCharge]

/-- PT preserves the pair-potential coefficient when applied to both sources. -/
theorem simultaneous_pt_preserves_potential
    (first second : JanusSector) :
    newtonianPotentialCoefficient (ptSector first) (ptSector second) =
      newtonianPotentialCoefficient first second := by
  unfold newtonianPotentialCoefficient
  rw [charge_is_pt_odd, charge_is_pt_odd]
  ring

/--
This realizes the Janus attraction/repulsion matrix without a negative kinetic
spin-2 degree of freedom.  The remaining physical test is whether the signed
charge coupling follows from a covariant matter action and respects free fall,
Bianchi identities and radiative stability.
-/
structure SignedMatterCompletionStatus where
  positiveSpinTwoKineticTermsDerived : Prop
  ptOddMatterChargeDerived : Prop
  sameSectorAttractionRecovered : Prop
  crossSectorRepulsionRecovered : Prop
  covariantMatterActionDerived : Prop
  weakEquivalencePrincipleAudited : Prop
  combinedBianchiIdentityClosed : Prop
  radiativeStabilityProved : Prop


def signedMatterCompletionClosed
    (s : SignedMatterCompletionStatus) : Prop :=
  s.positiveSpinTwoKineticTermsDerived /\
  s.ptOddMatterChargeDerived /\
  s.sameSectorAttractionRecovered /\
  s.crossSectorRepulsionRecovered /\
  s.covariantMatterActionDerived /\
  s.weakEquivalencePrincipleAudited /\
  s.combinedBianchiIdentityClosed /\
  s.radiativeStabilityProved

end P0EFTJanusSignedMatterNewtonianLimit
end JanusFormal
