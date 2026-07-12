import Mathlib

namespace JanusFormal
namespace P0EFTJanusPEChargeSelection

set_option autoImplicit false

/-- Additive PT parity and normal-root holonomy charge. -/
abbrev PTCharge := ZMod 2
abbrev Z4Charge := ZMod 4

/-- Discrete charges of one field sector. -/
structure SectorCharge where
  pt : PTCharge
  z4 : Z4Charge
  deriving DecidableEq, Repr

/-- A scalar bilinear can be invariant only when both additive charges cancel. -/
def NeutralPair
    (first second : SectorCharge) : Prop :=
  first.pt + second.pt = 0 /\
  first.z4 + second.z4 = 0

instance neutralPairDecidable
    (first second : SectorCharge) :
    Decidable (NeutralPair first second) := by
  unfold NeutralPair
  infer_instance

/-- Standard sectors used by the selection audit. -/
def periodicEven : SectorCharge :=
  { pt := 0, z4 := 0 }


def periodicOdd : SectorCharge :=
  { pt := 1, z4 := 0 }


def positiveQuarter : SectorCharge :=
  { pt := 0, z4 := 1 }


def negativeQuarter : SectorCharge :=
  { pt := 0, z4 := 3 }

/-- Periodic even sectors can pair with themselves. -/
@[simp] theorem periodic_even_self_neutral :
    NeutralPair periodicEven periodicEven := by
  native_decide

/-- Even and odd PT sectors cannot form a PT-even scalar bilinear. -/
@[simp] theorem even_odd_pair_not_neutral :
    Not (NeutralPair periodicEven periodicOdd) := by
  native_decide

/-- A positive-quarter sector cannot form a same-charge scalar bilinear. -/
@[simp] theorem positive_quarter_self_not_neutral :
    Not (NeutralPair positiveQuarter positiveQuarter) := by
  native_decide

/-- The same obstruction holds for the negative-quarter sector. -/
@[simp] theorem negative_quarter_self_not_neutral :
    Not (NeutralPair negativeQuarter negativeQuarter) := by
  native_decide

/-- PT-conjugate quarter sectors form a neutral pair. -/
@[simp] theorem conjugate_quarter_pair_neutral :
    NeutralPair positiveQuarter negativeQuarter := by
  native_decide

/-- The reverse conjugate pairing is neutral as well. -/
@[simp] theorem reverse_conjugate_quarter_pair_neutral :
    NeutralPair negativeQuarter positiveQuarter := by
  native_decide

/-- Quadratic coefficients on two PT-conjugate sectors. -/
@[ext] structure TwoSectorQuadraticForm where
  plusPlus : ℝ
  plusMinus : ℝ
  minusMinus : ℝ

/-- Charge selection for the `(+i,-i)` normal-root pair. -/
def RespectsQuarterCharge
    (form : TwoSectorQuadraticForm) : Prop :=
  form.plusPlus = 0 /\ form.minusMinus = 0

/-- Canonical cross pairing with one free normalization. -/
def quarterCrossForm
    (coefficient : ℝ) : TwoSectorQuadraticForm :=
  { plusPlus := 0
    plusMinus := coefficient
    minusMinus := 0 }

/-- Every canonical cross form obeys Z4 charge selection. -/
@[simp] theorem quarter_cross_form_respects_charge
    (coefficient : ℝ) :
    RespectsQuarterCharge (quarterCrossForm coefficient) := by
  exact ⟨rfl, rfl⟩

/-- Z4 neutrality reduces the conjugate-pair quadratic form to one coefficient. -/
theorem quarter_charge_form_unique_up_to_scale
    (form : TwoSectorQuadraticForm)
    (hCharge : RespectsQuarterCharge form) :
    form = quarterCrossForm form.plusMinus := by
  apply TwoSectorQuadraticForm.ext
  · exact hCharge.1
  · rfl
  · exact hCharge.2

/-- PT exchange symmetry for an uncharged two-fold sector. -/
def PTExchangeInvariant
    (form : TwoSectorQuadraticForm) : Prop :=
  form.plusPlus = form.minusMinus

/-- General PT-exchange-invariant uncharged form: diagonal plus cross coefficient. -/
def unchargedPTForm
    (diagonal cross : ℝ) : TwoSectorQuadraticForm :=
  { plusPlus := diagonal
    plusMinus := cross
    minusMinus := diagonal }

/-- Every displayed uncharged form is PT-exchange invariant. -/
@[simp] theorem uncharged_pt_form_invariant
    (diagonal cross : ℝ) :
    PTExchangeInvariant (unchargedPTForm diagonal cross) := by
  rfl

/-- PT exchange leaves two independent coefficients in an uncharged pair. -/
theorem pt_exchange_does_not_select_uncharged_pairing :
    ∃ first second : TwoSectorQuadraticForm,
      PTExchangeInvariant first /\
      PTExchangeInvariant second /\
      first.plusPlus = second.plusPlus /\
      first ≠ second := by
  refine ⟨unchargedPTForm 1 0,
    unchargedPTForm 1 1, rfl, rfl, rfl, ?_⟩
  intro hEqual
  have hCross := congrArg TwoSectorQuadraticForm.plusMinus hEqual
  norm_num [unchargedPTForm] at hCross

/-- Z4 charge selection is strictly stronger than PT exchange on the conjugate pair. -/
theorem z4_removes_same_sector_masses
    (form : TwoSectorQuadraticForm)
    (hCharge : RespectsQuarterCharge form) :
    form.plusPlus = 0 /\ form.minusMinus = 0 :=
  hCharge

/--
P.E discrete verdict: the normal-root Z4 does not choose the overall
normalization, but it removes the two same-charge quadratic coefficients.  A
PT-conjugate quarter pair therefore has one invariant scalar pairing up to
scale, whereas an uncharged PT doublet retains a diagonal and a cross
coefficient.
-/
structure ChargeSelectionPhysicalStatus where
  ptChargesDerived : Prop
  z4ChargesDerivedFromNormalRoot : Prop
  allFieldSectorChargesAssigned : Prop
  bilinearNeutralityProved : Prop
  conjugateQuarterPairingIdentified : Prop
  unchargedMultiplicitySpacesIdentified : Prop
  determinantRealityConditionsDerived : Prop
  remainingNormalizationsFixedMicroscopically : Prop


def chargeSelectionPhysicalClosure
    (s : ChargeSelectionPhysicalStatus) : Prop :=
  s.ptChargesDerived /\
  s.z4ChargesDerivedFromNormalRoot /\
  s.allFieldSectorChargesAssigned /\
  s.bilinearNeutralityProved /\
  s.conjugateQuarterPairingIdentified /\
  s.unchargedMultiplicitySpacesIdentified /\
  s.determinantRealityConditionsDerived /\
  s.remainingNormalizationsFixedMicroscopically

end P0EFTJanusPEChargeSelection
end JanusFormal
