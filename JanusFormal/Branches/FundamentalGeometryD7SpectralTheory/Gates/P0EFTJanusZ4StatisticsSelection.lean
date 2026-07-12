import Mathlib

namespace JanusFormal
namespace P0EFTJanusZ4StatisticsSelection

set_option autoImplicit false

/-- Bosonic or fermionic statistics. -/
inductive FieldStatistics where
  | boson
  | fermion
  deriving DecidableEq, Repr

/-- Additive phase convention for the central fermionic `Z4`. -/
abbrev PinZ4Phase := ZMod 4

/-- Fermion parity as an additive phase: `0` on bosons and `2` on fermions. -/
def fermionParityPhase : FieldStatistics → PinZ4Phase
  | FieldStatistics.boson => 0
  | FieldStatistics.fermion => 2

/-- Compatibility with a Pin-lifted generator satisfying `g^2=(-1)^F`. -/
def PinZ4Compatible
    (statistics : FieldStatistics)
    (phase : PinZ4Phase) : Prop :=
  phase + phase = fermionParityPhase statistics

instance pinZ4CompatibleDecidable
    (statistics : FieldStatistics)
    (phase : PinZ4Phase) :
    Decidable (PinZ4Compatible statistics phase) := by
  unfold PinZ4Compatible
  infer_instance

/-- Named holonomy phases. -/
def periodicPhase : PinZ4Phase := 0

def quarterPhase : PinZ4Phase := 1

def antiperiodicPhase : PinZ4Phase := 2

def threeQuarterPhase : PinZ4Phase := 3

/-- Periodic and antiperiodic phases are compatible with bosons. -/
@[simp] theorem periodic_phase_is_bosonic :
    PinZ4Compatible FieldStatistics.boson periodicPhase := by
  native_decide

@[simp] theorem antiperiodic_phase_is_bosonic :
    PinZ4Compatible FieldStatistics.boson antiperiodicPhase := by
  native_decide

/-- Quarter phases are incompatible with bosons. -/
@[simp] theorem quarter_phase_is_not_bosonic :
    Not (PinZ4Compatible FieldStatistics.boson quarterPhase) := by
  native_decide

@[simp] theorem three_quarter_phase_is_not_bosonic :
    Not (PinZ4Compatible FieldStatistics.boson threeQuarterPhase) := by
  native_decide

/-- Quarter phases are exactly the natural fermionic phases. -/
@[simp] theorem quarter_phase_is_fermionic :
    PinZ4Compatible FieldStatistics.fermion quarterPhase := by
  native_decide

@[simp] theorem three_quarter_phase_is_fermionic :
    PinZ4Compatible FieldStatistics.fermion threeQuarterPhase := by
  native_decide

/-- Periodic and antiperiodic phases are incompatible with the central fermion parity law. -/
@[simp] theorem periodic_phase_is_not_fermionic :
    Not (PinZ4Compatible FieldStatistics.fermion periodicPhase) := by
  native_decide

@[simp] theorem antiperiodic_phase_is_not_fermionic :
    Not (PinZ4Compatible FieldStatistics.fermion antiperiodicPhase) := by
  native_decide

/-- A directly quantized spin-two excitation is bosonic. -/
structure MassiveSpinTwoQuarterIdentification where
  statistics : FieldStatistics
  spinTwoIsBosonic : statistics = FieldStatistics.boson
  quarterHolonomyCompatibility : PinZ4Compatible statistics quarterPhase

/-- A bosonic massive spin-two tower cannot be the genuine Pin-Z4 quarter sector. -/
theorem massive_spin_two_cannot_be_direct_quarter_sector :
    Not (∃ _s : MassiveSpinTwoQuarterIdentification, True) := by
  rintro ⟨s, _⟩
  have hCompatibility := s.quarterHolonomyCompatibility
  rw [s.spinTwoIsBosonic] at hCompatibility
  exact quarter_phase_is_not_bosonic hCompatibility

/-- Five bosonic polarizations remain bosonic regardless of their multiplicity. -/
structure FivePolarizationQuarterIdentification where
  eachPolarizationStatistics : Fin 5 → FieldStatistics
  allBosonic :
    ∀ index, eachPolarizationStatistics index = FieldStatistics.boson
  allQuarterCompatible :
    ∀ index,
      PinZ4Compatible (eachPolarizationStatistics index) quarterPhase

/-- No set of five ordinary bosonic polarizations can supply five Pin-Z4 quarter towers. -/
theorem five_bosonic_polarizations_cannot_supply_quarter_towers :
    Not (∃ _s : FivePolarizationQuarterIdentification, True) := by
  rintro ⟨s, _⟩
  have hCompatibility := s.allQuarterCompatible 0
  rw [s.allBosonic 0] at hCompatibility
  exact quarter_phase_is_not_bosonic hCompatibility

/--
The arithmetic ratio `1:5` therefore remains viable only if the five quarter
weights come from genuine fermions (or fermionic ghosts with their correct
signs), not directly from the five physical polarizations of a massive
spin-two field.
-/
structure QuarterSectorExitStatus where
  fivePhysicalFermionTowersDerived : Prop
  fermionicGhostSectorDerived : Prop
  internalZ4NotEqualToPinLiftDerived : Prop
  bosonicHalfHolonomyReplacementDerived : Prop
  determinantWeightsAndSignsRecomputed : Prop
  atLeastOneStatisticsConsistentExitDerived : Prop


def quarterSectorStatisticsClosed
    (s : QuarterSectorExitStatus) : Prop :=
  (s.fivePhysicalFermionTowersDerived \/
    s.fermionicGhostSectorDerived \/
    s.internalZ4NotEqualToPinLiftDerived \/
    s.bosonicHalfHolonomyReplacementDerived) /\
  s.determinantWeightsAndSignsRecomputed /\
  s.atLeastOneStatisticsConsistentExitDerived

end P0EFTJanusZ4StatisticsSelection
end JanusFormal
