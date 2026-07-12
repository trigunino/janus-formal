import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusZ4StatisticsSelection

namespace JanusFormal
namespace P0EFTJanusSeparatedCentralInternalZ4

set_option autoImplicit false

open P0EFTJanusZ4StatisticsSelection

/-- Product of the central Pin lift and an independent internal order-four symmetry. -/
abbrev ProductZ4Phase := PinZ4Phase × PinZ4Phase

/-- Observable additive circle phase when both connections are present. -/
def totalCirclePhase (phase : ProductZ4Phase) : PinZ4Phase :=
  phase.1 + phase.2

/-- A genuine central Pin-quarter fermion. -/
def centralFermionQuarter : ProductZ4Phase :=
  (quarterPhase, periodicPhase)

/-- A boson with trivial central Pin phase and an internal quarter charge. -/
def internalBosonQuarter : ProductZ4Phase :=
  (periodicPhase, quarterPhase)

/-- The central quarter assignment obeys the fermion-parity square law. -/
@[simp] theorem central_quarter_is_fermion_compatible :
    PinZ4Compatible FieldStatistics.fermion centralFermionQuarter.1 := by
  exact quarter_phase_is_fermionic

/-- The internal-quarter boson obeys the bosonic central Pin square law. -/
@[simp] theorem internal_quarter_is_boson_compatible :
    PinZ4Compatible FieldStatistics.boson internalBosonQuarter.1 := by
  exact periodic_phase_is_bosonic

/-- Both sectors can display the same total quarter circle phase. -/
@[simp] theorem central_fermion_total_phase_is_quarter :
    totalCirclePhase centralFermionQuarter = quarterPhase := by
  native_decide

@[simp] theorem internal_boson_total_phase_is_quarter :
    totalCirclePhase internalBosonQuarter = quarterPhase := by
  native_decide

/-- They are nevertheless different charges in the product symmetry. -/
@[simp] theorem central_and_internal_quarter_charges_are_distinct :
    centralFermionQuarter ≠ internalBosonQuarter := by
  native_decide

/-- Their central Pin components are different. -/
@[simp] theorem central_pin_components_are_distinct :
    centralFermionQuarter.1 ≠ internalBosonQuarter.1 := by
  native_decide

/-- Their internal components are different. -/
@[simp] theorem internal_components_are_distinct :
    centralFermionQuarter.2 ≠ internalBosonQuarter.2 := by
  native_decide

/-- Squaring the central fermionic charge gives central fermion parity only. -/
theorem central_fermion_square_phase :
    centralFermionQuarter.1 + centralFermionQuarter.1 =
      fermionParityPhase FieldStatistics.fermion /\
    centralFermionQuarter.2 + centralFermionQuarter.2 = 0 := by
  native_decide

/-- Squaring the internal bosonic charge gives an internal half-turn, not fermion parity. -/
theorem internal_boson_square_phase :
    internalBosonQuarter.1 + internalBosonQuarter.1 =
      fermionParityPhase FieldStatistics.boson /\
    internalBosonQuarter.2 + internalBosonQuarter.2 = antiperiodicPhase := by
  native_decide

/--
Therefore the fermionic charge/eta sector and the bosonic modulus-stabilization
sector can share a numerical quarter holonomy while remaining mathematically
and statistically distinct.  Identifying them as one `Z4` would conflate
fermion parity with an internal bosonic half-turn.
-/
theorem separated_z4_sector_matrix :
    PinZ4Compatible FieldStatistics.fermion centralFermionQuarter.1 /\
    PinZ4Compatible FieldStatistics.boson internalBosonQuarter.1 /\
    totalCirclePhase centralFermionQuarter = quarterPhase /\
    totalCirclePhase internalBosonQuarter = quarterPhase /\
    centralFermionQuarter ≠ internalBosonQuarter := by
  exact ⟨central_quarter_is_fermion_compatible,
    internal_quarter_is_boson_compatible,
    central_fermion_total_phase_is_quarter,
    internal_boson_total_phase_is_quarter,
    central_and_internal_quarter_charges_are_distinct⟩

/--
Physical promotion requires two independently constructed principal bundles or
one larger product bundle, a proof that their connections couple to the claimed
field sectors, and a no-mixing/no-double-counting theorem for the determinant.
-/
structure SeparatedZ4PhysicalStatus where
  globalCentralPinZ4Constructed : Prop
  independentInternalZ4Constructed : Prop
  productBundleConstructed : Prop
  commutingActionsProved : Prop
  fermionicChargeSectorAssigned : Prop
  bosonicStabilizerSectorAssigned : Prop
  connectionCouplingsDerived : Prop
  mixedAnomaliesCancelled : Prop
  determinantFactorizationProved : Prop
  noSectorConflationOrDoubleCountingProved : Prop


def separatedZ4PhysicalClosure
    (s : SeparatedZ4PhysicalStatus) : Prop :=
  s.globalCentralPinZ4Constructed /\
  s.independentInternalZ4Constructed /\
  s.productBundleConstructed /\
  s.commutingActionsProved /\
  s.fermionicChargeSectorAssigned /\
  s.bosonicStabilizerSectorAssigned /\
  s.connectionCouplingsDerived /\
  s.mixedAnomaliesCancelled /\
  s.determinantFactorizationProved /\
  s.noSectorConflationOrDoubleCountingProved

end P0EFTJanusSeparatedCentralInternalZ4
end JanusFormal
