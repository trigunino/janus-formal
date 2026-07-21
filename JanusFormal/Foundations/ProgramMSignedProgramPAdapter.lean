import JanusFormal.Foundations.ProgramMConfigurationObservables
import JanusFormal.Foundations.ProgramMSignedInvolution
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusSignedMatterChargeNewtonianLimit

/-! # MF-PBRIDGE-002: conditional signed adapter from Program M to Program P -/

namespace JanusFormal.ProgramM

open P0EFTJanusSignedMatterChargeNewtonianLimit

universe u v

/-- The exact signed relational data accepted by the narrow Program-P adapter.
No metric, manifold, dimension, throat or action is included. -/
structure SignedProgramPInput (Obj : Type u) (Rel : Type v) where
  system : RelationalSystem Obj Rel
  exchange : Equiv.Perm Obj
  exchange_involutive : Function.Involutive exchange
  exchange_preserves : ∀ q x y,
    system.holds q (exchange x) (exchange y) ↔ system.holds q x y
  charge : Obj → ℝ
  charge_odd : ∀ x, charge (exchange x) = -charge x
  charge_ne_zero : ∀ x, charge x ≠ 0

/-- P's binary charge label extracted from the sign of a nonzero M charge. -/
noncomputable def sectorOfRealCharge (q : ℝ) : JanusCharge :=
  if 0 < q then JanusCharge.positive else JanusCharge.negative

/-- The part of an M charge not contained in P's binary sector label. -/
def chargeMagnitude (q : ℝ) : ℝ := |q|

theorem sectorOfRealCharge_value_mul_magnitude {q : ℝ} (hq : q ≠ 0) :
    chargeValueReal (sectorOfRealCharge q) * chargeMagnitude q = q := by
  by_cases hpos : 0 < q
  · simp [sectorOfRealCharge, chargeMagnitude, hpos, abs_of_pos,
      chargeValueReal, chargeValue]
  · have hneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hq
    simp [sectorOfRealCharge, chargeMagnitude, hpos, abs_of_neg hneg,
      chargeValueReal, chargeValue]

theorem sectorOfRealCharge_neg {q : ℝ} (hq : q ≠ 0) :
    sectorOfRealCharge (-q) = ptCharge (sectorOfRealCharge q) := by
  by_cases hpos : 0 < q
  · have hnpos : ¬ 0 < -q := by linarith
    simp [sectorOfRealCharge, hpos, hnpos, ptCharge]
  · have hneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hq
    have hnpos : 0 < -q := by linarith
    simp [sectorOfRealCharge, hpos, hnpos, ptCharge]

noncomputable def SignedProgramPInput.sector {Obj : Type u} {Rel : Type v}
    (C : SignedProgramPInput Obj Rel) (x : Obj) : JanusCharge :=
  sectorOfRealCharge (C.charge x)

def SignedProgramPInput.magnitude {Obj : Type u} {Rel : Type v}
    (C : SignedProgramPInput Obj Rel) (x : Obj) : ℝ :=
  chargeMagnitude (C.charge x)

/-- M's involution becomes exactly P's binary sector exchange. -/
theorem SignedProgramPInput.sector_exchange {Obj : Type u} {Rel : Type v}
    (C : SignedProgramPInput Obj Rel) (x : Obj) :
    C.sector (C.exchange x) = ptCharge (C.sector x) := by
  rw [SignedProgramPInput.sector, SignedProgramPInput.sector, C.charge_odd]
  exact sectorOfRealCharge_neg (C.charge_ne_zero x)

/-- The real M charge factors exactly into P's sign and a positive magnitude. -/
theorem SignedProgramPInput.charge_factorization {Obj : Type u} {Rel : Type v}
    (C : SignedProgramPInput Obj Rel) (x : Obj) :
    chargeValueReal (C.sector x) * C.magnitude x = C.charge x :=
  sectorOfRealCharge_value_mul_magnitude (C.charge_ne_zero x)

/-- Any external amplitude can be passed to P without identifying charge with
inertial mass: the magnitude is absorbed separately. -/
theorem SignedProgramPInput.source_factorization {Obj : Type u} {Rel : Type v}
    (C : SignedProgramPInput Obj Rel) (x : Obj) (amplitude : ℝ) :
    C.charge x * amplitude =
      chargeValueReal (C.sector x) * (C.magnitude x * amplitude) := by
  rw [← C.charge_factorization]
  ring

end JanusFormal.ProgramM
