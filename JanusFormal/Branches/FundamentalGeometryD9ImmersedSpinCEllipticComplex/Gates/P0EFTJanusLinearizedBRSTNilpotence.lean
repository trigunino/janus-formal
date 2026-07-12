import Mathlib

namespace JanusFormal
namespace P0EFTJanusLinearizedBRSTNilpotence

set_option autoImplicit false

/-- Linearized gauge action.  At the linearized level the ghost differential is
zero and the field differential is the infinitesimal gauge action. -/
structure LinearizedGaugeAction
    (Ghost Field : Type*)
    [Zero Ghost] [Zero Field] where
  act : Ghost → Field
  actZero : act 0 = 0

/-- Linearized BRST state with ghost degree and field degree. -/
@[ext] structure LinearizedBRSTState
    (Ghost Field : Type*) where
  ghost : Ghost
  field : Field

variable
  {Ghost Field : Type*}
  [Zero Ghost] [Zero Field]

/-- Zero BRST state. -/
def zeroBRSTState : LinearizedBRSTState Ghost Field :=
  { ghost := 0
    field := 0 }

/-- Linearized BRST differential `s(c,φ)=(0,Rc)`. -/
def brstDifferential
    (gauge : LinearizedGaugeAction Ghost Field)
    (state : LinearizedBRSTState Ghost Field) :
    LinearizedBRSTState Ghost Field :=
  { ghost := 0
    field := gauge.act state.ghost }

/-- The linearized BRST differential is nilpotent. -/
theorem brst_differential_square_zero
    (gauge : LinearizedGaugeAction Ghost Field)
    (state : LinearizedBRSTState Ghost Field) :
    brstDifferential gauge
        (brstDifferential gauge state) =
      zeroBRSTState := by
  ext
  · rfl
  · exact gauge.actZero

/-- BRST-closed state. -/
def IsBRSTClosed
    (gauge : LinearizedGaugeAction Ghost Field)
    (state : LinearizedBRSTState Ghost Field) : Prop :=
  brstDifferential gauge state = zeroBRSTState

/-- BRST-exact state. -/
def IsBRSTExact
    (gauge : LinearizedGaugeAction Ghost Field)
    (state : LinearizedBRSTState Ghost Field) : Prop :=
  ∃ preimage,
    brstDifferential gauge preimage = state

/-- Every exact state is closed. -/
theorem brst_exact_is_closed
    (gauge : LinearizedGaugeAction Ghost Field)
    (state : LinearizedBRSTState Ghost Field)
    (hExact : IsBRSTExact gauge state) :
    IsBRSTClosed gauge state := by
  rcases hExact with ⟨preimage, rfl⟩
  exact brst_differential_square_zero gauge preimage

/-- Pure gauge field state is BRST exact. -/
theorem pure_gauge_field_is_brst_exact
    (gauge : LinearizedGaugeAction Ghost Field)
    (ghost : Ghost) :
    IsBRSTExact gauge
      { ghost := 0
        field := gauge.act ghost } := by
  exact ⟨{ ghost := ghost, field := 0 }, rfl⟩

/-- BRST closure forces the infinitesimal ghost to stabilize the background. -/
theorem brst_closed_ghost_is_stabilizer
    (gauge : LinearizedGaugeAction Ghost Field)
    (state : LinearizedBRSTState Ghost Field)
    (hClosed : IsBRSTClosed gauge state) :
    gauge.act state.ghost = 0 := by
  have hField := congrArg
    (fun value : LinearizedBRSTState Ghost Field => value.field)
    hClosed
  exact hField

/-- If the gauge action is injective at zero, a BRST-closed state has zero ghost. -/
theorem stabilizer_free_brst_closed_has_zero_ghost
    (gauge : LinearizedGaugeAction Ghost Field)
    (hFree : ∀ ghost, gauge.act ghost = 0 → ghost = 0)
    (state : LinearizedBRSTState Ghost Field)
    (hClosed : IsBRSTClosed gauge state) :
    state.ghost = 0 :=
  hFree state.ghost
    (brst_closed_ghost_is_stabilizer gauge state hClosed)

/--
This is the tangent BRST differential only.  The nonlinear diffeomorphism
algebra, ghost self-interaction, antifields, antibracket and quantum master
equation belong to the full BV theory and are not implied by linear nilpotence.
-/
structure FullBRSTBVPhysicalStatus where
  nonlinearGaugeAlgebraConstructed : Prop
  fieldDependentBracketsControlled : Prop
  nonlinearGhostDifferentialConstructed : Prop
  classicalMasterEquationProved : Prop
  antifieldComplexConstructed : Prop
  gaugeFixingFermionConstructed : Prop
  quantumMeasureConstructed : Prop
  quantumMasterEquationProved : Prop
  anomalyClassVanishingProved : Prop


def fullBRSTBVPhysicalClosure
    (s : FullBRSTBVPhysicalStatus) : Prop :=
  s.nonlinearGaugeAlgebraConstructed /\
  s.fieldDependentBracketsControlled /\
  s.nonlinearGhostDifferentialConstructed /\
  s.classicalMasterEquationProved /\
  s.antifieldComplexConstructed /\
  s.gaugeFixingFermionConstructed /\
  s.quantumMeasureConstructed /\
  s.quantumMasterEquationProved /\
  s.anomalyClassVanishingProved

end P0EFTJanusLinearizedBRSTNilpotence
end JanusFormal
