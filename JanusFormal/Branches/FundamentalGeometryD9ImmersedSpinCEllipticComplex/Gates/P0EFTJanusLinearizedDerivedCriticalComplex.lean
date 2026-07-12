import Mathlib

namespace JanusFormal
namespace P0EFTJanusLinearizedDerivedCriticalComplex

set_option autoImplicit false

/--
Four-term linearized critical complex

`gauge parameters -> fields -> equations -> Noether identities`.

It is the algebraic tangent complex of a gauge-invariant derived critical locus.
The two square-zero laws are precisely linearized gauge invariance and the
Noether identity.
-/
structure LinearizedCriticalComplex
    (Gauge Field Equation Identity : Type*)
    [Zero Gauge] [Zero Field] [Zero Equation] [Zero Identity] where
  gaugeAction : Gauge → Field
  hessian : Field → Equation
  noether : Equation → Identity
  gaugeActionZero : gaugeAction 0 = 0
  hessianZero : hessian 0 = 0
  noetherZero : noether 0 = 0
  hessianGaugeZero : ∀ gauge, hessian (gaugeAction gauge) = 0
  noetherHessianZero : ∀ field, noether (hessian field) = 0

variable
  {Gauge Field Equation Identity : Type*}
  [Zero Gauge] [Zero Field] [Zero Equation] [Zero Identity]

/-- Infinitesimal automorphisms of the background. -/
def IsStabilizer
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (gauge : Gauge) : Prop :=
  complex.gaugeAction gauge = 0

/-- Linearized solutions of the field equations. -/
def IsLinearizedSolution
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (field : Field) : Prop :=
  complex.hessian field = 0

/-- Pure-gauge field variation. -/
def IsPureGauge
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (field : Field) : Prop :=
  ∃ gauge, complex.gaugeAction gauge = field

/-- Equation satisfying the linearized Noether compatibility condition. -/
def IsNoetherCompatible
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (equation : Equation) : Prop :=
  complex.noether equation = 0

/-- Equation lying in the Hessian image. -/
def IsHessianImage
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (equation : Equation) : Prop :=
  ∃ field, complex.hessian field = equation

/-- Every pure-gauge variation is a linearized solution. -/
theorem pure_gauge_is_linearized_solution
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (field : Field)
    (hGauge : IsPureGauge complex field) :
    IsLinearizedSolution complex field := by
  rcases hGauge with ⟨gauge, rfl⟩
  exact complex.hessianGaugeZero gauge

/-- Every Hessian equation satisfies the Noether identity. -/
theorem hessian_image_is_noether_compatible
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (equation : Equation)
    (hImage : IsHessianImage complex equation) :
    IsNoetherCompatible complex equation := by
  rcases hImage with ⟨field, rfl⟩
  exact complex.noetherHessianZero field

/-- Vanishing degree-minus-one cohomology: no infinitesimal stabilizers. -/
def StabilizerFree
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity) : Prop :=
  ∀ gauge, IsStabilizer complex gauge → gauge = 0

/-- Vanishing degree-zero cohomology: all linearized solutions are pure gauge. -/
def FormallyRigid
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity) : Prop :=
  ∀ field, IsLinearizedSolution complex field → IsPureGauge complex field

/-- Vanishing obstruction cohomology: every Noether-compatible source is a Hessian image. -/
def Unobstructed
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity) : Prop :=
  ∀ equation,
    IsNoetherCompatible complex equation →
      IsHessianImage complex equation

/-- One-loop isolated background in the finite algebraic sense. -/
def OneLoopIsolated
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity) : Prop :=
  StabilizerFree complex /\
  FormallyRigid complex /\
  Unobstructed complex

/-- One-loop isolation implies absence of stabilizers. -/
theorem one_loop_isolated_stabilizer_free
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (hIsolated : OneLoopIsolated complex) :
    StabilizerFree complex :=
  hIsolated.1

/-- One-loop isolation implies formal rigidity modulo gauge. -/
theorem one_loop_isolated_formally_rigid
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (hIsolated : OneLoopIsolated complex) :
    FormallyRigid complex :=
  hIsolated.2.1

/-- One-loop isolation implies unobstructedness. -/
theorem one_loop_isolated_unobstructed
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (hIsolated : OneLoopIsolated complex) :
    Unobstructed complex :=
  hIsolated.2.2

/-- Missing any one cohomological condition blocks one-loop isolation. -/
theorem missing_rigidity_blocks_isolation
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (hMissing : Not (FormallyRigid complex)) :
    Not (OneLoopIsolated complex) := by
  intro hIsolated
  exact hMissing hIsolated.2.1

/-- Missing obstruction control also blocks isolation. -/
theorem missing_unobstructedness_blocks_isolation
    (complex : LinearizedCriticalComplex Gauge Field Equation Identity)
    (hMissing : Not (Unobstructed complex)) :
    Not (OneLoopIsolated complex) := by
  intro hIsolated
  exact hMissing hIsolated.2.2

/--
Physical/global closure status.  The abstract complex becomes the tangent
complex of the Janus theory only after the global bundles, action, gauge group,
Hessian, Noether map and Fredholm domains are actually constructed.
-/
structure DerivedCriticalPhysicalStatus where
  configurationGroupoidConstructed : Prop
  gaugeLieAlgebraConstructed : Prop
  tangentFieldSpaceConstructed : Prop
  invariantActionConstructed : Prop
  backgroundCriticalPointProved : Prop
  hessianConstructed : Prop
  noetherOperatorConstructed : Prop
  squareZeroLawsProved : Prop
  ellipticGaugeFixingConstructed : Prop
  stabilizerCohomologyComputed : Prop
  deformationCohomologyComputed : Prop
  obstructionCohomologyComputed : Prop
  determinantLineConstructed : Prop


def derivedCriticalPhysicalClosure
    (s : DerivedCriticalPhysicalStatus) : Prop :=
  s.configurationGroupoidConstructed /\
  s.gaugeLieAlgebraConstructed /\
  s.tangentFieldSpaceConstructed /\
  s.invariantActionConstructed /\
  s.backgroundCriticalPointProved /\
  s.hessianConstructed /\
  s.noetherOperatorConstructed /\
  s.squareZeroLawsProved /\
  s.ellipticGaugeFixingConstructed /\
  s.stabilizerCohomologyComputed /\
  s.deformationCohomologyComputed /\
  s.obstructionCohomologyComputed /\
  s.determinantLineConstructed

end P0EFTJanusLinearizedDerivedCriticalComplex
end JanusFormal
