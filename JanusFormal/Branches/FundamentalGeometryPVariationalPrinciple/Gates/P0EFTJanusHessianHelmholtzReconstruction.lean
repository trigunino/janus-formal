import Mathlib

namespace JanusFormal
namespace P0EFTJanusHessianHelmholtzReconstruction

set_option autoImplicit false

/-- Linear two-field operator, used as a finite-dimensional Helmholtz model. -/
@[ext] structure LinearOperator2 where
  xx : ℝ
  xy : ℝ
  yx : ℝ
  yy : ℝ

/-- Formal self-adjointness in the standard Euclidean pairing. -/
def FormallySelfAdjoint (operator : LinearOperator2) : Prop :=
  operator.xy = operator.yx

/-- Quadratic potential with affine ambiguity. -/
@[ext] structure QuadraticPotential2 where
  xx : ℝ
  xy : ℝ
  yy : ℝ
  linearX : ℝ
  linearY : ℝ
  constant : ℝ

/-- Potential value. -/
def potentialValue
    (potential : QuadraticPotential2)
    (x y : ℝ) : ℝ :=
  potential.xx * x ^ 2 / 2 +
    potential.xy * x * y +
    potential.yy * y ^ 2 / 2 +
    potential.linearX * x +
    potential.linearY * y +
    potential.constant

/-- Gradient components. -/
def gradientX
    (potential : QuadraticPotential2)
    (x y : ℝ) : ℝ :=
  potential.xx * x + potential.xy * y + potential.linearX


def gradientY
    (potential : QuadraticPotential2)
    (x y : ℝ) : ℝ :=
  potential.xy * x + potential.yy * y + potential.linearY

/-- Hessian operator of a quadratic potential. -/
def hessianOperator
    (potential : QuadraticPotential2) : LinearOperator2 :=
  { xx := potential.xx
    xy := potential.xy
    yx := potential.xy
    yy := potential.yy }

/-- Every Hessian is formally self-adjoint. -/
theorem hessian_formally_self_adjoint
    (potential : QuadraticPotential2) :
    FormallySelfAdjoint (hessianOperator potential) := by
  rfl

/-- Canonical PT-even, zero-normalized primitive of a self-adjoint operator. -/
def canonicalPotential
    (operator : LinearOperator2) : QuadraticPotential2 :=
  { xx := operator.xx
    xy := operator.xy
    yy := operator.yy
    linearX := 0
    linearY := 0
    constant := 0 }

/-- A self-adjoint operator is exactly the Hessian of its canonical potential. -/
theorem canonical_potential_hessian
    (operator : LinearOperator2)
    (hSelfAdjoint : FormallySelfAdjoint operator) :
    hessianOperator (canonicalPotential operator) = operator := by
  apply LinearOperator2.ext
  · rfl
  · rfl
  · exact hSelfAdjoint
  · rfl

/-- Finite-dimensional Helmholtz theorem: Hessian realizability iff self-adjointness. -/
theorem helmholtz_realizability_iff
    (operator : LinearOperator2) :
    (∃ potential : QuadraticPotential2,
      hessianOperator potential = operator) ↔
      FormallySelfAdjoint operator := by
  constructor
  · rintro ⟨potential, rfl⟩
    exact hessian_formally_self_adjoint potential
  · intro hSelfAdjoint
    exact ⟨canonicalPotential operator,
      canonical_potential_hessian operator hSelfAdjoint⟩

/-- A nonsymmetric operator cannot be a Hessian. -/
theorem nonsymmetric_operator_is_not_variational
    (operator : LinearOperator2)
    (hNonsymmetric : operator.xy ≠ operator.yx) :
    Not (∃ potential : QuadraticPotential2,
      hessianOperator potential = operator) := by
  intro hPotential
  have hSelfAdjoint :=
    (helmholtz_realizability_iff operator).mp hPotential
  exact hNonsymmetric hSelfAdjoint

/-- Equal Hessians imply affine difference of potentials. -/
theorem equal_hessian_difference_affine
    (first second : QuadraticPotential2)
    (hHessian : hessianOperator first = hessianOperator second)
    (x y : ℝ) :
    potentialValue first x y - potentialValue second x y =
      (first.linearX - second.linearX) * x +
      (first.linearY - second.linearY) * y +
      (first.constant - second.constant) := by
  have hXX := congrArg LinearOperator2.xx hHessian
  have hXY := congrArg LinearOperator2.xy hHessian
  have hYY := congrArg LinearOperator2.yy hHessian
  unfold hessianOperator at hXX hXY hYY
  unfold potentialValue
  rw [hXX, hXY, hYY]
  ring

/-- Hessian data alone admit distinct affine completions. -/
theorem same_hessian_has_distinct_affine_completions
    (operator : LinearOperator2)
    (hSelfAdjoint : FormallySelfAdjoint operator) :
    ∃ first second : QuadraticPotential2,
      hessianOperator first = operator /\
      hessianOperator second = operator /\
      first ≠ second := by
  let first := canonicalPotential operator
  let second : QuadraticPotential2 :=
    { xx := operator.xx
      xy := operator.xy
      yy := operator.yy
      linearX := 1
      linearY := 0
      constant := 0 }
  refine ⟨first, second, ?_, ?_, ?_⟩
  · exact canonical_potential_hessian operator hSelfAdjoint
  · apply LinearOperator2.ext
    · rfl
    · rfl
    · exact hSelfAdjoint
    · rfl
  · intro hEqual
    have hLinear := congrArg QuadraticPotential2.linearX hEqual
    norm_num [first, second, canonicalPotential] at hLinear

/-- Coefficient-level PT symmetry around the origin. -/
def PTEven (potential : QuadraticPotential2) : Prop :=
  potential.linearX = 0 /\ potential.linearY = 0

/-- Reference normalization. -/
def ZeroNormalized (potential : QuadraticPotential2) : Prop :=
  potential.constant = 0

/-- Fixed Hessian plus PT symmetry and one normalization reconstruct the quadratic action uniquely. -/
theorem pt_normalized_hessian_reconstruction_unique
    (operator : LinearOperator2)
    (hSelfAdjoint : FormallySelfAdjoint operator)
    (potential : QuadraticPotential2)
    (hHessian : hessianOperator potential = operator)
    (hPT : PTEven potential)
    (hNormalized : ZeroNormalized potential) :
    potential = canonicalPotential operator := by
  have hXX := congrArg LinearOperator2.xx hHessian
  have hXY := congrArg LinearOperator2.xy hHessian
  have hYY := congrArg LinearOperator2.yy hHessian
  apply QuadraticPotential2.ext
  · exact hXX
  · exact hXY
  · exact hYY
  · simpa [canonicalPotential] using hPT.1
  · simpa [canonicalPotential] using hPT.2
  · simpa [canonicalPotential, ZeroNormalized] using hNormalized

/-- The canonical potential is PT-even and normalized. -/
theorem canonical_potential_pt_normalized
    (operator : LinearOperator2) :
    PTEven (canonicalPotential operator) /\
      ZeroNormalized (canonicalPotential operator) := by
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- Unique-existence theorem for the quadratic inverse problem. -/
theorem pt_normalized_reconstruction_unique_existence
    (operator : LinearOperator2)
    (hSelfAdjoint : FormallySelfAdjoint operator) :
    ∃! potential : QuadraticPotential2,
      hessianOperator potential = operator /\
      PTEven potential /\
      ZeroNormalized potential := by
  refine ⟨canonicalPotential operator, ?_, ?_⟩
  · exact ⟨canonical_potential_hessian operator hSelfAdjoint,
      (canonical_potential_pt_normalized operator).1,
      (canonical_potential_pt_normalized operator).2⟩
  · intro potential hProperties
    exact pt_normalized_hessian_reconstruction_unique
      operator hSelfAdjoint potential
      hProperties.1 hProperties.2.1 hProperties.2.2

/--
Nonlinear/local-field-theory Helmholtz contract.  Formal self-adjointness is
necessary but generally not sufficient globally: one must also kill the
variational-bicomplex obstruction and control boundary/null Lagrangians.
-/
structure LocalHelmholtzReconstructionStatus where
  localEulerLagrangeOperatorSpecified : Prop
  linearizationFormallySelfAdjoint : Prop
  gaugeNoetherIdentitiesCompatible : Prop
  helmholtzConditionsProved : Prop
  variationalBicomplexClassVanishing : Prop
  boundaryTermsClassified : Prop
  nullLagrangiansQuotiented : Prop
  localLagrangianReconstructed : Prop
  ptAndDiscreteSymmetriesImposed : Prop
  normalizationFixed : Prop
  finiteCountertermsFixedMicroscopically : Prop
  globalActionClassReconstructed : Prop


def localHelmholtzReconstructionClosed
    (s : LocalHelmholtzReconstructionStatus) : Prop :=
  s.localEulerLagrangeOperatorSpecified /\
  s.linearizationFormallySelfAdjoint /\
  s.gaugeNoetherIdentitiesCompatible /\
  s.helmholtzConditionsProved /\
  s.variationalBicomplexClassVanishing /\
  s.boundaryTermsClassified /\
  s.nullLagrangiansQuotiented /\
  s.localLagrangianReconstructed /\
  s.ptAndDiscreteSymmetriesImposed /\
  s.normalizationFixed /\
  s.finiteCountertermsFixedMicroscopically /\
  s.globalActionClassReconstructed

/-- Missing formal self-adjointness blocks variational reconstruction. -/
theorem missing_self_adjointness_blocks_helmholtz_reconstruction
    (s : LocalHelmholtzReconstructionStatus)
    (hMissing : Not s.linearizationFormallySelfAdjoint) :
    Not (localHelmholtzReconstructionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/-- Missing variational cohomology control blocks a global action. -/
theorem missing_variational_cohomology_blocks_global_action
    (s : LocalHelmholtzReconstructionStatus)
    (hMissing : Not s.variationalBicomplexClassVanishing) :
    Not (localHelmholtzReconstructionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end P0EFTJanusHessianHelmholtzReconstruction
end JanusFormal
