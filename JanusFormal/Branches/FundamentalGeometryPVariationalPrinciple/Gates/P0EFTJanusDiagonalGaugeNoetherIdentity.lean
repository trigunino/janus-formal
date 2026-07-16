import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonlinearGaugeFlowNoether

namespace JanusFormal
namespace P0EFTJanusDiagonalGaugeNoetherIdentity

set_option autoImplicit false

noncomputable section

open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusNonlinearGaugeFlowNoether

universe u v w

variable {Configuration : Type u} {GaugeParameter : Type v}
variable [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
variable [NormedAddCommGroup GaugeParameter] [NormedSpace ℝ GaugeParameter]

/-- A supplied, possibly field-dependent, infinitesimal diagonal gauge
generator.  Linearity is required only in the gauge parameter at each field. -/
abbrev DiagonalGaugeGenerator :=
  Configuration → GaugeParameter →L[ℝ] Configuration

/-- Frozen infinitesimal gauge line through one configuration.  It records
first-order gauge data and is not assumed to integrate to a complete flow. -/
def gaugeLine
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) (parameter : GaugeParameter) (t : ℝ) :
    Configuration :=
  q + t • generator q parameter

theorem gaugeLine_hasDerivAt
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) (parameter : GaugeParameter) :
    HasDerivAt (gaugeLine generator q parameter)
      (generator q parameter) 0 := by
  have hConstant : HasDerivAt (fun _ : ℝ => q) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) (c := q)
  have hLinear := (hasDerivAt_id (0 : ℝ)).smul_const
    (generator q parameter)
  have hSum := hConstant.add hLinear
  change HasDerivAt (fun t : ℝ => q + t • generator q parameter)
    (generator q parameter) 0
  exact hSum.congr_deriv (by simp)

/-- Infinitesimal invariance means that the actual action has zero derivative
along every supplied diagonal gauge line. -/
def InfinitesimallyDiagonalGaugeInvariantAt
    (action : Configuration → ℝ)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) : Prop :=
  ∀ parameter, HasDerivAt
    (fun t => action (gaugeLine generator q parameter t)) 0 0

def InfinitesimallyDiagonalGaugeInvariant
    (action : Configuration → ℝ)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter)) :
    Prop :=
  ∀ q, InfinitesimallyDiagonalGaugeInvariantAt action generator q

/-- Algebraic formal-adjoint constraint `K(q)ᵀ E(q)`: pull the Euler
covector back to gauge-parameter space.  No inner product or Riesz
identification is assumed. -/
def formalAdjointEulerConstraint
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) : GaugeParameter →L[ℝ] ℝ :=
  (euler q).comp (generator q)

/-- Bianchi-type annihilation at one field: the actual Euler covector kills
the whole image of the supplied diagonal gauge generator. -/
def EulerBianchiAnnihilationAt
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) : Prop :=
  ∀ parameter, euler q (generator q parameter) = 0

def EulerBianchiAnnihilation
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter)) :
    Prop :=
  ∀ q, EulerBianchiAnnihilationAt euler generator q

theorem action_gaugeLine_hasDerivAt
    (action : Configuration → ℝ)
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) (parameter : GaugeParameter)
    (hGradient : HasFDerivAt action (euler q) q) :
    HasDerivAt (fun t => action (gaugeLine generator q parameter t))
      (euler q (generator q parameter)) 0 := by
  have hComp := hGradient.comp_hasDerivAt_of_eq 0
    (gaugeLine_hasDerivAt generator q parameter)
    (by simp [gaugeLine])
  simpa [gaugeLine, Function.comp_def] using hComp

/-- Pointwise Noether equivalence using the genuine action derivative. -/
theorem infinitesimal_invariance_at_iff_euler_bianchi_annihilation
    (action : Configuration → ℝ)
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration)
    (hGradient : HasFDerivAt action (euler q) q) :
    InfinitesimallyDiagonalGaugeInvariantAt action generator q ↔
      EulerBianchiAnnihilationAt euler generator q := by
  constructor
  · intro hInvariant parameter
    exact (action_gaugeLine_hasDerivAt action euler generator q parameter
      hGradient).unique (hInvariant parameter)
  · intro hBianchi parameter
    exact (action_gaugeLine_hasDerivAt action euler generator q parameter
      hGradient).congr_deriv (hBianchi parameter)

/-- Global nonlinear, field-dependent infinitesimal Noether equivalence. -/
theorem infinitesimal_invariance_iff_euler_bianchi_annihilation
    (action : Configuration → ℝ)
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (hGradient : ∀ q, HasFDerivAt action (euler q) q) :
    InfinitesimallyDiagonalGaugeInvariant action generator ↔
      EulerBianchiAnnihilation euler generator := by
  constructor <;> intro h q
  · exact (infinitesimal_invariance_at_iff_euler_bianchi_annihilation
      action euler generator q (hGradient q)).1 (h q)
  · exact (infinitesimal_invariance_at_iff_euler_bianchi_annihilation
      action euler generator q (hGradient q)).2 (h q)

/-- The annihilation statement is exactly the vanishing formal-adjoint
constraint, not merely pointwise suggestive notation. -/
theorem euler_bianchi_annihilation_at_iff_formalAdjoint_constraint
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (q : Configuration) :
    EulerBianchiAnnihilationAt euler generator q ↔
      formalAdjointEulerConstraint euler generator q = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro parameter
    exact h parameter
  · intro h parameter
    have hApply := congrArg
      (fun constraint : GaugeParameter →L[ℝ] ℝ => constraint parameter) h
    simpa [formalAdjointEulerConstraint] using hApply

/-- Strongest packaged identity: infinitesimal invariance of an action with
its actual derivative is equivalent to `Kᵀ E = 0` at every field. -/
theorem infinitesimal_invariance_iff_formalAdjoint_bianchi_constraint
    (action : Configuration → ℝ)
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (hGradient : ∀ q, HasFDerivAt action (euler q) q) :
    InfinitesimallyDiagonalGaugeInvariant action generator ↔
      ∀ q, formalAdjointEulerConstraint euler generator q = 0 := by
  rw [infinitesimal_invariance_iff_euler_bianchi_annihilation
    action euler generator hGradient]
  constructor <;> intro h q
  · exact (euler_bianchi_annihilation_at_iff_formalAdjoint_constraint
      euler generator q).1 (h q)
  · exact (euler_bianchi_annihilation_at_iff_formalAdjoint_constraint
      euler generator q).2 (h q)

/-- Restrict a field-dependent gauge generator along a linear map of gauge
parameters. -/
def reparameterizedDiagonalGaugeGenerator
    {ReducedParameter : Type w}
    [NormedAddCommGroup ReducedParameter] [NormedSpace ℝ ReducedParameter]
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (parameterMap : ReducedParameter →L[ℝ] GaugeParameter) :
    DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := ReducedParameter) :=
  fun q => (generator q).comp parameterMap

/-- Pulling back the formal-adjoint Euler constraint agrees exactly with
reparameterizing the gauge generator. -/
theorem formalAdjointEulerConstraint_reparameterized
    {ReducedParameter : Type w}
    [NormedAddCommGroup ReducedParameter] [NormedSpace ℝ ReducedParameter]
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (parameterMap : ReducedParameter →L[ℝ] GaugeParameter)
    (q : Configuration) :
    formalAdjointEulerConstraint euler
        (reparameterizedDiagonalGaugeGenerator generator parameterMap) q =
      (formalAdjointEulerConstraint euler generator q).comp parameterMap := by
  rfl

/-- Infinitesimal invariance is preserved when the allowed gauge parameters
are restricted by a continuous linear map. -/
theorem infinitesimal_invariance_reparameterized
    {ReducedParameter : Type w}
    [NormedAddCommGroup ReducedParameter] [NormedSpace ℝ ReducedParameter]
    (action : Configuration → ℝ)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (parameterMap : ReducedParameter →L[ℝ] GaugeParameter)
    (hInvariant : InfinitesimallyDiagonalGaugeInvariant action generator) :
    InfinitesimallyDiagonalGaugeInvariant action
      (reparameterizedDiagonalGaugeGenerator generator parameterMap) := by
  intro q parameter
  simpa [reparameterizedDiagonalGaugeGenerator, gaugeLine] using
    hInvariant q (parameterMap parameter)

/-- A vanishing formal-adjoint constraint remains zero after an exact
reparameterization of the gauge generator. -/
theorem formalAdjoint_constraint_reparameterized_of_constraint
    {ReducedParameter : Type w}
    [NormedAddCommGroup ReducedParameter] [NormedSpace ℝ ReducedParameter]
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (parameterMap : ReducedParameter →L[ℝ] GaugeParameter)
    (q : Configuration)
    (hConstraint : formalAdjointEulerConstraint euler generator q = 0) :
    formalAdjointEulerConstraint euler
        (reparameterizedDiagonalGaugeGenerator generator parameterMap) q = 0 := by
  rw [formalAdjointEulerConstraint_reparameterized, hConstraint]
  rfl

/-- Constraint closure under a supplied reduction of gauge parameters. -/
theorem formalAdjoint_constraint_closed_under_parameter_map
    {ReducedParameter : Type w}
    [NormedAddCommGroup ReducedParameter] [NormedSpace ℝ ReducedParameter]
    (euler : EulerOneForm Configuration)
    (generator : DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := GaugeParameter))
    (parameterMap : ReducedParameter →L[ℝ] GaugeParameter)
    (q : Configuration)
    (hConstraint : formalAdjointEulerConstraint euler generator q = 0) :
    (formalAdjointEulerConstraint euler generator q).comp parameterMap = 0 := by
  rw [hConstraint]
  rfl

/-- A complete one-parameter gauge flow supplies a diagonal infinitesimal
generator by scalar multiplication of its velocity field. -/
def completeFlowDiagonalGaugeGenerator
    (flow : CompleteGaugeFlow Configuration) :
    DiagonalGaugeGenerator
      (Configuration := Configuration) (GaugeParameter := ℝ) :=
  fun q => ContinuousLinearMap.smulRight
    (ContinuousLinearMap.id ℝ ℝ) (flow.generator q)

@[simp]
theorem completeFlowDiagonalGaugeGenerator_apply
    (flow : CompleteGaugeFlow Configuration)
    (q : Configuration) (scalar : ℝ) :
    completeFlowDiagonalGaugeGenerator flow q scalar =
      scalar • flow.generator q :=
  rfl

/-- The diagonal Bianchi identity for the generator induced by a complete
flow is exactly annihilation of that flow's velocity field. -/
theorem eulerBianchiAnnihilation_completeFlow_iff
    (flow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration) :
    EulerBianchiAnnihilation euler
        (completeFlowDiagonalGaugeGenerator flow) ↔
      EulerAnnihilatesGenerator flow euler := by
  constructor
  · intro h q
    simpa using h q 1
  · intro h q scalar
    simp [completeFlowDiagonalGaugeGenerator, h q]

/-- For an action with its actual Euler derivative, invariance under a
complete gauge flow is equivalent to invariance along every frozen scalar
multiple of the same infinitesimal generator. -/
theorem flowGaugeInvariant_iff_infinitesimallyDiagonalGaugeInvariant
    (flow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (action : Configuration → ℝ)
    (hGradient : ∀ q, HasFDerivAt action (euler q) q) :
    FlowGaugeInvariant flow action ↔
      InfinitesimallyDiagonalGaugeInvariant action
        (completeFlowDiagonalGaugeGenerator flow) := by
  rw [flow_gauge_invariant_iff_euler_annihilates_generator
      flow euler action hGradient,
    infinitesimal_invariance_iff_euler_bianchi_annihilation
      action euler (completeFlowDiagonalGaugeGenerator flow) hGradient,
    eulerBianchiAnnihilation_completeFlow_iff]

/-- On a scalar flow parameter, the formal-adjoint constraint is scalar
multiplication by the Euler pairing with the flow generator. -/
@[simp]
theorem formalAdjointEulerConstraint_completeFlow_apply
    (flow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (q : Configuration) (scalar : ℝ) :
    formalAdjointEulerConstraint euler
        (completeFlowDiagonalGaugeGenerator flow) q scalar =
      scalar * euler q (flow.generator q) := by
  simp [formalAdjointEulerConstraint, completeFlowDiagonalGaugeGenerator]

/-- Vanishing of the complete-flow formal-adjoint constraint is exactly the
nonlinear Euler annihilation identity for the same supplied flow. -/
theorem completeFlow_formalAdjoint_constraint_iff
    (flow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration) :
    (∀ q, formalAdjointEulerConstraint euler
        (completeFlowDiagonalGaugeGenerator flow) q = 0) ↔
      EulerAnnihilatesGenerator flow euler := by
  constructor
  · intro hConstraint q
    have hAtOne := congrArg
      (fun constraint : ℝ →L[ℝ] ℝ => constraint 1) (hConstraint q)
    simpa using hAtOne
  · intro hAnnihilates q
    apply ContinuousLinearMap.ext
    intro scalar
    simp [hAnnihilates q]

/-- For an action with its actual Euler derivative, invariance under the
complete flow is equivalent directly to the vanishing constraint `Rᵀ E = 0`
for the scalar generator induced by that same flow. -/
theorem flowGaugeInvariant_iff_completeFlow_formalAdjoint_constraint
    (flow : CompleteGaugeFlow Configuration)
    (euler : EulerOneForm Configuration)
    (action : Configuration → ℝ)
    (hGradient : ∀ q, HasFDerivAt action (euler q) q) :
    FlowGaugeInvariant flow action ↔
      ∀ q, formalAdjointEulerConstraint euler
        (completeFlowDiagonalGaugeGenerator flow) q = 0 := by
  rw [flowGaugeInvariant_iff_infinitesimallyDiagonalGaugeInvariant
      flow euler action hGradient,
    infinitesimal_invariance_iff_formalAdjoint_bianchi_constraint
      action euler (completeFlowDiagonalGaugeGenerator flow) hGradient]

/-- A constant action and cancelling sector Euler contributions provide an
exact counterexample to splitting a combined Noether identity. -/
def counterexampleAction : ℝ → ℝ := fun _ => 0

def counterexampleTotalEuler : EulerOneForm ℝ := fun _ => 0

def counterexamplePlusEuler : EulerOneForm ℝ :=
  fun _ => ContinuousLinearMap.id ℝ ℝ

def counterexampleMinusEuler : EulerOneForm ℝ :=
  fun _ => -(ContinuousLinearMap.id ℝ ℝ)

def counterexampleDiagonalGenerator :
    DiagonalGaugeGenerator (Configuration := ℝ) (GaugeParameter := ℝ) :=
  fun _ => ContinuousLinearMap.id ℝ ℝ

theorem counterexample_actual_gradient
    (q : ℝ) :
    HasFDerivAt counterexampleAction (counterexampleTotalEuler q) q := by
  change HasFDerivAt (fun _ : ℝ => 0) (0 : ℝ →L[ℝ] ℝ) q
  exact hasFDerivAt_const (x := q) (c := (0 : ℝ))

theorem counterexample_euler_decomposition
    (q : ℝ) :
    counterexampleTotalEuler q =
      counterexamplePlusEuler q + counterexampleMinusEuler q := by
  simp [counterexampleTotalEuler, counterexamplePlusEuler,
    counterexampleMinusEuler]

theorem counterexample_combined_bianchi_identity :
    EulerBianchiAnnihilation counterexampleTotalEuler
      counterexampleDiagonalGenerator := by
  intro q parameter
  rfl

theorem counterexample_plus_identity_fails :
    ¬ EulerBianchiAnnihilation counterexamplePlusEuler
      counterexampleDiagonalGenerator := by
  intro h
  have hOne := h 0 1
  norm_num [counterexamplePlusEuler, counterexampleDiagonalGenerator] at hOne

theorem counterexample_minus_identity_fails :
    ¬ EulerBianchiAnnihilation counterexampleMinusEuler
      counterexampleDiagonalGenerator := by
  intro h
  have hOne := h 0 1
  norm_num [counterexampleMinusEuler, counterexampleDiagonalGenerator] at hOne

/-- Combined diagonal gauge invariance and its Bianchi-type identity do not
imply separate identities for an arbitrary decomposition into two sectors. -/
theorem combined_identity_does_not_imply_separate_sector_identities :
    ∃ (action : ℝ → ℝ)
        (totalEuler plusEuler minusEuler : EulerOneForm ℝ)
        (generator : DiagonalGaugeGenerator
          (Configuration := ℝ) (GaugeParameter := ℝ)),
      (∀ q, HasFDerivAt action (totalEuler q) q) ∧
      (∀ q, totalEuler q = plusEuler q + minusEuler q) ∧
      InfinitesimallyDiagonalGaugeInvariant action generator ∧
      EulerBianchiAnnihilation totalEuler generator ∧
      ¬ EulerBianchiAnnihilation plusEuler generator ∧
      ¬ EulerBianchiAnnihilation minusEuler generator := by
  refine ⟨counterexampleAction, counterexampleTotalEuler,
    counterexamplePlusEuler, counterexampleMinusEuler,
    counterexampleDiagonalGenerator, counterexample_actual_gradient,
    counterexample_euler_decomposition, ?_,
    counterexample_combined_bianchi_identity,
    counterexample_plus_identity_fails,
    counterexample_minus_identity_fails⟩
  exact (infinitesimal_invariance_iff_euler_bianchi_annihilation
    counterexampleAction counterexampleTotalEuler
    counterexampleDiagonalGenerator counterexample_actual_gradient).2
      counterexample_combined_bianchi_identity

/- All generators and identities above are supplied normed-space data.  The
term "Bianchi-type" denotes only the formal Noether annihilation `Kᵀ E = 0`;
no Janus diffeomorphism generator, covariant divergence, curvature identity,
or spacetime constraint algebra is constructed here. -/

end

end P0EFTJanusDiagonalGaugeNoetherIdentity
end JanusFormal
