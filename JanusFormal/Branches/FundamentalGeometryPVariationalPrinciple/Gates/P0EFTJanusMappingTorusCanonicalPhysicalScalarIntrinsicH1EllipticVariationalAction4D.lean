import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1EllipticOperator4D

/-!
# Variational action of the intrinsic physical H1 elliptic operator

On the dense domain of the canonical intrinsic elliptic operator `A`, define

`S_f(u) = 1/2 ⟪A u, u⟫ - ⟪f, u⟫`.

This file proves that its first variation is `⟪A u - f, v⟫`, its Hessian is
the symmetric form `⟪A v, w⟫`, stationarity is equivalent to the strong source
equation, and the compact response applied to `f` is the unique minimizer.
The action is exactly the pullback of the previously constructed graph-H1
action through the canonical regularity map.

This is the action of the intrinsic elliptic graph-energy sector.  It is not
identified here with the nonlinear Lorentzian Janus action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1EllipticVariationalAction4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped InnerProduct LinearPMap
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1EllipticOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev PhysicalHilbertH1 :=
  CanonicalPhysicalScalarHilbertH1 period hPeriod

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

private abbrev bulkInclusion :=
  canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod

private abbrev sourceRepresenter :=
  canonicalPhysicalScalarIntrinsicH1SourceRepresenter period hPeriod

private abbrev ellipticOperator :=
  canonicalPhysicalScalarIntrinsicH1EllipticOperator period hPeriod

private abbrev regularityMap :=
  canonicalPhysicalScalarIntrinsicH1EllipticRegularityMap period hPeriod

local instance intrinsicEllipticActionPhysicalH1CompleteSpace :
    CompleteSpace (PhysicalHilbertH1 period hPeriod) :=
  canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod

/-- Unsourced quadratic action of the intrinsic elliptic operator. -/
def canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
    (field : (ellipticOperator period hPeriod).domain) : Real :=
  (1 / 2 : Real) *
    inner Real
      (ellipticOperator period hPeriod field)
      (field : BulkL2 period hPeriod)

/-- Canonical sourced action on the dense elliptic domain. -/
def canonicalPhysicalScalarIntrinsicH1EllipticSourceAction
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain) : Real :=
  canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
      period hPeriod field -
    inner Real source (field : BulkL2 period hPeriod)

/-- First variation of the sourced elliptic action. -/
def canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
    (source : BulkL2 period hPeriod)
    (field variation : (ellipticOperator period hPeriod).domain) : Real :=
  inner Real
    (ellipticOperator period hPeriod field - source)
    (variation : BulkL2 period hPeriod)

/-- Bilinear Hessian of the sourced elliptic action. -/
def canonicalPhysicalScalarIntrinsicH1EllipticHessian
    (first second : (ellipticOperator period hPeriod).domain) : Real :=
  inner Real
    (ellipticOperator period hPeriod first)
    (second : BulkL2 period hPeriod)

/-- The operator quadratic action is half the squared graph-H1 regularity
norm. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction_eq
    (field : (ellipticOperator period hPeriod).domain) :
    canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
        period hPeriod field =
      (1 / 2 : Real) * ‖regularityMap period hPeriod field‖ ^ 2 := by
  unfold canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
  rw [canonicalPhysicalScalarIntrinsicH1EllipticOperator_energy_identity]
  rfl

/-- The operator-domain action is exactly the graph-H1 action of its
regularity representative. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_eq_graphH1
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceAction
        period hPeriod source field =
      canonicalPhysicalScalarIntrinsicH1SourceAction period hPeriod source
        (regularityMap period hPeriod field) := by
  unfold canonicalPhysicalScalarIntrinsicH1EllipticSourceAction
    canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
    canonicalPhysicalScalarIntrinsicH1SourceAction
  rw [canonicalPhysicalScalarIntrinsicH1EllipticOperator_energy_identity,
    canonicalPhysicalScalarIntrinsicH1EllipticRegularityMap_inclusion]
  rfl

/-- The elliptic Hessian is symmetric. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticHessian_comm
    (first second : (ellipticOperator period hPeriod).domain) :
    canonicalPhysicalScalarIntrinsicH1EllipticHessian
        period hPeriod first second =
      canonicalPhysicalScalarIntrinsicH1EllipticHessian
        period hPeriod second first := by
  unfold canonicalPhysicalScalarIntrinsicH1EllipticHessian
  calc
    inner Real (ellipticOperator period hPeriod first)
        (second : BulkL2 period hPeriod) =
      inner Real (first : BulkL2 period hPeriod)
        (ellipticOperator period hPeriod second) :=
      canonicalPhysicalScalarIntrinsicH1EllipticOperator_isFormalAdjoint_self
        period hPeriod first second
    _ = inner Real (ellipticOperator period hPeriod second)
        (first : BulkL2 period hPeriod) := real_inner_comm _ _

/-- Exact affine expansion of the sourced action. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_add
    (source : BulkL2 period hPeriod)
    (field variation : (ellipticOperator period hPeriod).domain) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
        source (field + variation) =
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source field +
        canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
          period hPeriod source field variation +
        canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
          period hPeriod variation := by
  have hCross :
      inner Real (ellipticOperator period hPeriod variation)
          (field : BulkL2 period hPeriod) =
        inner Real (ellipticOperator period hPeriod field)
          (variation : BulkL2 period hPeriod) := by
    calc
      _ = inner Real (variation : BulkL2 period hPeriod)
          (ellipticOperator period hPeriod field) :=
        canonicalPhysicalScalarIntrinsicH1EllipticOperator_isFormalAdjoint_self
          period hPeriod variation field
      _ = _ := real_inner_comm _ _
  unfold canonicalPhysicalScalarIntrinsicH1EllipticSourceAction
    canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
    canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
  simp only [LinearPMap.map_add, Submodule.coe_add, inner_add_left,
    inner_add_right, inner_sub_left]
  rw [hCross]
  ring

/-- Exact polynomial expansion along every affine domain line. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_line
    (source : BulkL2 period hPeriod)
    (field variation : (ellipticOperator period hPeriod).domain)
    (parameter : Real) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
        source (field + parameter • variation) =
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source field +
        parameter *
          canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
            period hPeriod source field variation +
        parameter ^ 2 *
          canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
            period hPeriod variation := by
  rw [canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_add]
  unfold canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
    canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
  simp only [LinearPMap.map_smul, Submodule.coe_smul,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- First derivative of the sourced elliptic action. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_hasDerivAt
    (source : BulkL2 period hPeriod)
    (field variation : (ellipticOperator period hPeriod).domain) :
    @HasDerivAt Real _ Real
      Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun parameter : Real =>
        canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source (field + parameter • variation))
      (canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
        period hPeriod source field variation) 0 := by
  let linearTerm :=
    canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
      period hPeriod source field variation
  let quadraticTerm :=
    canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
      period hPeriod variation
  have hPolynomial : ∀ parameter : Real,
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source (field + parameter • variation) =
        canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
            source field +
          parameter * linearTerm + parameter ^ 2 * quadraticTerm := by
    intro parameter
    exact canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_line
      period hPeriod source field variation parameter
  have hDerivative :=
    (((hasDerivAt_const (x := (0 : Real))
      (canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
        source field)).add
      ((hasDerivAt_id (0 : Real)).mul_const linearTerm)).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const quadraticTerm))
  norm_num at hDerivative
  apply hDerivative.congr_of_eventuallyEq
  filter_upwards [] with parameter
  exact hPolynomial parameter

/-- Differentiating the first variation gives the elliptic Hessian. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation_hasDerivAt
    (source : BulkL2 period hPeriod)
    (field first second : (ellipticOperator period hPeriod).domain) :
    @HasDerivAt Real _ Real
      Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun parameter : Real =>
        canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
          period hPeriod source (field + parameter • first) second)
      (canonicalPhysicalScalarIntrinsicH1EllipticHessian
        period hPeriod first second) 0 := by
  let constantTerm :=
    canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
      period hPeriod source field second
  let linearTerm :=
    canonicalPhysicalScalarIntrinsicH1EllipticHessian
      period hPeriod first second
  have hPolynomial : ∀ parameter : Real,
      canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
          period hPeriod source (field + parameter • first) second =
        constantTerm + parameter * linearTerm := by
    intro parameter
    dsimp [constantTerm, linearTerm]
    unfold canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
      canonicalPhysicalScalarIntrinsicH1EllipticHessian
    simp only [LinearPMap.map_add, LinearPMap.map_smul, inner_add_left,
      inner_sub_left, real_inner_smul_left]
    ring
  have hDerivative :=
    (hasDerivAt_const (x := (0 : Real)) constantTerm).add
      ((hasDerivAt_id (0 : Real)).mul_const linearTerm)
  norm_num at hDerivative
  apply hDerivative.congr_of_eventuallyEq
  filter_upwards [] with parameter
  exact hPolynomial parameter

/-- Canonical strong solution supplied by the compact response. -/
def canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
    (source : BulkL2 period hPeriod) :
    (ellipticOperator period hPeriod).domain :=
  canonicalPhysicalScalarIntrinsicH1EllipticDomainElement
    period hPeriod source

/-- The canonical solution satisfies the strong Euler equation. -/
@[simp]
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_equation
    (source : BulkL2 period hPeriod) :
    ellipticOperator period hPeriod
        (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
          period hPeriod source) =
      source :=
  canonicalPhysicalScalarIntrinsicH1EllipticOperator_on_response
    period hPeriod source

/-- The regularity representative of the strong solution is the original H1
source representer. -/
@[simp]
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_regularity
    (source : BulkL2 period hPeriod) :
    regularityMap period hPeriod
        (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
          period hPeriod source) =
      sourceRepresenter period hPeriod source := by
  change sourceRepresenter period hPeriod
      (ellipticOperator period hPeriod
        (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
          period hPeriod source)) =
    sourceRepresenter period hPeriod source
  rw [canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_equation]

/-- Exact completion of the square around the strong solution. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_completion
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceAction
        period hPeriod source field =
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source
          (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
            period hPeriod source) +
        (1 / 2 : Real) *
          ‖regularityMap period hPeriod field -
            sourceRepresenter period hPeriod source‖ ^ 2 := by
  rw [canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_eq_graphH1,
    canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_eq_graphH1,
    canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_regularity]
  exact canonicalPhysicalScalarIntrinsicH1SourceAction_completion
    period hPeriod source (regularityMap period hPeriod field)

/-- Stationarity of the sourced elliptic action. -/
def canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain) : Prop :=
  ∀ variation : (ellipticOperator period hPeriod).domain,
    canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
      period hPeriod source field variation = 0

/-- A strong source solution is stationary. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary_of_equation
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain)
    (hEquation : ellipticOperator period hPeriod field = source) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary
      period hPeriod source field := by
  intro variation
  unfold canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
  rw [hEquation, sub_self, inner_zero_left]

/-- Density upgrades weak stationarity to the strong source equation. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceEquation_of_stationary
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain)
    (hStationary :
      canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary
        period hPeriod source field) :
    ellipticOperator period hPeriod field = source := by
  let residual :=
    ellipticOperator period hPeriod field - source
  let good : Set (BulkL2 period hPeriod) :=
    {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hDomain :
      ((ellipticOperator period hPeriod).domain :
        Set (BulkL2 period hPeriod)) ⊆ good := by
    intro test hTest
    simpa [good, residual,
      canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation] using
      hStationary ⟨test, hTest⟩
  have hClosure :
      closure
          ((ellipticOperator period hPeriod).domain :
            Set (BulkL2 period hPeriod)) =
        Set.univ :=
    (canonicalPhysicalScalarIntrinsicH1EllipticOperator_domain_dense
      period hPeriod).closure_eq
  have hResidual :
      residual ∈
        closure
          ((ellipticOperator period hPeriod).domain :
            Set (BulkL2 period hPeriod)) := by
    rw [hClosure]
    trivial
  have hSelf : inner Real residual residual = 0 :=
    (closure_minimal hDomain hGoodClosed) hResidual
  have hNorm : ‖residual‖ = 0 := by
    have hNormSq : ‖residual‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hSelf
    nlinarith [sq_nonneg ‖residual‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Weak stationarity is exactly the strong Euler equation. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary_iff_equation
    (source : BulkL2 period hPeriod)
    (field : (ellipticOperator period hPeriod).domain) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary
        period hPeriod source field ↔
      ellipticOperator period hPeriod field = source :=
  ⟨canonicalPhysicalScalarIntrinsicH1EllipticSourceEquation_of_stationary
      period hPeriod source field,
    canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary_of_equation
      period hPeriod source field⟩

/-- The strong response solution is stationary. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_stationary
    (source : BulkL2 period hPeriod) :
    canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary period hPeriod
      source
      (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
        period hPeriod source) :=
  canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary_of_equation
    period hPeriod source _
    (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_equation
      period hPeriod source)

/-- The quadratic action controls the bulk norm. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction_coercive
    (field : (ellipticOperator period hPeriod).domain) :
    ‖(field : BulkL2 period hPeriod)‖ ^ 2 ≤
      2 * ‖bulkInclusion period hPeriod‖ ^ 2 *
        canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
          period hPeriod field := by
  have hCoercive :=
    canonicalPhysicalScalarIntrinsicH1EllipticOperator_coercive
      period hPeriod field
  calc
    _ ≤ ‖bulkInclusion period hPeriod‖ ^ 2 *
        inner Real (ellipticOperator period hPeriod field)
          (field : BulkL2 period hPeriod) := hCoercive
    _ = _ := by
      unfold canonicalPhysicalScalarIntrinsicH1EllipticQuadraticAction
      ring

/-- The compact response gives the unique global minimizer of the elliptic
source action. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_unique_minimizer
    (source : BulkL2 period hPeriod) :
    (∀ field : (ellipticOperator period hPeriod).domain,
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source
          (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
            period hPeriod source) ≤
        canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source field) ∧
      (∀ field : (ellipticOperator period hPeriod).domain,
        canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
              source field =
            canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
              source
              (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
                period hPeriod source) →
          field =
            canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
              period hPeriod source) := by
  constructor
  · intro field
    rw [canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_completion
      period hPeriod source field]
    nlinarith [sq_nonneg
      ‖regularityMap period hPeriod field -
        sourceRepresenter period hPeriod source‖]
  · intro field hAction
    rw [canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_completion
      period hPeriod source field]
      at hAction
    have hNorm :
        ‖regularityMap period hPeriod field -
          sourceRepresenter period hPeriod source‖ = 0 := by
      nlinarith [norm_nonneg
        (regularityMap period hPeriod field -
          sourceRepresenter period hPeriod source)]
    have hRegularity :
        regularityMap period hPeriod field =
          sourceRepresenter period hPeriod source :=
      sub_eq_zero.mp (norm_eq_zero.mp hNorm)
    apply Subtype.ext
    rw [←
      canonicalPhysicalScalarIntrinsicH1EllipticRegularityMap_inclusion
        period hPeriod field, hRegularity]
    rfl

/-- Complete variational certificate of the intrinsic elliptic source
action. -/
theorem canonicalPhysicalScalarIntrinsicH1EllipticVariationalAction_certificate
    (source : BulkL2 period hPeriod) :
    ellipticOperator period hPeriod
        (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
          period hPeriod source) =
      source ∧
    canonicalPhysicalScalarIntrinsicH1EllipticSourceStationary period hPeriod
      source
      (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
        period hPeriod source) ∧
    (∀ field variation : (ellipticOperator period hPeriod).domain,
      @HasDerivAt Real _ Real
        Real.normedAddCommGroup.toAddCommGroup
        RCLike.toInnerProductSpaceReal.toModule _ _
        (fun parameter : Real =>
          canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
            source (field + parameter • variation))
        (canonicalPhysicalScalarIntrinsicH1EllipticFirstVariation
          period hPeriod source field variation) 0) ∧
    (∀ field : (ellipticOperator period hPeriod).domain,
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source
          (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
            period hPeriod source) ≤
        canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
          source field) ∧
    (∀ field : (ellipticOperator period hPeriod).domain,
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
            source field =
          canonicalPhysicalScalarIntrinsicH1EllipticSourceAction period hPeriod
            source
            (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
              period hPeriod source) →
        field =
          canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution
            period hPeriod source) := by
  exact
    ⟨canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_equation
        period hPeriod source,
      canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_stationary
        period hPeriod source,
      canonicalPhysicalScalarIntrinsicH1EllipticSourceAction_hasDerivAt
        period hPeriod source,
      (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_unique_minimizer
        period hPeriod source).1,
      (canonicalPhysicalScalarIntrinsicH1EllipticSourceSolution_unique_minimizer
        period hPeriod source).2⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1EllipticVariationalAction4D
end JanusFormal
