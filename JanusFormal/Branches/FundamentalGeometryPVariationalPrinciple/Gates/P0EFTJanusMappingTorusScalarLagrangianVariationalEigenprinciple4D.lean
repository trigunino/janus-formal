import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D

/-!
# Variational eigenvalue principle for closed Lagrangian scalar realizations

This file formulates the quadratic variational principle directly on the actual
closed operator domain.  It defines the Jacobi pairing, mass pairing, quadratic
functional and constrained functional.  Exact affine Taylor formulas identify
the first variation.

When the domain inclusion is dense in the ambient Hilbert space, vanishing of
all constrained first variations is equivalent to the strong eigenvalue
equation.  Every nonzero eigenfield has Rayleigh quotient equal to its
eigenvalue.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

private abbrev LagrangianDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    data hClosable traceBound condition

/-- Symmetric Jacobi pairing on the actual Lagrangian operator domain. -/
def canonicalScalarClosedLagrangianJacobiPairing
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : LagrangianDomain data hClosable traceBound condition) : Real :=
  inner Real
    (canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition first)
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition second)

/-- Ambient mass pairing on the same domain. -/
def canonicalScalarClosedLagrangianMassPairing
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : LagrangianDomain data hClosable traceBound condition) : Real :=
  inner Real
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition first)
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition second)

/-- Symmetry of the Jacobi pairing is exactly the boundary-Lagrangian Green
identity. -/
theorem canonicalScalarClosedLagrangianJacobiPairing_comm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition first second =
      canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition second first := by
  unfold canonicalScalarClosedLagrangianJacobiPairing
  calc
    _ = inner Real
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition first)
        (canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition second) :=
      canonicalScalarClosedLagrangianDomainOperator_symmetric
        data hClosable traceBound condition first second
    _ = _ := real_inner_comm _ _

/-- Symmetry of the mass pairing. -/
theorem canonicalScalarClosedLagrangianMassPairing_comm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianMassPairing
        data hClosable traceBound condition first second =
      canonicalScalarClosedLagrangianMassPairing
        data hClosable traceBound condition second first :=
  real_inner_comm _ _

@[simp] theorem canonicalScalarClosedLagrangianJacobiPairing_add_left
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second test : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition (first + second) test =
      canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition first test +
        canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition second test := by
  simp [canonicalScalarClosedLagrangianJacobiPairing, inner_add_left]

@[simp] theorem canonicalScalarClosedLagrangianJacobiPairing_add_right
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field first second : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition field (first + second) =
      canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field first +
        canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field second := by
  simp [canonicalScalarClosedLagrangianJacobiPairing, inner_add_right]

@[simp] theorem canonicalScalarClosedLagrangianJacobiPairing_smul_left
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (scalar : Real)
    (field test : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition (scalar • field) test =
      scalar * canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition field test := by
  simp [canonicalScalarClosedLagrangianJacobiPairing,
    real_inner_smul_left]

@[simp] theorem canonicalScalarClosedLagrangianJacobiPairing_smul_right
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (scalar : Real)
    (field test : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition field (scalar • test) =
      scalar * canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition field test := by
  simp [canonicalScalarClosedLagrangianJacobiPairing,
    real_inner_smul_right]

/-- Jacobi quadratic functional. -/
def canonicalScalarClosedLagrangianQuadraticFunctional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : LagrangianDomain data hClosable traceBound condition) : Real :=
  canonicalScalarClosedLagrangianJacobiPairing
    data hClosable traceBound condition field field

/-- Ambient squared norm functional. -/
def canonicalScalarClosedLagrangianMassFunctional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : LagrangianDomain data hClosable traceBound condition) : Real :=
  canonicalScalarClosedLagrangianMassPairing
    data hClosable traceBound condition field field

/-- Constrained quadratic functional `Q - lambda M`. -/
def canonicalScalarClosedLagrangianConstrainedFunctional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition) : Real :=
  canonicalScalarClosedLagrangianQuadraticFunctional
      data hClosable traceBound condition field -
    eigenvalue * canonicalScalarClosedLagrangianMassFunctional
      data hClosable traceBound condition field

/-- Affine curve in the actual operator domain. -/
def canonicalScalarClosedLagrangianAffineCurve
    {data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
    {hClosable : CanonicalScalarGraphClosable data}
    {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
    {condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace}
    (field variation : LagrangianDomain data hClosable traceBound condition)
    (parameter : Real) : LagrangianDomain data hClosable traceBound condition :=
  field + parameter • variation

/-- Exact quadratic Taylor formula for the Jacobi functional. -/
theorem canonicalScalarClosedLagrangianQuadraticFunctional_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field variation : LagrangianDomain data hClosable traceBound condition)
    (parameter : Real) :
    canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition
        (canonicalScalarClosedLagrangianAffineCurve field variation parameter) =
      canonicalScalarClosedLagrangianQuadraticFunctional
          data hClosable traceBound condition field +
        2 * parameter * canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field variation +
        parameter ^ 2 * canonicalScalarClosedLagrangianQuadraticFunctional
          data hClosable traceBound condition variation := by
  unfold canonicalScalarClosedLagrangianQuadraticFunctional
    canonicalScalarClosedLagrangianAffineCurve
  rw [canonicalScalarClosedLagrangianJacobiPairing_add_left,
    canonicalScalarClosedLagrangianJacobiPairing_add_right,
    canonicalScalarClosedLagrangianJacobiPairing_add_right,
    canonicalScalarClosedLagrangianJacobiPairing_smul_left,
    canonicalScalarClosedLagrangianJacobiPairing_smul_right,
    canonicalScalarClosedLagrangianJacobiPairing_smul_right,
    canonicalScalarClosedLagrangianJacobiPairing_comm
      data hClosable traceBound condition variation field]
  ring

/-- Exact quadratic Taylor formula for the ambient mass functional. -/
theorem canonicalScalarClosedLagrangianMassFunctional_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field variation : LagrangianDomain data hClosable traceBound condition)
    (parameter : Real) :
    canonicalScalarClosedLagrangianMassFunctional
        data hClosable traceBound condition
        (canonicalScalarClosedLagrangianAffineCurve field variation parameter) =
      canonicalScalarClosedLagrangianMassFunctional
          data hClosable traceBound condition field +
        2 * parameter * canonicalScalarClosedLagrangianMassPairing
          data hClosable traceBound condition field variation +
        parameter ^ 2 * canonicalScalarClosedLagrangianMassFunctional
          data hClosable traceBound condition variation := by
  unfold canonicalScalarClosedLagrangianMassFunctional
    canonicalScalarClosedLagrangianMassPairing
    canonicalScalarClosedLagrangianAffineCurve
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition variation)
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition field)]
  ring

/-- Exact quadratic Taylor formula for the constrained functional. -/
theorem canonicalScalarClosedLagrangianConstrainedFunctional_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field variation : LagrangianDomain data hClosable traceBound condition)
    (parameter : Real) :
    canonicalScalarClosedLagrangianConstrainedFunctional
        data hClosable traceBound condition eigenvalue
        (canonicalScalarClosedLagrangianAffineCurve field variation parameter) =
      canonicalScalarClosedLagrangianConstrainedFunctional
          data hClosable traceBound condition eigenvalue field +
        parameter *
          (2 * (canonicalScalarClosedLagrangianJacobiPairing
              data hClosable traceBound condition field variation -
            eigenvalue * canonicalScalarClosedLagrangianMassPairing
              data hClosable traceBound condition field variation)) +
        parameter ^ 2 *
          canonicalScalarClosedLagrangianConstrainedFunctional
            data hClosable traceBound condition eigenvalue variation := by
  unfold canonicalScalarClosedLagrangianConstrainedFunctional
  rw [canonicalScalarClosedLagrangianQuadraticFunctional_affine,
    canonicalScalarClosedLagrangianMassFunctional_affine]
  ring

/-- First derivative of the constrained functional along every affine domain
variation. -/
theorem canonicalScalarClosedLagrangianConstrainedFunctional_hasDerivAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field variation : LagrangianDomain data hClosable traceBound condition) :
    HasDerivAt
      (fun parameter : Real =>
        canonicalScalarClosedLagrangianConstrainedFunctional
          data hClosable traceBound condition eigenvalue
          (canonicalScalarClosedLagrangianAffineCurve field variation parameter))
      (2 * (canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field variation -
        eigenvalue * canonicalScalarClosedLagrangianMassPairing
          data hClosable traceBound condition field variation)) 0 := by
  rw [show (fun parameter : Real =>
      canonicalScalarClosedLagrangianConstrainedFunctional
        data hClosable traceBound condition eigenvalue
        (canonicalScalarClosedLagrangianAffineCurve field variation parameter)) =
      (fun parameter : Real =>
        canonicalScalarClosedLagrangianConstrainedFunctional
            data hClosable traceBound condition eigenvalue field +
          parameter *
            (2 * (canonicalScalarClosedLagrangianJacobiPairing
                data hClosable traceBound condition field variation -
              eigenvalue * canonicalScalarClosedLagrangianMassPairing
                data hClosable traceBound condition field variation)) +
          parameter ^ 2 *
            canonicalScalarClosedLagrangianConstrainedFunctional
              data hClosable traceBound condition eigenvalue variation) from by
        funext parameter
        exact canonicalScalarClosedLagrangianConstrainedFunctional_affine
          data hClosable traceBound condition eigenvalue field variation parameter]
  simpa [Pi.add_apply] using (((hasDerivAt_const (x := (0 : Real))
      (canonicalScalarClosedLagrangianConstrainedFunctional
        data hClosable traceBound condition eigenvalue field)).add
      ((hasDerivAt_id (0 : Real)).mul_const
        (2 * (canonicalScalarClosedLagrangianJacobiPairing
            data hClosable traceBound condition field variation -
          eigenvalue * canonicalScalarClosedLagrangianMassPairing
            data hClosable traceBound condition field variation)))).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const
        (canonicalScalarClosedLagrangianConstrainedFunctional
          data hClosable traceBound condition eigenvalue variation)))

/-- Weak constrained stationarity at a candidate eigenvalue. -/
def CanonicalScalarClosedLagrangianStationaryAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition) : Prop :=
  ∀ variation : LagrangianDomain data hClosable traceBound condition,
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition field variation =
      eigenvalue * canonicalScalarClosedLagrangianMassPairing
        data hClosable traceBound condition field variation

/-- Every strong eigenfield is constrained-stationary. -/
theorem canonicalScalarClosedLagrangian_eigenfield_stationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hEigen :
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field) :
    CanonicalScalarClosedLagrangianStationaryAt
      data hClosable traceBound condition eigenvalue field := by
  intro variation
  unfold canonicalScalarClosedLagrangianJacobiPairing
    canonicalScalarClosedLagrangianMassPairing
  rw [hEigen, real_inner_smul_left]

/-- Dense weak stationarity implies the strong eigenvalue equation. -/
theorem canonicalScalarClosedLagrangian_stationary_eigenfield
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition))
    (hStationary : CanonicalScalarClosedLagrangianStationaryAt
      data hClosable traceBound condition eigenvalue field) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field =
      eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field := by
  let residual : Ambient :=
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field -
      eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq
    · fun_prop
    · fun_prop
  have hRange : Set.range
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition) ⊆ good := by
    rintro test ⟨variation, rfl⟩
    dsimp [good, residual]
    rw [inner_sub_left, real_inner_smul_left]
    change canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field variation -
        eigenvalue * canonicalScalarClosedLagrangianMassPairing
          data hClosable traceBound condition field variation = 0
    rw [hStationary variation, sub_self]
  have hClosure : closure (Set.range
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) = Set.univ :=
    hDense.closure_range
  have hResidualMem : residual ∈ closure (Set.range
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) := by
    rw [hClosure]
    trivial
  have hResidualGood := (closure_minimal hRange hGoodClosed) hResidualMem
  have hResidualInner : inner Real residual residual = 0 := hResidualGood
  have hResidualNorm : ‖residual‖ = 0 := by
    rw [← sq_eq_zero_iff]
    simpa [real_inner_self_eq_norm_sq] using hResidualInner
  have hResidualZero : residual = 0 := norm_eq_zero.mp hResidualNorm
  exact sub_eq_zero.mp hResidualZero

/-- Under a dense domain inclusion, constrained stationarity is equivalent to
the strong eigenfield equation. -/
theorem canonicalScalarClosedLagrangian_stationary_iff_eigenfield
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) :
    CanonicalScalarClosedLagrangianStationaryAt
        data hClosable traceBound condition eigenvalue field ↔
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field :=
  ⟨canonicalScalarClosedLagrangian_stationary_eigenfield
      data hClosable traceBound condition eigenvalue field hDense,
    canonicalScalarClosedLagrangian_eigenfield_stationary
      data hClosable traceBound condition eigenvalue field⟩

/-- Rayleigh quotient on nonzero domain fields. -/
noncomputable def canonicalScalarClosedLagrangianRayleighQuotient
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : LagrangianDomain data hClosable traceBound condition) : Real :=
  canonicalScalarClosedLagrangianQuadraticFunctional
      data hClosable traceBound condition field /
    canonicalScalarClosedLagrangianMassFunctional
      data hClosable traceBound condition field

/-- The mass functional is the squared ambient norm. -/
theorem canonicalScalarClosedLagrangianMassFunctional_eq_norm_sq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianMassFunctional
        data hClosable traceBound condition field =
      ‖canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field‖ ^ 2 := by
  unfold canonicalScalarClosedLagrangianMassFunctional
    canonicalScalarClosedLagrangianMassPairing
  exact real_inner_self_eq_norm_sq _

/-- Every nonzero eigenfield has Rayleigh quotient equal to its eigenvalue. -/
theorem canonicalScalarClosedLagrangianRayleighQuotient_eigenfield
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hField : field ≠ 0)
    (hEigen :
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field) :
    canonicalScalarClosedLagrangianRayleighQuotient
        data hClosable traceBound condition field = eigenvalue := by
  let ambientField := canonicalScalarClosedLagrangianDomainInclusion
    data hClosable traceBound condition field
  have hAmbient : ambientField ≠ 0 :=
    canonicalScalarClosedLagrangian_eigenfield_inclusion_ne_zero
      data hClosable traceBound condition field hField
  have hNormSq : ‖ambientField‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hAmbient)
  unfold canonicalScalarClosedLagrangianRayleighQuotient
    canonicalScalarClosedLagrangianQuadraticFunctional
    canonicalScalarClosedLagrangianJacobiPairing
  rw [hEigen, real_inner_smul_left,
    canonicalScalarClosedLagrangianMassFunctional_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  field_simp

/-- Variational-eigenvalue certificate. -/
theorem canonicalScalarLagrangianVariationalEigenprinciple_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (eigenvalue : Real)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) :
    (CanonicalScalarClosedLagrangianStationaryAt
        data hClosable traceBound condition eigenvalue field ↔
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field) ∧
      (∀ variation : LagrangianDomain data hClosable traceBound condition,
        HasDerivAt
          (fun parameter : Real =>
            canonicalScalarClosedLagrangianConstrainedFunctional
              data hClosable traceBound condition eigenvalue
              (canonicalScalarClosedLagrangianAffineCurve
                field variation parameter))
          (2 * (canonicalScalarClosedLagrangianJacobiPairing
              data hClosable traceBound condition field variation -
            eigenvalue * canonicalScalarClosedLagrangianMassPairing
              data hClosable traceBound condition field variation)) 0) :=
  ⟨canonicalScalarClosedLagrangian_stationary_iff_eigenfield
      data hClosable traceBound condition eigenvalue field hDense,
    canonicalScalarClosedLagrangianConstrainedFunctional_hasDerivAt
      data hClosable traceBound condition eigenvalue field⟩

end
end P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
end JanusFormal
