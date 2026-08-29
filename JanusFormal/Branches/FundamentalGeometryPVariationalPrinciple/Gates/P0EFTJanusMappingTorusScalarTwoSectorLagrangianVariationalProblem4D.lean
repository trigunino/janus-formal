import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D

/-!
# Two-sector scalar parent variational problem

For two copies of one closed Lagrangian scalar domain, define the sourced parent
action

`S(u,v) = 1/2 Q(u) + 1/2 Q(v) + kappa <u,v> - <f,u> - <g,v>`.

Its first variations are the coupled bulk equations

`A u + kappa v = f`, `A v + kappa u = g`.

The even/odd coordinates `e=(u+v)/2`, `o=(u-v)/2` diagonalize these equations to
`(A+kappa)e=(f+g)/2` and `(A-kappa)o=(f-g)/2`.  The parent action splits into the
same shifted diagonal/relative sectors.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarTwoSectorLagrangianVariationalProblem4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
open P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D

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

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {hClosable : CanonicalScalarGraphClosable data}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace}

/-- Even domain coordinate. -/
def canonicalScalarTwoSectorDomainEven
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) :
    LagrangianDomain data hClosable traceBound condition :=
  (1 / 2 : Real) • (field.1 + field.2)

/-- Odd domain coordinate. -/
def canonicalScalarTwoSectorDomainOdd
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) :
    LagrangianDomain data hClosable traceBound condition :=
  (1 / 2 : Real) • (field.1 - field.2)

/-- Reconstruction from even and odd domain coordinates. -/
theorem canonicalScalarTwoSectorDomain_reconstruction
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) :
    field =
      (canonicalScalarTwoSectorDomainEven field +
          canonicalScalarTwoSectorDomainOdd field,
        canonicalScalarTwoSectorDomainEven field -
          canonicalScalarTwoSectorDomainOdd field) := by
  apply Prod.ext <;>
    simp [canonicalScalarTwoSectorDomainEven,
      canonicalScalarTwoSectorDomainOdd] <;> module

/-- Unsourced two-sector quadratic parent action. -/
def canonicalScalarTwoSectorParentQuadraticAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) : Real :=
  (1 / 2 : Real) *
      canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition field.1 +
    (1 / 2 : Real) *
      canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition field.2 +
    coupling * canonicalScalarClosedLagrangianMassPairing
      data hClosable traceBound condition field.1 field.2

/-- Sourced two-sector parent action. -/
def canonicalScalarTwoSectorParentSourceAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real)
    (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) : Real :=
  canonicalScalarTwoSectorParentQuadraticAction
      data hClosable traceBound condition coupling field -
    inner Real source.1
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.1) -
    inner Real source.2
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.2)

/-- Coupled strong Euler equations. -/
def CanonicalScalarTwoSectorStrongSolution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real)
    (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) : Prop :=
  canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field.1 +
      coupling • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.2 = source.1 ∧
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field.2 +
      coupling • canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.1 = source.2

/-- Weak stationarity against arbitrary two-sector variations. -/
def CanonicalScalarTwoSectorStationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real)
    (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) : Prop :=
  ∀ variation : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition,
    canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field.1 variation.1 +
        coupling * canonicalScalarClosedLagrangianMassPairing
          data hClosable traceBound condition field.2 variation.1 =
      inner Real source.1
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition variation.1) ∧
    canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field.2 variation.2 +
        coupling * canonicalScalarClosedLagrangianMassPairing
          data hClosable traceBound condition field.1 variation.2 =
      inner Real source.2
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition variation.2)

/-- Exact affine Taylor formula for the two-sector sourced action. -/
theorem canonicalScalarTwoSectorParentSourceAction_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real) (source : Ambient × Ambient)
    (field variation : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition)
    (parameter : Real) :
    canonicalScalarTwoSectorParentSourceAction
        data hClosable traceBound condition coupling source
        (field + parameter • variation) =
      canonicalScalarTwoSectorParentSourceAction
          data hClosable traceBound condition coupling source field +
        parameter *
          (canonicalScalarClosedLagrangianJacobiPairing
              data hClosable traceBound condition field.1 variation.1 +
            canonicalScalarClosedLagrangianJacobiPairing
              data hClosable traceBound condition field.2 variation.2 +
            coupling * canonicalScalarClosedLagrangianMassPairing
              data hClosable traceBound condition field.2 variation.1 +
            coupling * canonicalScalarClosedLagrangianMassPairing
              data hClosable traceBound condition field.1 variation.2 -
            inner Real source.1
              (canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition variation.1) -
            inner Real source.2
              (canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition variation.2)) +
        parameter ^ 2 *
          canonicalScalarTwoSectorParentQuadraticAction
            data hClosable traceBound condition coupling variation := by
  have hFirst := canonicalScalarClosedLagrangianQuadraticFunctional_affine
    data hClosable traceBound condition field.1 variation.1 parameter
  have hSecond := canonicalScalarClosedLagrangianQuadraticFunctional_affine
    data hClosable traceBound condition field.2 variation.2 parameter
  simp only [canonicalScalarClosedLagrangianAffineCurve] at hFirst hSecond
  unfold canonicalScalarTwoSectorParentSourceAction
    canonicalScalarTwoSectorParentQuadraticAction
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  rw [hFirst, hSecond]
  simp only [canonicalScalarClosedLagrangianMassPairing,
    map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition variation.1)
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.2)]
  ring

/-- Strong coupled equations imply weak stationarity. -/
theorem canonicalScalarTwoSectorStrongSolution_stationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real) (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition)
    (hSolution : CanonicalScalarTwoSectorStrongSolution
      data hClosable traceBound condition coupling source field) :
    CanonicalScalarTwoSectorStationary
      data hClosable traceBound condition coupling source field := by
  intro variation
  constructor
  · unfold canonicalScalarClosedLagrangianJacobiPairing
      canonicalScalarClosedLagrangianMassPairing
    rw [← real_inner_smul_left, ← inner_add_left, hSolution.1]
  · unfold canonicalScalarClosedLagrangianJacobiPairing
      canonicalScalarClosedLagrangianMassPairing
    rw [← real_inner_smul_left, ← inner_add_left, hSolution.2]

/-- Dense weak stationarity implies the strong coupled equations. -/
theorem canonicalScalarTwoSectorStationary_strongSolution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real) (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition))
    (hStationary : CanonicalScalarTwoSectorStationary
      data hClosable traceBound condition coupling source field) :
    CanonicalScalarTwoSectorStrongSolution
      data hClosable traceBound condition coupling source field := by
  constructor
  · let effectiveSource := source.1 - coupling •
      canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.2
    have hOperator :=
      canonicalScalarClosedLagrangian_stationary_sourceSolution
        data hClosable traceBound condition effectiveSource field.1 hDense (by
          intro variation
          have h := (hStationary (variation, 0)).1
          unfold canonicalScalarClosedLagrangianMassPairing at h
          change canonicalScalarClosedLagrangianJacobiPairing
                data hClosable traceBound condition field.1 variation =
            inner Real effectiveSource
              (canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition variation)
          rw [inner_sub_left, real_inner_smul_left]
          linarith)
    dsimp [effectiveSource] at hOperator
    rw [hOperator]
    module
  · let effectiveSource := source.2 - coupling •
      canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field.1
    have hOperator :=
      canonicalScalarClosedLagrangian_stationary_sourceSolution
        data hClosable traceBound condition effectiveSource field.2 hDense (by
          intro variation
          have h := (hStationary (0, variation)).2
          unfold canonicalScalarClosedLagrangianMassPairing at h
          change canonicalScalarClosedLagrangianJacobiPairing
                data hClosable traceBound condition field.2 variation =
            inner Real effectiveSource
              (canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition variation)
          rw [inner_sub_left, real_inner_smul_left]
          linarith)
    dsimp [effectiveSource] at hOperator
    rw [hOperator]
    module

/-- Weak and strong two-sector equations are equivalent under density. -/
theorem canonicalScalarTwoSectorStationary_iff_strongSolution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real) (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) :
    CanonicalScalarTwoSectorStationary
        data hClosable traceBound condition coupling source field ↔
      CanonicalScalarTwoSectorStrongSolution
        data hClosable traceBound condition coupling source field :=
  ⟨canonicalScalarTwoSectorStationary_strongSolution
      data hClosable traceBound condition coupling source field hDense,
    canonicalScalarTwoSectorStrongSolution_stationary
      data hClosable traceBound condition coupling source field⟩

/-- Diagonalization of the coupled strong equations. -/
theorem canonicalScalarTwoSectorStrongSolution_iff_even_odd
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real) (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) :
    CanonicalScalarTwoSectorStrongSolution
        data hClosable traceBound condition coupling source field ↔
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainEven field) +
        coupling • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainEven field) =
        (1 / 2 : Real) • (source.1 + source.2) ∧
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainOdd field) -
        coupling • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainOdd field) =
        (1 / 2 : Real) • (source.1 - source.2) := by
  constructor
  · intro hSolution
    constructor
    · unfold canonicalScalarTwoSectorDomainEven
      rw [map_smul, map_add, map_smul, map_add]
      rw [← hSolution.1, ← hSolution.2]
      module
    · unfold canonicalScalarTwoSectorDomainOdd
      rw [map_smul, map_sub, map_smul, map_sub]
      rw [← hSolution.1, ← hSolution.2]
      module
  · intro hDiagonal
    have hReconstruct := canonicalScalarTwoSectorDomain_reconstruction field
    rw [hReconstruct]
    constructor
    · have hSum := hDiagonal.1
      have hDiff := hDiagonal.2
      calc
        canonicalScalarClosedLagrangianDomainOperator
              data hClosable traceBound condition
              (canonicalScalarTwoSectorDomainEven field +
                canonicalScalarTwoSectorDomainOdd field) +
            coupling • canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition
              (canonicalScalarTwoSectorDomainEven field -
                canonicalScalarTwoSectorDomainOdd field) =
            (canonicalScalarClosedLagrangianDomainOperator
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainEven field) +
              coupling • canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainEven field)) +
            (canonicalScalarClosedLagrangianDomainOperator
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainOdd field) -
              coupling • canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainOdd field)) := by
                  simp only [map_add, map_sub, smul_sub]
                  module
        _ = (1 / 2 : Real) • (source.1 + source.2) +
            (1 / 2 : Real) • (source.1 - source.2) := by rw [hSum, hDiff]
        _ = source.1 := by module
    · have hSum := hDiagonal.1
      have hDiff := hDiagonal.2
      calc
        canonicalScalarClosedLagrangianDomainOperator
              data hClosable traceBound condition
              (canonicalScalarTwoSectorDomainEven field -
                canonicalScalarTwoSectorDomainOdd field) +
            coupling • canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition
              (canonicalScalarTwoSectorDomainEven field +
                canonicalScalarTwoSectorDomainOdd field) =
            (canonicalScalarClosedLagrangianDomainOperator
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainEven field) +
              coupling • canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainEven field)) -
            (canonicalScalarClosedLagrangianDomainOperator
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainOdd field) -
              coupling • canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition
                (canonicalScalarTwoSectorDomainOdd field)) := by
                  simp only [map_add, map_sub, smul_add]
                  module
        _ = (1 / 2 : Real) • (source.1 + source.2) -
            (1 / 2 : Real) • (source.1 - source.2) := by rw [hSum, hDiff]
        _ = source.2 := by module

/-- Diagonalization of the unsourced parent quadratic action. -/
theorem canonicalScalarTwoSectorParentQuadraticAction_diagonalization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition) :
    canonicalScalarTwoSectorParentQuadraticAction
        data hClosable traceBound condition coupling field =
      canonicalScalarClosedLagrangianQuadraticFunctional
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainEven field) +
        coupling * canonicalScalarClosedLagrangianMassFunctional
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainEven field) +
      canonicalScalarClosedLagrangianQuadraticFunctional
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainOdd field) -
        coupling * canonicalScalarClosedLagrangianMassFunctional
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainOdd field) := by
  have hReconstruct := canonicalScalarTwoSectorDomain_reconstruction field
  nth_rewrite 1 [hReconstruct]
  unfold canonicalScalarTwoSectorParentQuadraticAction
    canonicalScalarClosedLagrangianQuadraticFunctional
    canonicalScalarClosedLagrangianJacobiPairing
    canonicalScalarClosedLagrangianMassFunctional
    canonicalScalarClosedLagrangianMassPairing
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  rw [canonicalScalarClosedLagrangianDomainOperator_symmetric
      data hClosable traceBound condition
      (canonicalScalarTwoSectorDomainEven field)
      (canonicalScalarTwoSectorDomainOdd field),
    real_inner_comm
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (canonicalScalarTwoSectorDomainEven field))
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (canonicalScalarTwoSectorDomainOdd field))]
  ring

/-- Two-sector variational certificate. -/
theorem canonicalScalarTwoSectorLagrangianVariationalProblem_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (coupling : Real) (source : Ambient × Ambient)
    (field : LagrangianDomain data hClosable traceBound condition ×
      LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) :
    (CanonicalScalarTwoSectorStationary
        data hClosable traceBound condition coupling source field ↔
      CanonicalScalarTwoSectorStrongSolution
        data hClosable traceBound condition coupling source field) ∧
      (CanonicalScalarTwoSectorStrongSolution
        data hClosable traceBound condition coupling source field ↔
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainEven field) +
        coupling • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainEven field) =
        (1 / 2 : Real) • (source.1 + source.2) ∧
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainOdd field) -
        coupling • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition
          (canonicalScalarTwoSectorDomainOdd field) =
        (1 / 2 : Real) • (source.1 - source.2)) :=
  ⟨canonicalScalarTwoSectorStationary_iff_strongSolution
      data hClosable traceBound condition coupling source field hDense,
    canonicalScalarTwoSectorStrongSolution_iff_even_odd
      data hClosable traceBound condition coupling source field⟩

end
end P0EFTJanusMappingTorusScalarTwoSectorLagrangianVariationalProblem4D
end JanusFormal
