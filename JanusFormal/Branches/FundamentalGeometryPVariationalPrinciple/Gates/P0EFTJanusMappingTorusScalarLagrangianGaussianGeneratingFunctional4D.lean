import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFiniteMorseIndex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D

/-!
# Gaussian source generating functional

At a bounded zero-resolvent point, the classical sourced solution is `u_f=R₀f`.
The quadratic source action evaluates on shell to

`S_f(u_f) = -1/2 <f,u_f>`.

The tree-level generating functional is therefore

`W(f)=1/2 <f,R₀f>`.

For a symmetric positive realization this quadratic response is symmetric and
nonnegative.  The file also proves the exact polarization and affine source
identities.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianGaussianGeneratingFunctional4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
open P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Classical source solution given by the zero resolvent. -/
def canonicalScalarClosedLagrangianClassicalSourceSolution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0) :
    Ambient →L[Real]
      canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :=
  zeroResolvent.resolvent

/-- Ambient response operator at zero spectral parameter. -/
def canonicalScalarClosedLagrangianGaussianResponse
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0) :
    Ambient →L[Real] Ambient :=
  zeroResolvent.ambientResolvent
    data hClosable traceBound condition 0

/-- Gaussian bilinear source response. -/
def canonicalScalarClosedLagrangianGaussianPairing
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (first second : Ambient) : Real :=
  inner Real first
    (canonicalScalarClosedLagrangianGaussianResponse
      data hClosable traceBound condition zeroResolvent second)

/-- Tree-level Gaussian generating functional. -/
def canonicalScalarClosedLagrangianGaussianGeneratingFunctional
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) : Real :=
  (1 / 2 : Real) *
    canonicalScalarClosedLagrangianGaussianPairing
      data hClosable traceBound condition zeroResolvent source source

/-- Classical solution solves the source equation. -/
theorem canonicalScalarClosedLagrangianClassicalSourceSolution_equation
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition
        (canonicalScalarClosedLagrangianClassicalSourceSolution
          data hClosable traceBound condition zeroResolvent source) = source :=
  canonicalScalarClosedLagrangian_zeroResolvent_solution
    data hClosable traceBound condition zeroResolvent source

/-- The zero ambient response is symmetric. -/
theorem canonicalScalarClosedLagrangianGaussianResponse_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0) :
    (canonicalScalarClosedLagrangianGaussianResponse
      data hClosable traceBound condition zeroResolvent).toLinearMap.IsSymmetric :=
  canonicalScalarClosedLagrangianAmbientResolvent_isSymmetric
    data hClosable traceBound condition 0 zeroResolvent

/-- Symmetry of the Gaussian pairing. -/
theorem canonicalScalarClosedLagrangianGaussianPairing_comm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (first second : Ambient) :
    canonicalScalarClosedLagrangianGaussianPairing
        data hClosable traceBound condition zeroResolvent first second =
      canonicalScalarClosedLagrangianGaussianPairing
        data hClosable traceBound condition zeroResolvent second first :=
  by
    unfold canonicalScalarClosedLagrangianGaussianPairing
    have hSymmetry :=
      canonicalScalarClosedLagrangianGaussianResponse_isSymmetric
        data hClosable traceBound condition zeroResolvent first second
    calc
      inner Real first
          (canonicalScalarClosedLagrangianGaussianResponse
            data hClosable traceBound condition zeroResolvent second) =
        inner Real
          (canonicalScalarClosedLagrangianGaussianResponse
            data hClosable traceBound condition zeroResolvent first) second := by
              symm
              exact hSymmetry
      _ = inner Real second
          (canonicalScalarClosedLagrangianGaussianResponse
            data hClosable traceBound condition zeroResolvent first) :=
        real_inner_comm _ _

/-- On-shell source action is minus one half the Gaussian pairing. -/
theorem canonicalScalarClosedLagrangianSourceAction_onShell
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    canonicalScalarClosedLagrangianSourceAction
        data hClosable traceBound condition source
        (canonicalScalarClosedLagrangianClassicalSourceSolution
          data hClosable traceBound condition zeroResolvent source) =
      -(1 / 2 : Real) *
        canonicalScalarClosedLagrangianGaussianPairing
          data hClosable traceBound condition zeroResolvent source source := by
  have hEquation :=
    canonicalScalarClosedLagrangianClassicalSourceSolution_equation
      data hClosable traceBound condition zeroResolvent source
  unfold canonicalScalarClosedLagrangianSourceAction
    canonicalScalarClosedLagrangianQuadraticFunctional
    canonicalScalarClosedLagrangianJacobiPairing
    canonicalScalarClosedLagrangianGaussianPairing
    canonicalScalarClosedLagrangianGaussianResponse
  rw [hEquation]
  unfold canonicalScalarClosedLagrangianClassicalSourceSolution
  have hAmbient :
      zeroResolvent.ambientResolvent
          data hClosable traceBound condition 0 source =
        canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (zeroResolvent.resolvent source) := by
    simp [CanonicalScalarClosedLagrangianBoundedResolventAt.ambientResolvent,
      canonicalScalarClosedLagrangianDomainInclusionCLM,
      canonicalScalarClosedLagrangianDomainInclusion,
      canonicalScalarClosedOperatorInclusion]
  rw [hAmbient]
  ring

/-- Generating functional is minus the on-shell source action. -/
theorem canonicalScalarClosedLagrangianGaussianGeneratingFunctional_eq_neg_onShell
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    canonicalScalarClosedLagrangianGaussianGeneratingFunctional
        data hClosable traceBound condition zeroResolvent source =
      -canonicalScalarClosedLagrangianSourceAction
        data hClosable traceBound condition source
        (canonicalScalarClosedLagrangianClassicalSourceSolution
          data hClosable traceBound condition zeroResolvent source) := by
  rw [canonicalScalarClosedLagrangianSourceAction_onShell]
  unfold canonicalScalarClosedLagrangianGaussianGeneratingFunctional
  ring

/-- Exact polarization of the Gaussian generating functional. -/
theorem canonicalScalarClosedLagrangianGaussianGeneratingFunctional_add
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (first second : Ambient) :
    canonicalScalarClosedLagrangianGaussianGeneratingFunctional
        data hClosable traceBound condition zeroResolvent (first + second) =
      canonicalScalarClosedLagrangianGaussianGeneratingFunctional
          data hClosable traceBound condition zeroResolvent first +
        canonicalScalarClosedLagrangianGaussianGeneratingFunctional
          data hClosable traceBound condition zeroResolvent second +
        canonicalScalarClosedLagrangianGaussianPairing
          data hClosable traceBound condition zeroResolvent first second := by
  have hComm := canonicalScalarClosedLagrangianGaussianPairing_comm
    data hClosable traceBound condition zeroResolvent second first
  unfold canonicalScalarClosedLagrangianGaussianPairing at hComm
  unfold canonicalScalarClosedLagrangianGaussianGeneratingFunctional
    canonicalScalarClosedLagrangianGaussianPairing
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hComm]
  ring

/-- Homogeneity of the Gaussian generating functional. -/
theorem canonicalScalarClosedLagrangianGaussianGeneratingFunctional_smul
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (scalar : Real) (source : Ambient) :
    canonicalScalarClosedLagrangianGaussianGeneratingFunctional
        data hClosable traceBound condition zeroResolvent (scalar • source) =
      scalar ^ 2 * canonicalScalarClosedLagrangianGaussianGeneratingFunctional
        data hClosable traceBound condition zeroResolvent source := by
  unfold canonicalScalarClosedLagrangianGaussianGeneratingFunctional
    canonicalScalarClosedLagrangianGaussianPairing
    canonicalScalarClosedLagrangianGaussianResponse
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Positivity of the operator gives nonnegative Gaussian response. -/
theorem canonicalScalarClosedLagrangianGaussianGeneratingFunctional_nonnegative
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (hPositive : 0 < semibounded.lowerBound)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    0 ≤ canonicalScalarClosedLagrangianGaussianGeneratingFunctional
      data hClosable traceBound condition zeroResolvent source := by
  let solution := zeroResolvent.resolvent source
  have hEquation := canonicalScalarClosedLagrangianClassicalSourceSolution_equation
    data hClosable traceBound condition zeroResolvent source
  have hBound := semibounded.bound solution
  unfold canonicalScalarClosedLagrangianGaussianGeneratingFunctional
    canonicalScalarClosedLagrangianGaussianPairing
    canonicalScalarClosedLagrangianGaussianResponse
  change 0 ≤ (1 / 2 : Real) * inner Real source
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition solution)
  rw [← hEquation]
  change 0 ≤ (1 / 2 : Real) * inner Real
    (canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition solution)
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition solution)
  have hLowerTerm : 0 ≤ semibounded.lowerBound *
      ‖canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition solution‖ ^ 2 :=
    mul_nonneg (le_of_lt hPositive) (sq_nonneg _)
  linarith

/-- Gaussian generating-functional certificate. -/
theorem canonicalScalarLagrangianGaussianGeneratingFunctional_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition
        (canonicalScalarClosedLagrangianClassicalSourceSolution
          data hClosable traceBound condition zeroResolvent source) = source ∧
      canonicalScalarClosedLagrangianGaussianGeneratingFunctional
          data hClosable traceBound condition zeroResolvent source =
        -canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source
          (canonicalScalarClosedLagrangianClassicalSourceSolution
            data hClosable traceBound condition zeroResolvent source) :=
  ⟨canonicalScalarClosedLagrangianClassicalSourceSolution_equation
      data hClosable traceBound condition zeroResolvent source,
    canonicalScalarClosedLagrangianGaussianGeneratingFunctional_eq_neg_onShell
      data hClosable traceBound condition zeroResolvent source⟩

end
end P0EFTJanusMappingTorusScalarLagrangianGaussianGeneratingFunctional4D
end JanusFormal
