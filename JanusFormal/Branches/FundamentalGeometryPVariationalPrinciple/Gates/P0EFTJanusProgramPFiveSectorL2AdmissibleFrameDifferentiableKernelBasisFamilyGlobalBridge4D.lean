import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D

/-!
# Differentiable true-kernel families from admissible L² frames

Vectorwise differentiability of the basepoint frame on the fixed kernel basis
upgrades the transported true-kernel bases to the standard differentiable
finite-kernel-family packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2AdmissibleFrameDifferentiableKernelBasisFamilyGlobalBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiniteIntertwiningOperatorFrameTransport4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D
open P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D.DifferentiableFiniteKernelBasisFamilyData
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData

variable
  {State Metric Abelian Matter Longitudinal Boundary : Type*}
  {Index : Type}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}
  {operator : Real → State →L[Real] State}

namespace FiveSectorL2AdmissibleFrameKernelGramData

variable
  (representation : NaturalEllipticOperatorRepresentationData
    immersionCategory family
      (fun parameter state => operator parameter state))
  (coordinates : FiveSectorHilbertCoordinates
    (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
    (Longitudinal := Longitudinal) (Boundary := Boundary))
  (refinement : FiveSectorNaturalRepresentationRefinementData
    representation coordinates)
  (pullback : FiveSectorNaturalRepresentationPullbackData
    representation coordinates refinement)
  (data : FiveSectorL2AdmissibleFrameKernelGramData
    (Index := Index) representation coordinates refinement pullback)

/-- The standard ambient kernel vector is the base basis vector acted on by
the admissible operator frame. -/
theorem toFiniteKernelBasisFamilyData_vector_eq_operatorFrame
    [Fintype Index] [DecidableEq Index]
    (parameter : Real) (index : Index) :
    (toFiniteKernelBasisFamilyData representation coordinates refinement
        pullback data).vector parameter index =
      (data.operatorFrame representation coordinates refinement pullback).frame
        parameter (data.baseKernelBasis index).1 := by
  rw [toFiniteKernelBasisFamilyData_vector representation coordinates
    refinement pullback data parameter index]
  change
    (data.operatorFrame representation coordinates refinement pullback).transport
        0 parameter (data.baseKernelBasis index).1 =
      (data.operatorFrame representation coordinates refinement pullback).frame
        parameter (data.baseKernelBasis index).1
  rw [(data.operatorFrame representation coordinates refinement pullback).transport_zero
    parameter]

/-- Upgrade the transported true-kernel bases using precisely the
frame-on-base-basis differentiability hypothesis. -/
def toDifferentiableFiniteKernelBasisFamilyData
    [Fintype Index] [DecidableEq Index]
    (operatorFrame_vector_differentiable : ∀ index,
      Differentiable Real
        (fun parameter : Real =>
          (data.operatorFrame representation coordinates refinement pullback).frame
            parameter (data.baseKernelBasis index).1)) :
    DifferentiableFiniteKernelBasisFamilyData operator Index where
  kernels := toFiniteKernelBasisFamilyData representation coordinates refinement
    pullback data
  vector_differentiable := by
    intro index
    have hFunction :
        (fun parameter : Real =>
          (toFiniteKernelBasisFamilyData representation coordinates refinement
            pullback data).vector parameter index) =
        (fun parameter : Real =>
          (data.operatorFrame representation coordinates refinement pullback).frame
            parameter (data.baseKernelBasis index).1) := by
      funext parameter
      exact toFiniteKernelBasisFamilyData_vector_eq_operatorFrame representation
        coordinates refinement pullback data parameter index
    rw [hFunction]
    exact operatorFrame_vector_differentiable index

@[simp]
theorem toDifferentiableFiniteKernelBasisFamilyData_vector
    [Fintype Index] [DecidableEq Index]
    (operatorFrame_vector_differentiable : ∀ index,
      Differentiable Real
        (fun parameter : Real =>
          (data.operatorFrame representation coordinates refinement pullback).frame
            parameter (data.baseKernelBasis index).1))
    (parameter : Real) (index : Index) :
    (toDifferentiableFiniteKernelBasisFamilyData representation coordinates
        refinement pullback data operatorFrame_vector_differentiable).kernels.vector
        parameter index =
      data.transportedKernelVector representation coordinates refinement
        pullback parameter index := by
  exact toFiniteKernelBasisFamilyData_vector representation coordinates
    refinement pullback data parameter index

/-- Public differentiable true-kernel-family checkpoint. -/
theorem five_sector_l2_admissible_frame_differentiable_kernel_basis_family_gate
    [Fintype Index] [DecidableEq Index]
    (operatorFrame_vector_differentiable : ∀ index,
      Differentiable Real
        (fun parameter : Real =>
          (data.operatorFrame representation coordinates refinement pullback).frame
            parameter (data.baseKernelBasis index).1)) :
    let kernels := toDifferentiableFiniteKernelBasisFamilyData representation
      coordinates refinement pullback data operatorFrame_vector_differentiable
    (∀ index,
      Differentiable Real
        (fun parameter : Real => kernels.kernels.vector parameter index)) ∧
    (∀ index,
      Continuous
        (fun parameter : Real => kernels.kernels.vector parameter index)) ∧
    (∀ parameter index,
      operator parameter (kernels.kernels.vector parameter index) = 0) ∧
    (∀ first second index,
      kernels.kernels.kernelTransport first second
          (kernels.kernels.basis first index) =
        kernels.kernels.basis second index) := by
  dsimp only
  exact differentiable_finite_kernel_basis_family_gate operator
    (toDifferentiableFiniteKernelBasisFamilyData representation coordinates
      refinement pullback data operatorFrame_vector_differentiable)

/-- Terminal C1 true-kernel checkpoint: the standard differentiable family,
complete spanning, and global Gram regularity come from the same transported
basis. -/
theorem five_sector_l2_admissible_frame_differentiable_true_kernel_global_gate
    [Fintype Index] [DecidableEq Index]
    (operatorFrame_vector_differentiable : ∀ index,
      Differentiable Real
        (fun parameter : Real =>
          (data.operatorFrame representation coordinates refinement pullback).frame
            parameter (data.baseKernelBasis index).1)) :
    let kernels := toDifferentiableFiniteKernelBasisFamilyData representation
      coordinates refinement pullback data operatorFrame_vector_differentiable
    (∀ index,
      Differentiable Real
        (fun parameter : Real => kernels.kernels.vector parameter index)) ∧
    (∀ parameter,
      Submodule.span Real
          (Set.range
            (data.transportedKernelVector representation coordinates refinement
              pullback parameter)) = ⊤) ∧
    transportedKernelGramRegularSet representation coordinates refinement
        pullback data = Set.univ := by
  dsimp only
  exact
    ⟨(toDifferentiableFiniteKernelBasisFamilyData representation coordinates
        refinement pullback data
        operatorFrame_vector_differentiable).vector_differentiable,
      transportedKernelVector_span_eq_top representation coordinates refinement
        pullback data,
      transportedKernelGramRegularSet_eq_univ representation coordinates
        refinement pullback data⟩

end FiveSectorL2AdmissibleFrameKernelGramData

end

end P0EFTJanusProgramPFiveSectorL2AdmissibleFrameDifferentiableKernelBasisFamilyGlobalBridge4D
end JanusFormal
