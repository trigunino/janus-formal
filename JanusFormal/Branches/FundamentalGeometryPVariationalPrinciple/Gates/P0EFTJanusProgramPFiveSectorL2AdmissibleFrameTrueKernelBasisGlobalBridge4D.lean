import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelBasisFamily4D

/-!
# Global true-kernel basis from an admissible L² frame

The admissible frame restricts to an equivalence of the complete kernels.
Mapping the base-kernel basis through that equivalence therefore gives a basis,
not merely an independent family, at every parameter.  Hence there are no
hidden kernel modes anywhere on the real parameter line.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData

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

/-- The transported base basis is a basis of the complete true kernel. -/
def transportedTrueKernelBasis (parameter : Real) :
    Module.Basis Index Real (operator parameter).ker :=
  data.baseKernelBasis.map
    (data.kernelTransport representation coordinates refinement pullback parameter)

@[simp]
theorem transportedTrueKernelBasis_apply
    (parameter : Real) (index : Index) :
    transportedTrueKernelBasis representation coordinates refinement pullback
        data parameter index =
      data.transportedKernelVector representation coordinates refinement
        pullback parameter index := by
  rfl

/-- The transported true-kernel bases form the standard fixed-label kernel
family. -/
def toFiniteKernelBasisFamilyData
    [Fintype Index] [DecidableEq Index] :
    FiniteKernelBasisFamilyData operator Index where
  basis := transportedTrueKernelBasis representation coordinates refinement
    pullback data

@[simp]
theorem toFiniteKernelBasisFamilyData_vector
    [Fintype Index] [DecidableEq Index]
    (parameter : Real) (index : Index) :
    (toFiniteKernelBasisFamilyData representation coordinates refinement
        pullback data).vector parameter index =
      data.transportedKernelVector representation coordinates refinement
        pullback parameter index := by
  rfl

/-- Public adapter to the standard finite-kernel-family API. -/
theorem five_sector_l2_admissible_frame_finite_kernel_basis_family_gate
    [Fintype Index] [DecidableEq Index] :
    let kernels := toFiniteKernelBasisFamilyData representation coordinates
      refinement pullback data
    (∀ parameter index,
      operator parameter (kernels.vector parameter index) = 0) ∧
    (∀ first second index,
      kernels.kernelTransport first second (kernels.basis first index) =
        kernels.basis second index) ∧
    (∀ first second third,
      (kernels.kernelTransport first second).trans
          (kernels.kernelTransport second third) =
        kernels.kernelTransport first third) ∧
    (∀ parameter,
      Module.finrank Real (operator parameter).ker = Fintype.card Index) := by
  dsimp only
  exact (toFiniteKernelBasisFamilyData representation coordinates refinement
    pullback data).finite_kernel_basis_family_gate operator

/-- The transported named vectors span the whole true kernel; no additional
kernel mode can appear at any parameter. -/
theorem transportedKernelVector_span_eq_top (parameter : Real) :
    Submodule.span Real
        (Set.range
          (data.transportedKernelVector representation coordinates refinement
            pullback parameter)) = ⊤ := by
  have hFamily :
      data.transportedKernelVector representation coordinates refinement
          pullback parameter =
        transportedTrueKernelBasis representation coordinates refinement
          pullback data parameter := by
    funext index
    exact (transportedTrueKernelBasis_apply representation coordinates
      refinement pullback data parameter index).symm
  rw [hFamily]
  exact (transportedTrueKernelBasis representation coordinates refinement
    pullback data parameter).span_eq

/-- Public full-kernel closure together with global Gram regularity. -/
theorem five_sector_l2_admissible_frame_true_kernel_global_gate
    [Fintype Index] [DecidableEq Index] :
    (∀ parameter,
      Submodule.span Real
          (Set.range
            (data.transportedKernelVector representation coordinates refinement
              pullback parameter)) = ⊤) ∧
    transportedKernelGramRegularSet representation coordinates refinement
        pullback data = Set.univ :=
  ⟨transportedKernelVector_span_eq_top representation coordinates refinement
      pullback data,
    transportedKernelGramRegularSet_eq_univ representation coordinates
      refinement pullback data⟩

end FiveSectorL2AdmissibleFrameKernelGramData

end

end P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D
end JanusFormal
