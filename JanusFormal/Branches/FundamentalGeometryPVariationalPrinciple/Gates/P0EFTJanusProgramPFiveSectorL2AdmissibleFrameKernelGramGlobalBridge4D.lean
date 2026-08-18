import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramInjectivity4D

/-!
# Global Gram nondegeneracy from an admissible L² frame

The admissible frame transports one genuine base-kernel basis through linear
equivalences.  Hence its finite synthesis and Gram maps are injective at every
parameter, and the corresponding determinant regular set is all of `Real`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D

variable
  {State Metric Abelian Matter Longitudinal Boundary Index : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  [Fintype Index] [DecidableEq Index]
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

/-- The Gram map of the transported true-kernel basis. -/
def transportedKernelGramMap (parameter : Real) :
    (Index → Real) →ₗ[Real] (Index → Real) :=
  finiteFamilyGramMap
    (data.transportedKernelVector representation coordinates refinement
      pullback parameter)

/-- Every transported coefficient synthesis is injective. -/
theorem transportedKernelSynthesis_injective (parameter : Real) :
    Function.Injective
      (finiteFamilySynthesis
        (data.transportedKernelVector representation coordinates refinement
          pullback parameter)) := by
  intro first second hEqual
  have hDifference :
      finiteFamilySynthesis
          (data.transportedKernelVector representation coordinates refinement
            pullback parameter)
          (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hCoefficientZero :=
    (Fintype.linearIndependent_iff.mp
      (data.transportedKernelVector_linearIndependent representation coordinates
        refinement pullback parameter))
      (first - second) (by
        simpa [finiteFamilySynthesis] using hDifference)
  funext index
  exact sub_eq_zero.mp (hCoefficientZero index)

/-- The transported true-kernel Gram map is injective for every parameter. -/
theorem transportedKernelGramMap_injective (parameter : Real) :
    Function.Injective
      (transportedKernelGramMap representation coordinates refinement pullback
        data parameter) :=
  finiteFamilyGramMap_injective_of_synthesis_injective _
    (transportedKernelSynthesis_injective representation coordinates refinement
      pullback data parameter)

/-- Determinant regular set of the transported true-kernel basis. -/
def transportedKernelGramRegularSet : Set Real :=
  {parameter |
    (Matrix.gram Real
      (data.transportedKernelVector representation coordinates refinement
        pullback parameter)).det ≠ 0}

/-- Linear-equivalence transport makes the Gram regular set global. -/
theorem transportedKernelGramRegularSet_eq_univ :
    transportedKernelGramRegularSet representation coordinates refinement
      pullback data = Set.univ := by
  ext parameter
  simp only [transportedKernelGramRegularSet, Set.mem_setOf_eq, Set.mem_univ,
    iff_true]
  exact data.transportedKernelGram_det_ne_zero representation coordinates
    refinement pullback parameter

/-- Public direct L²-frame-to-global-Gram checkpoint. -/
theorem five_sector_l2_admissible_frame_global_gram_gate :
    (∀ parameter,
      Function.Injective
        (transportedKernelGramMap representation coordinates refinement pullback
          data parameter)) ∧
    transportedKernelGramRegularSet representation coordinates refinement
        pullback data = Set.univ :=
  ⟨transportedKernelGramMap_injective representation coordinates refinement
      pullback data,
    transportedKernelGramRegularSet_eq_univ representation coordinates
      refinement pullback data⟩

end FiveSectorL2AdmissibleFrameKernelGramData

end
end P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
end JanusFormal
