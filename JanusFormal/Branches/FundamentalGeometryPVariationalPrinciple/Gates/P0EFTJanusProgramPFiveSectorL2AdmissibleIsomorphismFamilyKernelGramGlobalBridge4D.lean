import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D

/-!
# D11 admissible-isomorphism families to global L² kernel Gram data

A coherent pairwise D11 isomorphism family restricts at the basepoint to the
admissible frame consumed by the L² kernel-Gram bridge.  The only additional
geometric inputs are the identified L² coordinates and a genuine base-kernel
basis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2AdmissibleIsomorphismFamilyKernelGramGlobalBridge4D

set_option autoImplicit false

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData

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

/-- Restriction of a pairwise D11 isomorphism family to its basepoint frame. -/
def admissibleIsomorphismFamilyToFrameData
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback) :
    LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback where
  isomorphismAt := fun parameter => isomorphisms.isomorphism 0 parameter
  isomorphism_zero_inv := isomorphisms.isomorphism_self_inv 0
  reverseLinear := fun parameter => isomorphisms.reverseLinear 0 parameter
  forwardLinear := fun parameter => isomorphisms.forwardLinear 0 parameter
  reverse_source_agreement := fun parameter state =>
    isomorphisms.reverse_source_agreement 0 parameter state
  forward_source_agreement := fun parameter state =>
    isomorphisms.forward_source_agreement 0 parameter state
  reverse_target_agreement := fun parameter state =>
    isomorphisms.reverse_target_agreement 0 parameter state

/-- Package a D11 family with the honest L² coordinates and base-kernel
basis required by the global Gram bridge. -/
def admissibleIsomorphismFamilyKernelGramData
    (l2Coordinates : FiveSectorL2HilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (projector_eq : ∀ sector,
      coordinates.sectorProjector sector =
        l2Coordinates.sectorProjector (fivePhysicalSectorL2SlotEquiv sector))
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (baseKernelBasis : Module.Basis Index Real (operator 0).ker) :
    FiveSectorL2AdmissibleFrameKernelGramData
      (Index := Index) representation coordinates refinement pullback where
  l2Coordinates := l2Coordinates
  projector_eq := projector_eq
  frameData := admissibleIsomorphismFamilyToFrameData representation coordinates
    refinement pullback isomorphisms
  baseKernelBasis := baseKernelBasis

/-- Public direct D11-family-to-global-Gram checkpoint. -/
theorem five_sector_l2_admissible_isomorphism_family_global_gram_gate
    (l2Coordinates : FiveSectorL2HilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (projector_eq : ∀ sector,
      coordinates.sectorProjector sector =
        l2Coordinates.sectorProjector (fivePhysicalSectorL2SlotEquiv sector))
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (baseKernelBasis : Module.Basis Index Real (operator 0).ker) :
    let gramData := admissibleIsomorphismFamilyKernelGramData representation
      coordinates refinement pullback l2Coordinates projector_eq isomorphisms
        baseKernelBasis
    (∀ parameter,
      Function.Injective
        (transportedKernelGramMap representation coordinates refinement pullback
          gramData parameter)) ∧
    transportedKernelGramRegularSet representation coordinates refinement
        pullback gramData = Set.univ := by
  dsimp only
  exact five_sector_l2_admissible_frame_global_gram_gate representation
    coordinates refinement pullback
      (admissibleIsomorphismFamilyKernelGramData representation coordinates
        refinement pullback l2Coordinates projector_eq isomorphisms
          baseKernelBasis)

end
end P0EFTJanusProgramPFiveSectorL2AdmissibleIsomorphismFamilyKernelGramGlobalBridge4D
end JanusFormal
