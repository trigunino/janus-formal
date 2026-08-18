import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusAdmissibleMorphismIsomorphism
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteIntertwiningOperatorFrameTransport4D

/-!
# Represented linear frame from basepoint admissible isomorphisms

Pairwise D11 isomorphisms are unnecessary for a global trivialization.  Choose,
for every parameter `a`, one admissible isomorphism from the represented H12
object at `0` to the represented object at `a`.

If forward and reverse represented source pullbacks are real-linear, they are
mutual inverses by functoriality.  Reverse source and target pullback agreement
then makes the reverse pullback a frame `F_a` satisfying

`H_a F_a = F_a H_0`.

The existing sector-covariance theorem also gives `F_a P_s = P_s F_a`.  Thus
this is the minimal represented D11 input for the basepoint-frame continuation
route.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusAdmissibleMorphismIsomorphism
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiniteIntertwiningOperatorFrameTransport4D

variable
  {State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}
  {operator : Real → State →L[Real] State}

/-- Basepoint admissible isomorphisms with linear represented forward and
reverse pullbacks. -/
structure LinearNaturalRepresentationAdmissibleIsomorphismFrameData
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement) where
  isomorphismAt : ∀ parameter,
    AdmissibleIsomorphism immersionCategory
      (representation.objectAt 0) (representation.objectAt parameter)
  isomorphism_zero_inv :
    (isomorphismAt 0).inv =
      admissibleIdentity immersionCategory (representation.objectAt 0)
  reverseLinear : ∀ parameter, State →ₗ[Real] State
  forwardLinear : ∀ parameter, State →ₗ[Real] State
  reverse_source_agreement : ∀ parameter state,
    representation.representedSourcePullback
        (isomorphismAt parameter).inv state =
      reverseLinear parameter state
  forward_source_agreement : ∀ parameter state,
    representation.representedSourcePullback
        (isomorphismAt parameter).hom state =
      forwardLinear parameter state
  reverse_target_agreement : ∀ parameter state,
    representation.representedTargetPullback
        (isomorphismAt parameter).inv state =
      reverseLinear parameter state

namespace LinearNaturalRepresentationAdmissibleIsomorphismFrameData

/-- Reverse represented pullback as a linear equivalence from the H12 frame to
the current parameter. -/
def frame
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) : State ≃ₗ[Real] State where
  toFun := data.reverseLinear parameter
  invFun := data.forwardLinear parameter
  left_inv := by
    intro state
    change data.forwardLinear parameter (data.reverseLinear parameter state) = state
    rw [← data.forward_source_agreement parameter
      (data.reverseLinear parameter state)]
    rw [← data.reverse_source_agreement parameter state]
    rw [← representation.representedSourcePullback_compose
      (data.isomorphismAt parameter).inv
      (data.isomorphismAt parameter).hom state]
    rw [(data.isomorphismAt parameter).inv_hom_id]
    exact representation.representedSourcePullback_identity 0 state
  right_inv := by
    intro state
    change data.reverseLinear parameter (data.forwardLinear parameter state) = state
    rw [← data.reverse_source_agreement parameter
      (data.forwardLinear parameter state)]
    rw [← data.forward_source_agreement parameter state]
    rw [← representation.representedSourcePullback_compose
      (data.isomorphismAt parameter).hom
      (data.isomorphismAt parameter).inv state]
    rw [(data.isomorphismAt parameter).hom_inv_id]
    exact representation.representedSourcePullback_identity parameter state
  map_add' := (data.reverseLinear parameter).map_add
  map_smul' := (data.reverseLinear parameter).map_smul

@[simp]
theorem frame_apply
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) (state : State) :
    data.frame representation coordinates refinement pullback parameter state =
      data.reverseLinear parameter state :=
  rfl

/-- The represented H12 frame is the identity. -/
theorem frame_zero
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback) :
    data.frame representation coordinates refinement pullback 0 =
      LinearEquiv.refl Real State := by
  ext state
  change data.reverseLinear 0 state = state
  rw [← data.reverse_source_agreement 0 state]
  rw [data.isomorphism_zero_inv]
  exact representation.representedSourcePullback_identity 0 state

/-- D11 naturality gives the frame/operator intertwining equation. -/
theorem frame_intertwines
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) (state : State) :
    operator parameter
        (data.frame representation coordinates refinement pullback parameter state) =
      data.frame representation coordinates refinement pullback parameter
        (operator 0 state) := by
  have hNatural := representation.representedOperator_naturality
    (data.isomorphismAt parameter).inv state
  change
    representation.representedTargetPullback
        (data.isomorphismAt parameter).inv (operator 0 state) =
      operator parameter
        (representation.representedSourcePullback
          (data.isomorphismAt parameter).inv state) at hNatural
  calc
    operator parameter
        (data.frame representation coordinates refinement pullback parameter state) =
      operator parameter
        (representation.representedSourcePullback
          (data.isomorphismAt parameter).inv state) := by
        simpa only [frame_apply] using
          (congrArg (operator parameter)
            (data.reverse_source_agreement parameter state)).symm
    _ = representation.representedTargetPullback
          (data.isomorphismAt parameter).inv (operator 0 state) :=
      hNatural.symm
    _ = data.frame representation coordinates refinement pullback parameter
          (operator 0 state) :=
      by simpa only [frame_apply] using
        data.reverse_target_agreement parameter (operator 0 state)

/-- Existing sector covariance gives frame/projector commutation. -/
theorem frame_commutes_sectorProjector
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) (sector : FivePhysicalSector) (state : State) :
    data.frame representation coordinates refinement pullback parameter
        (coordinates.sectorProjector sector state) =
      coordinates.sectorProjector sector
        (data.frame representation coordinates refinement pullback parameter state) := by
  have hSector := pullback.source_commutes
    (data.isomorphismAt parameter).inv sector state
  calc
    data.frame representation coordinates refinement pullback parameter
        (coordinates.sectorProjector sector state) =
      representation.representedSourcePullback
        (data.isomorphismAt parameter).inv
        (coordinates.sectorProjector sector state) :=
      (data.reverse_source_agreement parameter
        (coordinates.sectorProjector sector state)).symm
    _ = coordinates.sectorProjector sector
        (representation.representedSourcePullback
          (data.isomorphismAt parameter).inv state) :=
      hSector.symm
    _ = coordinates.sectorProjector sector
        (data.frame representation coordinates refinement pullback parameter state) := by
      simpa only [frame_apply] using
        congrArg (coordinates.sectorProjector sector)
          (data.reverse_source_agreement parameter state)

/-- Adapter to the generic basepoint operator-frame packet. -/
def toFiniteIntertwiningOperatorFrame
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback) :
    FiniteIntertwiningOperatorFrameData operator where
  frame := data.frame representation coordinates refinement pullback
  frame_zero := data.frame_zero representation coordinates refinement pullback
  intertwines_basepoint := data.frame_intertwines representation coordinates
    refinement pullback

/-- Public represented admissible-isomorphism frame checkpoint. -/
theorem linear_natural_representation_admissible_isomorphism_frame_gate
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
    (data : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback) :
    (∀ parameter,
      Function.LeftInverse (data.forwardLinear parameter)
        (data.reverseLinear parameter)) ∧
    (∀ parameter,
      Function.RightInverse (data.forwardLinear parameter)
        (data.reverseLinear parameter)) ∧
    (∀ parameter state,
      operator parameter
          (data.frame representation coordinates refinement pullback parameter state) =
        data.frame representation coordinates refinement pullback parameter
          (operator 0 state)) ∧
    (∀ parameter sector state,
      data.frame representation coordinates refinement pullback parameter
          (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector
          (data.frame representation coordinates refinement pullback parameter
            state)) ∧
    Nonempty (FiniteIntertwiningOperatorFrameData operator) := by
  refine ⟨?_, ?_,
    data.frame_intertwines representation coordinates refinement pullback,
    data.frame_commutes_sectorProjector representation coordinates refinement
      pullback,
    ⟨data.toFiniteIntertwiningOperatorFrame representation coordinates refinement
      pullback⟩⟩
  · intro parameter state
    exact (data.frame representation coordinates refinement pullback parameter).left_inv state
  · intro parameter state
    exact (data.frame representation coordinates refinement pullback parameter).right_inv state

end LinearNaturalRepresentationAdmissibleIsomorphismFrameData

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
end JanusFormal
