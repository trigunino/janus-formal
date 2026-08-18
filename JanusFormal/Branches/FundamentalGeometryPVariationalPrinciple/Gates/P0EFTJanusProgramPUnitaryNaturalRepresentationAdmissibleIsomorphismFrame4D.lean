import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

/-!
# Unitary represented frame from admissible D11 isomorphisms

A represented basepoint D11 frame already gives a linear equivalence `F_a` and
proves `H_a F_a = F_a H_0` together with preservation of the five physical
sectors.  To transport the canonical orthogonal complements, one additional
metric statement is required:

`‖F_a x‖ = ‖x‖`.

This file upgrades the represented linear frame to a linear isometric
equivalence and exports the generic unitary operator-frame packet.  No separate
complement map is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

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

/-- A represented admissible-isomorphism frame whose reverse pullback preserves
the Hilbert norm. -/
structure UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
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
  linearFrame : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
    representation coordinates refinement pullback
  reverse_norm_map : ∀ parameter state,
    ‖linearFrame.reverseLinear parameter state‖ = ‖state‖

namespace UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData

/-- The represented reverse pullback as a linear isometric equivalence. -/
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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) : State ≃ₗᵢ[Real] State where
  __ := data.linearFrame.frame representation coordinates refinement pullback
    parameter
  norm_map' := data.reverse_norm_map parameter

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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) (state : State) :
    data.frame representation coordinates refinement pullback parameter state =
      data.linearFrame.reverseLinear parameter state :=
  rfl

/-- The represented unitary frame is the identity at H12. -/
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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback) :
    data.frame representation coordinates refinement pullback 0 =
      LinearIsometryEquiv.refl Real State := by
  ext state
  exact congrArg
    (fun equivalence => equivalence state)
    (data.linearFrame.frame_zero representation coordinates refinement pullback)

/-- D11 naturality gives the unitary frame/operator intertwining equation. -/
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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) (state : State) :
    operator parameter
        (data.frame representation coordinates refinement pullback parameter state) =
      data.frame representation coordinates refinement pullback parameter
        (operator 0 state) :=
  data.linearFrame.frame_intertwines representation coordinates refinement
    pullback parameter state

/-- The unitary represented frame preserves all five physical projectors. -/
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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (parameter : Real) (sector : FivePhysicalSector) (state : State) :
    data.frame representation coordinates refinement pullback parameter
        (coordinates.sectorProjector sector state) =
      coordinates.sectorProjector sector
        (data.frame representation coordinates refinement pullback parameter
          state) :=
  data.linearFrame.frame_commutes_sectorProjector representation coordinates
    refinement pullback parameter sector state

/-- Adapter to the generic unitary operator-frame packet. -/
def toFiniteUnitaryIntertwiningOperatorFrame
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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback) :
    FiniteUnitaryIntertwiningOperatorFrameData operator where
  frame := data.frame representation coordinates refinement pullback
  frame_zero := data.frame_zero representation coordinates refinement pullback
  intertwines_basepoint := data.frame_intertwines representation coordinates
    refinement pullback

/-- Public unitary represented-frame checkpoint. -/
theorem unitary_natural_representation_admissible_isomorphism_frame_gate
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
    (data : UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback) :
    (∀ parameter state,
      ‖data.frame representation coordinates refinement pullback parameter state‖ =
        ‖state‖) ∧
    (∀ parameter state,
      operator parameter
          (data.frame representation coordinates refinement pullback parameter
            state) =
        data.frame representation coordinates refinement pullback parameter
          (operator 0 state)) ∧
    (∀ parameter sector state,
      data.frame representation coordinates refinement pullback parameter
          (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector
          (data.frame representation coordinates refinement pullback parameter
            state)) ∧
    Nonempty (FiniteUnitaryIntertwiningOperatorFrameData operator) :=
  ⟨fun parameter state =>
      (data.frame representation coordinates refinement pullback parameter).norm_map state,
    data.frame_intertwines representation coordinates refinement pullback,
    data.frame_commutes_sectorProjector representation coordinates refinement
      pullback,
    ⟨data.toFiniteUnitaryIntertwiningOperatorFrame representation coordinates
      refinement pullback⟩⟩

end UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData

end
end P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
end JanusFormal
