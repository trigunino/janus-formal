import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

/-!
# Sector commutation transported by a represented D11 frame

Basepoint sector commutation, frame/operator intertwining and frame/projector
commutation transport the same commutation identity to every parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrameCommuting4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

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

/-- A sector commutation identity at the basepoint propagates along any
sector-preserving represented D11 frame. -/
theorem operator_commutes_sectorProjector_of_basepoint_frame
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
    (frameData : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (baseCommutes : ∀ sector state,
      operator 0 (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector (operator 0 state))
    (parameter : Real) (sector : FivePhysicalSector) (state : State) :
    operator parameter (coordinates.sectorProjector sector state) =
      coordinates.sectorProjector sector (operator parameter state) := by
  let frame := frameData.frame representation coordinates refinement pullback
    parameter
  let baseState := frame.symm state
  have hState : frame baseState = state := frame.apply_symm_apply state
  rw [← hState]
  calc
    operator parameter (coordinates.sectorProjector sector (frame baseState)) =
        operator parameter
          (frame (coordinates.sectorProjector sector baseState)) := by
      rw [frameData.frame_commutes_sectorProjector representation coordinates
        refinement pullback]
    _ = frame
        (operator 0 (coordinates.sectorProjector sector baseState)) :=
      frameData.frame_intertwines representation coordinates refinement pullback
        parameter (coordinates.sectorProjector sector baseState)
    _ = frame (coordinates.sectorProjector sector (operator 0 baseState)) := by
      rw [baseCommutes]
    _ = coordinates.sectorProjector sector (frame (operator 0 baseState)) :=
      frameData.frame_commutes_sectorProjector representation coordinates
        refinement pullback parameter sector (operator 0 baseState)
    _ = coordinates.sectorProjector sector
        (operator parameter (frame baseState)) := by
      rw [frameData.frame_intertwines representation coordinates refinement
        pullback]

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrameCommuting4D
end JanusFormal
