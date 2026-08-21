import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D

/-!
# Metric D11 admissible-isomorphism transport

A represented D11 transport is not automatically isometric.  This file records
the missing metric statement explicitly: every reverse represented pullback
preserves the real Hilbert inner product.  Norm preservation is then derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D

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

/-- Metric compatibility of a represented D11 admissible-isomorphism family.
This is additional geometric data, not a consequence of naturality. -/
structure LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
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
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback) where
  reverse_inner_map : ∀ first second firstState secondState,
    inner Real (isomorphisms.reverseLinear first second firstState)
        (isomorphisms.reverseLinear first second secondState) =
      inner Real firstState secondState

namespace LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData

/-- Inner-product preservation of the reverse represented pullback implies
norm preservation. -/
theorem reverse_norm_map
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
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (metric : LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      representation coordinates refinement pullback isomorphisms)
    (first second : Real) (state : State) :
    ‖isomorphisms.reverseLinear first second state‖ = ‖state‖ := by
  have hInner := metric.reverse_inner_map first second state state
  have hSq :
      ‖isomorphisms.reverseLinear first second state‖ ^ 2 = ‖state‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hInner
  nlinarith [norm_nonneg (isomorphisms.reverseLinear first second state),
    norm_nonneg state]

end LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D
end JanusFormal
