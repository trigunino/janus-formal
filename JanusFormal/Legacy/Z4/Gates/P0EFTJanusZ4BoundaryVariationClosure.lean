import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LinearizedActionVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DeterminantMeasureVariation

namespace JanusFormal
namespace P0EFTJanusZ4BoundaryVariationClosure

set_option autoImplicit false

abbrev LinearizedActionVariation :=
  P0EFTJanusZ4LinearizedActionVariation.LinearizedActionVariation

abbrev DeterminantMeasureVariation :=
  P0EFTJanusZ4DeterminantMeasureVariation.DeterminantMeasureVariation

structure BoundaryVariationClosure where
  membraneBoundaryFunctionalDeclared : Prop
  linearizedBulkBoundaryResidualMatched : Prop
  determinantMeasureBoundaryResidualMatched : Prop
  orientationSignsFixed : Prop
  noIndependentSecondMetricIntroduced : Prop
  nonlinearBoundaryVariationClosed : Prop

def boundaryVariationScaffoldReady (b : BoundaryVariationClosure) : Prop :=
  b.membraneBoundaryFunctionalDeclared /\
  b.linearizedBulkBoundaryResidualMatched /\
  b.determinantMeasureBoundaryResidualMatched /\
  b.orientationSignsFixed /\
  b.noIndependentSecondMetricIntroduced

def boundaryPromotesLinearizedAction
    (b : BoundaryVariationClosure)
    (v : LinearizedActionVariation)
    (m : DeterminantMeasureVariation) : Prop :=
  boundaryVariationScaffoldReady b /\
  P0EFTJanusZ4LinearizedActionVariation.linearizedActionVariationReady v /\
  P0EFTJanusZ4DeterminantMeasureVariation.measureVariationScaffoldReady m

def fullBoundaryActionClosure
    (b : BoundaryVariationClosure)
    (v : LinearizedActionVariation)
    (m : DeterminantMeasureVariation) : Prop :=
  boundaryPromotesLinearizedAction b v m /\
  b.nonlinearBoundaryVariationClosed /\
  v.nonlinearActionVariationClosed

theorem boundary_scaffold_preserves_single_z4_geometry
    (b : BoundaryVariationClosure)
    (h : boundaryVariationScaffoldReady b) :
    b.noIndependentSecondMetricIntroduced := by
  exact h.right.right.right.right

theorem boundary_scaffold_does_not_close_full_action
    (b : BoundaryVariationClosure)
    (v : LinearizedActionVariation)
    (m : DeterminantMeasureVariation)
    (_h : boundaryPromotesLinearizedAction b v m)
    (hMissing : Not b.nonlinearBoundaryVariationClosed) :
    Not (fullBoundaryActionClosure b v m) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusZ4BoundaryVariationClosure
end JanusFormal
