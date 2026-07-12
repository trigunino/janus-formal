import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwoMetricFirstVariation

set_option autoImplicit false

variable {VPlus VMinus : Type*}
variable [AddCommMonoid VPlus] [Module ℝ VPlus]
variable [AddCommMonoid VMinus] [Module ℝ VMinus]

/-- Total first variation for two independent metric variations. -/
def totalFirstVariation
    (equationPlus : VPlus →ₗ[ℝ] ℝ)
    (equationMinus : VMinus →ₗ[ℝ] ℝ)
    (variationPlus : VPlus)
    (variationMinus : VMinus) : ℝ :=
  equationPlus variationPlus + equationMinus variationMinus

/--
Stationarity under all independent variations is equivalent to vanishing of
both Euler-Lagrange linear functionals.
-/
theorem independent_metric_variations_split
    (equationPlus : VPlus →ₗ[ℝ] ℝ)
    (equationMinus : VMinus →ₗ[ℝ] ℝ)
    (hStationary :
      ∀ variationPlus variationMinus,
        totalFirstVariation equationPlus equationMinus
          variationPlus variationMinus = 0) :
    equationPlus = 0 /\ equationMinus = 0 := by
  constructor
  · ext variationPlus
    have h := hStationary variationPlus 0
    simpa [totalFirstVariation] using h
  · ext variationMinus
    have h := hStationary 0 variationMinus
    simpa [totalFirstVariation] using h

/-- The converse: two Euler-Lagrange equations imply total stationarity. -/
theorem split_equations_imply_total_stationarity
    (equationPlus : VPlus →ₗ[ℝ] ℝ)
    (equationMinus : VMinus →ₗ[ℝ] ℝ)
    (hPlus : equationPlus = 0)
    (hMinus : equationMinus = 0) :
    ∀ variationPlus variationMinus,
      totalFirstVariation equationPlus equationMinus
        variationPlus variationMinus = 0 := by
  intro variationPlus variationMinus
  simp [totalFirstVariation, hPlus, hMinus]

/-- Bulk plus boundary first variation for one metric sector. -/
def sectorFirstVariation
    (bulk boundary : VPlus →ₗ[ℝ] ℝ) : VPlus →ₗ[ℝ] ℝ :=
  bulk + boundary

/-- Bulk equations alone do not close the variational problem if a boundary term remains. -/
theorem nonzero_boundary_variation_blocks_full_stationarity
    (bulk boundary : VPlus →ₗ[ℝ] ℝ)
    (hBulk : bulk = 0)
    (hBoundary : boundary ≠ 0) :
    sectorFirstVariation bulk boundary ≠ 0 := by
  intro hTotal
  apply hBoundary
  simpa [sectorFirstVariation, hBulk] using hTotal

/--
A complete nonlinear Janus action must include all bulk, cross-sector and
boundary functionals before its field and junction equations can be claimed as
Euler-Lagrange consequences.
-/
structure CompleteTwoMetricActionStatus where
  plusEinsteinHilbertDefined : Prop
  minusEinsteinHilbertDefined : Prop
  relativeKineticSignFixed : Prop
  plusMatterActionDefined : Prop
  minusMatterActionDefined : Prop
  singleCommonCrossInteractionDefined : Prop
  diagonalDiffeomorphismInvariant : Prop
  plusBoundaryTermDefined : Prop
  minusBoundaryTermDefined : Prop
  nullBoundaryTermDefined : Prop
  llBraneWorldvolumeActionDefined : Prop
  independentMetricVariationsDerived : Prop
  interactionFieldEquationsDerived : Prop
  boundaryJunctionEquationsDerived : Prop
  nonlinearConstraintAlgebraClosed : Prop
  stableBranchSelected : Prop


def completeTwoMetricActionClosed
    (s : CompleteTwoMetricActionStatus) : Prop :=
  s.plusEinsteinHilbertDefined /\
  s.minusEinsteinHilbertDefined /\
  s.relativeKineticSignFixed /\
  s.plusMatterActionDefined /\
  s.minusMatterActionDefined /\
  s.singleCommonCrossInteractionDefined /\
  s.diagonalDiffeomorphismInvariant /\
  s.plusBoundaryTermDefined /\
  s.minusBoundaryTermDefined /\
  s.nullBoundaryTermDefined /\
  s.llBraneWorldvolumeActionDefined /\
  s.independentMetricVariationsDerived /\
  s.interactionFieldEquationsDerived /\
  s.boundaryJunctionEquationsDerived /\
  s.nonlinearConstraintAlgebraClosed /\
  s.stableBranchSelected

end P0EFTJanusTwoMetricFirstVariation
end JanusFormal
