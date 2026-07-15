import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge

/-!
The M30 cross densities are published only symbolically, and no complete
GHY/null/worldvolume boundary functional is supplied. This gate therefore
audits one explicit reduced candidate; it does not attribute that candidate to
the published Janus action.
-/

namespace JanusFormal
namespace P0EFTJanusReducedTwoMetricBoundaryFirstVariation

set_option autoImplicit false

noncomputable section

open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusPTFlatBimetricVariationalBridge

/-- Two independent positive- and negative-sheet scale modes. This is a
finite-dimensional candidate sector, not the full space of Janus metrics. -/
abbrev ScalePair := ℝ × ℝ

/-- Affine variation through a two-scale background. -/
def affineVariation
    (scale variation : ScalePair) (t : ℝ) : ScalePair :=
  (scale.1 + t * variation.1, scale.2 + t * variation.2)

@[simp]
theorem affineVariation_zero
    (scale variation : ScalePair) :
    affineVariation scale variation 0 = scale := by
  simp [affineVariation]

/-- Linear first variation displayed by its independent Euler components. -/
def pairFirstVariation
    (plus minus : ℝ) (variation : ScalePair) : ℝ :=
  plus * variation.1 + minus * variation.2

theorem affineCoordinate_hasDerivAt
    (base variation : ℝ) :
    HasDerivAt (fun t : ℝ => base + t * variation) variation 0 := by
  have h : HasDerivAt (fun t : ℝ => base + t * variation)
      (1 * variation) 0 :=
    (hasDerivAt_id 0).mul_const variation |>.const_add base
  exact h.congr_deriv (one_mul variation)

/-- Explicit quadratic bulk candidate. Its two coefficients only summarize
reduced curvature/matter channels; they are not claimed to be a derivation of
the full Einstein--Hilbert bulk action. -/
def reducedBulkAction
    (bulkPlus bulkMinus : ℝ) (scale : ScalePair) : ℝ :=
  (bulkPlus / 2) * scale.1 ^ 2 +
    (bulkMinus / 2) * scale.2 ^ 2

/-- Homogeneous two-scale lift of the PT-flat relative shape. -/
def homogeneousRelativeShape
    (beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  4 * beta1 * (scale.2 ^ 2 + scale.2 * scale.1 + scale.1 ^ 2) +
    3 * beta2 * (scale.2 + scale.1) ^ 2

/-- Explicit exchange-symmetric homogeneous interaction candidate. -/
def reducedInteractionAction
    (coupling beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  coupling * (scale.2 - scale.1) ^ 2 *
    homogeneousRelativeShape beta1 beta2 scale

/-- Two explicit reduced boundary channels. Their coefficients remain missing
physical data until genuine GHY/null/worldvolume functionals are derived. -/
def reducedBoundaryAction
    (boundaryPlus boundaryMinus : ℝ) (scale : ScalePair) : ℝ :=
  boundaryPlus * scale.1 + boundaryMinus * scale.2

/-- Complete explicit reduced candidate used in this gate. -/
def reducedTwoMetricAction
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) : ℝ :=
  reducedBulkAction bulkPlus bulkMinus scale +
    reducedInteractionAction coupling beta1 beta2 scale +
    reducedBoundaryAction boundaryPlus boundaryMinus scale

/-- Plus derivative of the homogeneous relative shape. -/
def homogeneousRelativeShapePlus
    (beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  4 * beta1 * (scale.2 + 2 * scale.1) +
    6 * beta2 * (scale.2 + scale.1)

/-- Minus derivative of the homogeneous relative shape. -/
def homogeneousRelativeShapeMinus
    (beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  4 * beta1 * (2 * scale.2 + scale.1) +
    6 * beta2 * (scale.2 + scale.1)

/-- Plus interaction Euler component. -/
def interactionEulerPlus
    (coupling beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  coupling *
    (-2 * (scale.2 - scale.1) * homogeneousRelativeShape beta1 beta2 scale +
      (scale.2 - scale.1) ^ 2 *
        homogeneousRelativeShapePlus beta1 beta2 scale)

/-- Minus interaction Euler component. -/
def interactionEulerMinus
    (coupling beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  coupling *
    (2 * (scale.2 - scale.1) * homogeneousRelativeShape beta1 beta2 scale +
      (scale.2 - scale.1) ^ 2 *
        homogeneousRelativeShapeMinus beta1 beta2 scale)

/-- Full plus Euler component: bulk plus interaction plus boundary. -/
def reducedEulerPlus
    (bulkPlus coupling beta1 beta2 boundaryPlus : ℝ)
    (scale : ScalePair) : ℝ :=
  bulkPlus * scale.1 +
    interactionEulerPlus coupling beta1 beta2 scale + boundaryPlus

/-- Full minus Euler component: bulk plus interaction plus boundary. -/
def reducedEulerMinus
    (bulkMinus coupling beta1 beta2 boundaryMinus : ℝ)
    (scale : ScalePair) : ℝ :=
  bulkMinus * scale.2 +
    interactionEulerMinus coupling beta1 beta2 scale + boundaryMinus

/-- The homogeneous lift restricts exactly to the audited proportional
interaction, rather than merely agreeing to low order. -/
theorem reducedInteractionAction_on_unit_plus
    (coupling beta1 beta2 c : ℝ) :
    reducedInteractionAction coupling beta1 beta2 (1, c) =
      coupling * proportionalInteractionEnergy beta1 beta2 c := by
  rw [interaction_energy_factorization]
  unfold reducedInteractionAction homogeneousRelativeShape relativeShape
  ring

/-- The explicit interaction candidate is invariant under sheet exchange. -/
theorem reducedInteractionAction_exchange
    (coupling beta1 beta2 : ℝ) (scale : ScalePair) :
    reducedInteractionAction coupling beta1 beta2 scale.swap =
      reducedInteractionAction coupling beta1 beta2 scale := by
  rcases scale with ⟨scalePlus, scaleMinus⟩
  simp [reducedInteractionAction, homogeneousRelativeShape, Prod.swap]
  ring

theorem reducedBulkAction_line_hasDerivAt
    (bulkPlus bulkMinus : ℝ) (scale variation : ScalePair) :
    HasDerivAt
      (fun t => reducedBulkAction bulkPlus bulkMinus
        (affineVariation scale variation t))
      (pairFirstVariation
        (bulkPlus * scale.1) (bulkMinus * scale.2) variation) 0 := by
  have hPlus : HasDerivAt
      (fun t : ℝ => scale.1 + t * variation.1) variation.1 0 := by
    exact affineCoordinate_hasDerivAt scale.1 variation.1
  have hMinus : HasDerivAt
      (fun t : ℝ => scale.2 + t * variation.2) variation.2 0 := by
    exact affineCoordinate_hasDerivAt scale.2 variation.2
  have hDerivative :=
    ((hPlus.pow 2).const_mul (bulkPlus / 2)).add
      ((hMinus.pow 2).const_mul (bulkMinus / 2))
  refine (hDerivative.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · norm_num [pairFirstVariation]
    ring
  · intro t
    simp [affineVariation, reducedBulkAction]

theorem homogeneousRelativeShape_line_hasDerivAt
    (beta1 beta2 : ℝ) (scale variation : ScalePair) :
    HasDerivAt
      (fun t => homogeneousRelativeShape beta1 beta2
        (affineVariation scale variation t))
      (pairFirstVariation
        (homogeneousRelativeShapePlus beta1 beta2 scale)
        (homogeneousRelativeShapeMinus beta1 beta2 scale) variation) 0 := by
  have hPlus : HasDerivAt
      (fun t : ℝ => scale.1 + t * variation.1) variation.1 0 := by
    exact affineCoordinate_hasDerivAt scale.1 variation.1
  have hMinus : HasDerivAt
      (fun t : ℝ => scale.2 + t * variation.2) variation.2 0 := by
    exact affineCoordinate_hasDerivAt scale.2 variation.2
  have hFirst :=
    ((hMinus.pow 2).add (hMinus.mul hPlus)).add (hPlus.pow 2)
  have hSecond := (hMinus.add hPlus).pow 2
  have hDerivative :=
    (hFirst.const_mul (4 * beta1)).add
      (hSecond.const_mul (3 * beta2))
  refine (hDerivative.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · norm_num [pairFirstVariation, homogeneousRelativeShapePlus,
      homogeneousRelativeShapeMinus]
    ring
  · intro t
    simp [affineVariation, homogeneousRelativeShape]

/-- Genuine derivative of the interaction along every independent affine
two-metric variation. -/
theorem reducedInteractionAction_line_hasDerivAt
    (coupling beta1 beta2 : ℝ) (scale variation : ScalePair) :
    HasDerivAt
      (fun t => reducedInteractionAction coupling beta1 beta2
        (affineVariation scale variation t))
      (pairFirstVariation
        (interactionEulerPlus coupling beta1 beta2 scale)
        (interactionEulerMinus coupling beta1 beta2 scale) variation) 0 := by
  have hPlus : HasDerivAt
      (fun t : ℝ => scale.1 + t * variation.1) variation.1 0 := by
    exact affineCoordinate_hasDerivAt scale.1 variation.1
  have hMinus : HasDerivAt
      (fun t : ℝ => scale.2 + t * variation.2) variation.2 0 := by
    exact affineCoordinate_hasDerivAt scale.2 variation.2
  have hDifference := hMinus.sub hPlus
  have hShape := homogeneousRelativeShape_line_hasDerivAt
    beta1 beta2 scale variation
  have hDerivative := (hDifference.pow 2).mul hShape |>.const_mul coupling
  refine (hDerivative.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · norm_num [affineVariation, pairFirstVariation, interactionEulerPlus,
      interactionEulerMinus]
    ring
  · intro t
    simp [affineVariation, reducedInteractionAction]
    ring

theorem reducedBoundaryAction_line_hasDerivAt
    (boundaryPlus boundaryMinus : ℝ) (scale variation : ScalePair) :
    HasDerivAt
      (fun t => reducedBoundaryAction boundaryPlus boundaryMinus
        (affineVariation scale variation t))
      (pairFirstVariation boundaryPlus boundaryMinus variation) 0 := by
  have hPlus : HasDerivAt
      (fun t : ℝ => scale.1 + t * variation.1) variation.1 0 := by
    exact affineCoordinate_hasDerivAt scale.1 variation.1
  have hMinus : HasDerivAt
      (fun t : ℝ => scale.2 + t * variation.2) variation.2 0 := by
    exact affineCoordinate_hasDerivAt scale.2 variation.2
  have hDerivative :=
    (hPlus.const_mul boundaryPlus).add (hMinus.const_mul boundaryMinus)
  refine (hDerivative.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · rfl
  · intro t
    simp [affineVariation, reducedBoundaryAction]

/-- Joint Frechet differentiability of the explicit polynomial candidate. -/
theorem reducedTwoMetricAction_hasFDerivAt_canonical
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) :
    HasFDerivAt
      (reducedTwoMetricAction bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus)
      (fderiv ℝ
        (reducedTwoMetricAction bulkPlus bulkMinus coupling beta1 beta2
          boundaryPlus boundaryMinus) scale) scale := by
  apply DifferentiableAt.hasFDerivAt
  unfold reducedTwoMetricAction reducedBulkAction reducedInteractionAction
    homogeneousRelativeShape reducedBoundaryAction
  fun_prop

/-- Actual first variation of the complete candidate along every affine
variation, with bulk, interaction and boundary contributions explicit. -/
theorem reducedTwoMetricAction_line_hasDerivAt
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale variation : ScalePair) :
    HasDerivAt
      (fun t => reducedTwoMetricAction bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus (affineVariation scale variation t))
      (pairFirstVariation
        (reducedEulerPlus bulkPlus coupling beta1 beta2 boundaryPlus scale)
        (reducedEulerMinus bulkMinus coupling beta1 beta2 boundaryMinus scale)
        variation) 0 := by
  have hBulk := reducedBulkAction_line_hasDerivAt
    bulkPlus bulkMinus scale variation
  have hInteraction := reducedInteractionAction_line_hasDerivAt
    coupling beta1 beta2 scale variation
  have hBoundary := reducedBoundaryAction_line_hasDerivAt
    boundaryPlus boundaryMinus scale variation
  have hDerivative := (hBulk.add hInteraction).add hBoundary
  refine (hDerivative.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  · unfold pairFirstVariation reducedEulerPlus reducedEulerMinus
    ring
  · intro t
    simp [reducedTwoMetricAction]

/-- Actual stationarity under all independent reduced metric variations. -/
def ReducedStationaryAt
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) : Prop :=
  ∀ variation,
    HasDerivAt
      (fun t => reducedTwoMetricAction bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus (affineVariation scale variation t))
      0 0

/-- Exact stationarity criterion for independent plus/minus variations. -/
theorem reduced_stationarity_iff_euler_components_zero
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus : ℝ)
    (scale : ScalePair) :
    ReducedStationaryAt bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus scale ↔
      reducedEulerPlus bulkPlus coupling beta1 beta2 boundaryPlus scale = 0 ∧
      reducedEulerMinus bulkMinus coupling beta1 beta2 boundaryMinus scale = 0 := by
  constructor
  · intro hStationary
    constructor
    · have hDisplayed := reducedTwoMetricAction_line_hasDerivAt
        bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus
        scale (1, 0)
      have hUnique := hDisplayed.unique (hStationary (1, 0))
      simpa [pairFirstVariation] using hUnique
    · have hDisplayed := reducedTwoMetricAction_line_hasDerivAt
        bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus
        scale (0, 1)
      have hUnique := hDisplayed.unique (hStationary (0, 1))
      simpa [pairFirstVariation] using hUnique
  · rintro ⟨hPlus, hMinus⟩ variation
    simpa [hPlus, hMinus, pairFirstVariation] using
      reducedTwoMetricAction_line_hasDerivAt
        bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus
        scale variation

@[simp]
theorem interactionEulerPlus_symmetric
    (coupling beta1 beta2 r : ℝ) :
    interactionEulerPlus coupling beta1 beta2 (r, r) = 0 := by
  simp [interactionEulerPlus]

@[simp]
theorem interactionEulerMinus_symmetric
    (coupling beta1 beta2 r : ℝ) :
    interactionEulerMinus coupling beta1 beta2 (r, r) = 0 := by
  simp [interactionEulerMinus]

/-- At equal scales, exact stationarity is precisely balance of each bulk
channel by its boundary channel. -/
theorem symmetric_stationarity_iff_boundary_balance
    (bulkPlus bulkMinus coupling beta1 beta2 boundaryPlus boundaryMinus r : ℝ) :
    ReducedStationaryAt bulkPlus bulkMinus coupling beta1 beta2
        boundaryPlus boundaryMinus (r, r) ↔
      boundaryPlus = -(bulkPlus * r) ∧
      boundaryMinus = -(bulkMinus * r) := by
  rw [reduced_stationarity_iff_euler_components_zero]
  simp [reducedEulerPlus, reducedEulerMinus]
  constructor <;> rintro ⟨hPlus, hMinus⟩
  · constructor <;> linarith
  · constructor <;> linarith

def stationarizingBoundaryPlus
    (bulkPlus coupling beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  -(bulkPlus * scale.1 + interactionEulerPlus coupling beta1 beta2 scale)

def stationarizingBoundaryMinus
    (bulkMinus coupling beta1 beta2 : ℝ) (scale : ScalePair) : ℝ :=
  -(bulkMinus * scale.2 + interactionEulerMinus coupling beta1 beta2 scale)

/-- Missing-boundary obstruction: every scale pair can be made stationary by
some linear boundary channel. Thus the reduced bulk-plus-interaction candidate
cannot select a Janus scale before the physical boundary functional is fixed. -/
theorem unspecified_boundary_can_stationarize_any_scale_pair
    (bulkPlus bulkMinus coupling beta1 beta2 : ℝ) (scale : ScalePair) :
    ReducedStationaryAt bulkPlus bulkMinus coupling beta1 beta2
      (stationarizingBoundaryPlus bulkPlus coupling beta1 beta2 scale)
      (stationarizingBoundaryMinus bulkMinus coupling beta1 beta2 scale)
      scale := by
  rw [reduced_stationarity_iff_euler_components_zero]
  constructor <;>
    simp [reducedEulerPlus, reducedEulerMinus,
      stationarizingBoundaryPlus, stationarizingBoundaryMinus]

end

end P0EFTJanusReducedTwoMetricBoundaryFirstVariation
end JanusFormal
