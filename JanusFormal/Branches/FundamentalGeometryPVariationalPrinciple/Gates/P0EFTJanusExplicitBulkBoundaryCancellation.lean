import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusTwoSectorBulkBoundaryFrechetVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLedger
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLocalVariations

/-!
A finite-dimensional, pointwise two-sector model of bulk/boundary
cancellation.  In each sector the second scalar field coordinate is the
amplitude of one fixed extrinsic-curvature direction.  The affine GHY slot is
the explicit density from the boundary ledger with all induced geometry held
fixed.  Its derivative cancels an equal and opposite supplied bulk flux.

This gate proves only that local algebraic cancellation model.  It is not an
Einstein--Hilbert metric variation, an integration theorem for null/corner
strata, or a worldvolume equation of motion.
-/

namespace JanusFormal
namespace P0EFTJanusExplicitBulkBoundaryCancellation

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations
open P0EFTJanusTwoSectorBulkBoundaryFrechetVariation

/-- The first coordinate is an interior mode; the second is one fixed local
extrinsic-curvature amplitude. -/
abbrev LocalSectorField := ℝ × ℝ

/-- Concrete trace/lift interface for the local boundary amplitude. -/
def localBoundaryInterface :
    BoundaryVariationInterface
      (Field := LocalSectorField) (Boundary := ℝ) where
  trace := ContinuousLinearMap.snd ℝ ℝ ℝ
  admissible := ⊤
  boundaryAdmissible := ⊤
  boundaryLift := ContinuousLinearMap.inr ℝ ℝ ℝ
  interior_admissible := by
    intro variation hVariation
    simp
  admissible_trace := by
    intro variation hVariation
    simp
  boundaryLift_admissible := by
    intro boundary hBoundary
    simp
  trace_boundaryLift := by
    intro boundary hBoundary
    simp

@[simp]
theorem localBoundaryInterface_trace_apply (variation : LocalSectorField) :
    localBoundaryInterface.trace variation = variation.2 := by
  rfl

@[simp]
theorem localBoundaryInterface_boundaryLift_apply (boundary : ℝ) :
    localBoundaryInterface.boundaryLift boundary = (0, boundary) := by
  rfl

/-- A fixed non-null face and one chosen extrinsic-curvature direction. -/
structure FixedGHYSlot where
  einsteinScale : ℝ
  geometry : NonNullBoundaryPointData
  extrinsicDirection : Matrix3
  extrinsicDirectionSymmetric :
    extrinsicDirection.transpose = extrinsicDirection

/-- The concrete coefficient obtained by differentiating the GHY density in
the chosen direction at fixed induced geometry. -/
def ghyCoefficient (slot : FixedGHYSlot) : ℝ :=
  nonNullGHYExtrinsicVariation
    slot.einsteinScale slot.geometry slot.extrinsicDirection

/-- Continuous scalar flux carrying the concrete GHY coefficient. -/
def scalarFlux (coefficient : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ coefficient

@[simp]
theorem scalarFlux_apply (coefficient amplitude : ℝ) :
    scalarFlux coefficient amplitude = coefficient * amplitude := by
  simp [scalarFlux, mul_comm]

def ghyBoundaryFlux (slot : FixedGHYSlot) : ℝ →L[ℝ] ℝ :=
  scalarFlux (ghyCoefficient slot)

/-- The actual affine GHY-density curve supplied by the local-variation gate. -/
def ghyBoundaryAction (slot : FixedGHYSlot) : ℝ → ℝ :=
  nonNullGHYExtrinsicCurve
    slot.einsteinScale slot.geometry slot.extrinsicDirection

theorem ghyBoundaryAction_hasFDerivAt_zero (slot : FixedGHYSlot) :
    HasFDerivAt (ghyBoundaryAction slot) (ghyBoundaryFlux slot) 0 := by
  change HasDerivAt
    (nonNullGHYExtrinsicCurve
      slot.einsteinScale slot.geometry slot.extrinsicDirection)
    (nonNullGHYExtrinsicVariation
      slot.einsteinScale slot.geometry slot.extrinsicDirection) 0
  exact nonNullGHYExtrinsicCurve_hasDerivAt
    slot.einsteinScale slot.geometry slot.extrinsicDirection

/-- Interior Euler functional on the first local field coordinate. -/
def interiorEuler (coefficient : ℝ) : LocalSectorField →L[ℝ] ℝ :=
  coefficient • ContinuousLinearMap.fst ℝ ℝ ℝ

@[simp]
theorem interiorEuler_apply
    (coefficient : ℝ) (variation : LocalSectorField) :
    interiorEuler coefficient variation = coefficient * variation.1 := by
  simp [interiorEuler]

/-- Bulk first variation with a supplied multiple of the opposite GHY flux.
`bulkMultiplier = 1` is the matched normalization. -/
def suppliedBulkEuler
    (interiorCoefficient bulkMultiplier : ℝ) (slot : FixedGHYSlot) :
    LocalSectorField →L[ℝ] ℝ :=
  interiorEuler interiorCoefficient -
    bulkMultiplier •
      (ghyBoundaryFlux slot).comp localBoundaryInterface.trace

/-- A concrete affine-linear bulk action realizing `suppliedBulkEuler`. -/
def suppliedBulkAction
    (interiorCoefficient bulkMultiplier : ℝ) (slot : FixedGHYSlot) :
    LocalSectorField → ℝ :=
  suppliedBulkEuler interiorCoefficient bulkMultiplier slot

theorem suppliedBulkAction_hasFDerivAt
    (interiorCoefficient bulkMultiplier : ℝ) (slot : FixedGHYSlot)
    (field : LocalSectorField) :
    HasFDerivAt
      (suppliedBulkAction interiorCoefficient bulkMultiplier slot)
      (suppliedBulkEuler interiorCoefficient bulkMultiplier slot) field := by
  exact
    (suppliedBulkEuler interiorCoefficient bulkMultiplier slot).hasFDerivAt

@[simp]
theorem suppliedBulkEuler_apply
    (interiorCoefficient bulkMultiplier : ℝ) (slot : FixedGHYSlot)
    (variation : LocalSectorField) :
    suppliedBulkEuler interiorCoefficient bulkMultiplier slot variation =
      interiorCoefficient * variation.1 -
        bulkMultiplier * ghyCoefficient slot * variation.2 := by
  simp [suppliedBulkEuler, ghyBoundaryFlux]
  ring

/-- Exact local flux cancellation when the bulk coefficient is matched. -/
theorem matched_sector_firstVariation_eq_interior
    (interiorCoefficient : ℝ) (slot : FixedGHYSlot) :
    sectorFirstVariation localBoundaryInterface
        (suppliedBulkEuler interiorCoefficient 1 slot)
        (ghyBoundaryFlux slot) =
      interiorEuler interiorCoefficient := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [sectorFirstVariation_apply, suppliedBulkEuler_apply,
    ghyBoundaryFlux]

/-- The local base point keeps the varied boundary amplitude at zero. -/
def localBasePoint (interiorValue : ℝ) : LocalSectorField :=
  (interiorValue, 0)

/-- Two independent local sectors, each with an explicit bulk multiplier and
its concrete affine GHY slot. -/
def localTwoSectorAction
    (plusInterior plusBulkMultiplier : ℝ) (plusSlot : FixedGHYSlot)
    (minusInterior minusBulkMultiplier : ℝ) (minusSlot : FixedGHYSlot) :
    LocalSectorField × LocalSectorField → ℝ :=
  twoSectorAction localBoundaryInterface localBoundaryInterface
    (suppliedBulkAction plusInterior plusBulkMultiplier plusSlot)
    (ghyBoundaryAction plusSlot)
    (suppliedBulkAction minusInterior minusBulkMultiplier minusSlot)
    (ghyBoundaryAction minusSlot)

theorem localTwoSectorAction_fderiv
    (plusInterior plusBulkMultiplier : ℝ) (plusSlot : FixedGHYSlot)
    (minusInterior minusBulkMultiplier : ℝ) (minusSlot : FixedGHYSlot)
    (plusValue minusValue : ℝ) :
    fderiv ℝ
        (localTwoSectorAction plusInterior plusBulkMultiplier plusSlot
          minusInterior minusBulkMultiplier minusSlot)
        (localBasePoint plusValue, localBasePoint minusValue) =
      twoSectorFirstVariation
        (sectorFirstVariation localBoundaryInterface
          (suppliedBulkEuler plusInterior plusBulkMultiplier plusSlot)
          (ghyBoundaryFlux plusSlot))
        (sectorFirstVariation localBoundaryInterface
          (suppliedBulkEuler minusInterior minusBulkMultiplier minusSlot)
          (ghyBoundaryFlux minusSlot)) := by
  apply twoSectorAction_fderiv
  · exact suppliedBulkAction_hasFDerivAt
      plusInterior plusBulkMultiplier plusSlot (localBasePoint plusValue)
  · simpa [localBoundaryInterface, localBasePoint] using
      ghyBoundaryAction_hasFDerivAt_zero plusSlot
  · exact suppliedBulkAction_hasFDerivAt
      minusInterior minusBulkMultiplier minusSlot (localBasePoint minusValue)
  · simpa [localBoundaryInterface, localBasePoint] using
      ghyBoundaryAction_hasFDerivAt_zero minusSlot

/-- With both bulk coefficients matched, only the two interior Euler
functionals remain in the full two-sector derivative. -/
theorem matched_localTwoSectorAction_fderiv
    (plusInterior : ℝ) (plusSlot : FixedGHYSlot)
    (minusInterior : ℝ) (minusSlot : FixedGHYSlot)
    (plusValue minusValue : ℝ) :
    fderiv ℝ
        (localTwoSectorAction plusInterior 1 plusSlot
          minusInterior 1 minusSlot)
        (localBasePoint plusValue, localBasePoint minusValue) =
      twoSectorFirstVariation
        (interiorEuler plusInterior) (interiorEuler minusInterior) := by
  rw [localTwoSectorAction_fderiv,
    matched_sector_firstVariation_eq_interior,
    matched_sector_firstVariation_eq_interior]

/-- After sector-by-sector GHY cancellation, stationarity under all local
variations is equivalent to the vanishing of both interior Euler terms. -/
theorem matched_stationary_iff_interiorEuler_zero
    (plusInterior : ℝ) (plusSlot : FixedGHYSlot)
    (minusInterior : ℝ) (minusSlot : FixedGHYSlot)
    (plusValue minusValue : ℝ) :
    TwoSectorStationaryAt
        (localTwoSectorAction plusInterior 1 plusSlot
          minusInterior 1 minusSlot)
        localBoundaryInterface.admissible
        localBoundaryInterface.admissible
        (localBasePoint plusValue, localBasePoint minusValue) ↔
      plusInterior = 0 ∧ minusInterior = 0 := by
  constructor
  · intro hStationary
    constructor
    · have hPlus := hStationary (1, 0) (by simp [localBoundaryInterface])
          (0, 0) (by simp [localBoundaryInterface])
      rw [matched_localTwoSectorAction_fderiv] at hPlus
      simpa using hPlus
    · have hMinus := hStationary (0, 0) (by simp [localBoundaryInterface])
          (1, 0) (by simp [localBoundaryInterface])
      rw [matched_localTwoSectorAction_fderiv] at hMinus
      simpa using hMinus
  · rintro ⟨hPlus, hMinus⟩ plusVariation hPlusAdmissible
      minusVariation hMinusAdmissible
    rw [matched_localTwoSectorAction_fderiv]
    simp [hPlus, hMinus]

/-- Exact residual on a pure plus-sector boundary variation. -/
theorem mismatched_plus_coefficient_residual
    (plusInterior plusBulkMultiplier : ℝ) (plusSlot : FixedGHYSlot)
    (minusInterior : ℝ) (minusSlot : FixedGHYSlot)
    (plusValue minusValue : ℝ) :
    fderiv ℝ
        (localTwoSectorAction plusInterior plusBulkMultiplier plusSlot
          minusInterior 1 minusSlot)
        (localBasePoint plusValue, localBasePoint minusValue)
        ((0, 1), (0, 0)) =
      (1 - plusBulkMultiplier) * ghyCoefficient plusSlot := by
  rw [localTwoSectorAction_fderiv]
  simp [sectorFirstVariation_apply, suppliedBulkEuler_apply,
    ghyBoundaryFlux]
  ring

/-- A genuinely mismatched bulk multiplier leaves a nonzero boundary flux
whenever the selected GHY direction has nonzero coefficient. -/
theorem mismatched_plus_coefficient_leaves_nonzero_flux
    (plusInterior plusBulkMultiplier : ℝ) (plusSlot : FixedGHYSlot)
    (minusInterior : ℝ) (minusSlot : FixedGHYSlot)
    (plusValue minusValue : ℝ)
    (hMismatch : plusBulkMultiplier ≠ 1)
    (hGHY : ghyCoefficient plusSlot ≠ 0) :
    fderiv ℝ
        (localTwoSectorAction plusInterior plusBulkMultiplier plusSlot
          minusInterior 1 minusSlot)
        (localBasePoint plusValue, localBasePoint minusValue)
        ((0, 1), (0, 0)) ≠ 0 := by
  rw [mismatched_plus_coefficient_residual]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hMismatch)) hGHY

/- The fixed induced metric, inverse, orientation and chosen local direction
are supplied data.  Promoting this cancellation to the covariant EH/LL/null
problem remains a separate Program P gate. -/

end

end P0EFTJanusExplicitBulkBoundaryCancellation
end JanusFormal
