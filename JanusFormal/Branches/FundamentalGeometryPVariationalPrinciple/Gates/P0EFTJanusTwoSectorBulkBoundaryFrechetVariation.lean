import Mathlib

/-!
This gate gives a normed-space interface for genuine bulk-plus-boundary first
variations in two independent sectors.  The trace and boundary lift are
declared analytic data.  No GHY, null-boundary, corner, or Janus junction
functional is claimed to have been geometrically constructed.
-/

namespace JanusFormal
namespace P0EFTJanusTwoSectorBulkBoundaryFrechetVariation

set_option autoImplicit false

noncomputable section

universe u v w x

variable {Field : Type u} {Boundary : Type v}
variable [NormedAddCommGroup Field] [NormedSpace ℝ Field]
variable [NormedAddCommGroup Boundary] [NormedSpace ℝ Boundary]

/-- Analytic interface for admissible bulk and boundary variations.  Interior
variations lie in the trace kernel, while every admissible boundary mode has a
declared admissible lift. -/
structure BoundaryVariationInterface where
  trace : Field →L[ℝ] Boundary
  admissible : Submodule ℝ Field
  boundaryAdmissible : Submodule ℝ Boundary
  boundaryLift : Boundary →L[ℝ] Field
  interior_admissible : trace.ker ≤ admissible
  admissible_trace : ∀ variation, variation ∈ admissible →
    trace variation ∈ boundaryAdmissible
  boundaryLift_admissible : ∀ boundary, boundary ∈ boundaryAdmissible →
    boundaryLift boundary ∈ admissible
  trace_boundaryLift : ∀ boundary, boundary ∈ boundaryAdmissible →
    trace (boundaryLift boundary) = boundary

theorem BoundaryVariationInterface.trace_boundaryLift_apply
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (boundary : Boundary)
    (hBoundary : boundary ∈ interface.boundaryAdmissible) :
    interface.trace (interface.boundaryLift boundary) = boundary := by
  exact interface.trace_boundaryLift boundary hBoundary

/-- Affine line through a field configuration in a chosen variation. -/
def affineVariation (field variation : Field) (t : ℝ) : Field :=
  field + t • variation

theorem affineVariation_hasDerivAt
    (field variation : Field) :
    HasDerivAt (affineVariation field variation) variation 0 := by
  have hDerivative :=
    ((hasDerivAt_id (0 : ℝ)).smul_const variation).const_add field
  exact hDerivative.congr_deriv (one_smul ℝ variation)

/-- A sector action consisting of a bulk action and a boundary action pulled
back through the declared trace. -/
def sectorAction
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (field : Field) : ℝ :=
  bulkAction field + boundaryAction (interface.trace field)

/-- Displayed sector first variation: bulk Euler functional plus boundary
flux composed with the trace. -/
def sectorFirstVariation
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ) : Field →L[ℝ] ℝ :=
  bulkEuler + boundaryFlux.comp interface.trace

@[simp]
theorem sectorFirstVariation_apply
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ)
    (variation : Field) :
    sectorFirstVariation interface bulkEuler boundaryFlux variation =
      bulkEuler variation + boundaryFlux (interface.trace variation) := by
  rfl

/-- Genuine Frechet derivative of the sector action. -/
theorem sectorAction_hasFDerivAt
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (field : Field)
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ)
    (hBulk : HasFDerivAt bulkAction bulkEuler field)
    (hBoundary : HasFDerivAt boundaryAction boundaryFlux
      (interface.trace field)) :
    HasFDerivAt (sectorAction interface bulkAction boundaryAction)
      (sectorFirstVariation interface bulkEuler boundaryFlux) field := by
  change HasFDerivAt
    (fun point => bulkAction point + boundaryAction (interface.trace point))
    (bulkEuler + boundaryFlux.comp interface.trace) field
  exact hBulk.add (hBoundary.comp field interface.trace.hasFDerivAt)

/-- Genuine directional derivative along every affine admissible or
non-admissible variation. -/
theorem sectorAction_line_hasDerivAt
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (field variation : Field)
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ)
    (hBulk : HasFDerivAt bulkAction bulkEuler field)
    (hBoundary : HasFDerivAt boundaryAction boundaryFlux
      (interface.trace field)) :
    HasDerivAt
      (fun t => sectorAction interface bulkAction boundaryAction
        (affineVariation field variation t))
      (sectorFirstVariation interface bulkEuler boundaryFlux variation) 0 := by
  simpa [Function.comp_def] using
    (sectorAction_hasFDerivAt interface bulkAction boundaryAction field
      bulkEuler boundaryFlux hBulk hBoundary).comp_hasDerivAt_of_eq
        0 (affineVariation_hasDerivAt field variation)
        (by simp [affineVariation])

/-- Exact Frechet derivative of the sector action. -/
theorem sectorAction_fderiv
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (field : Field)
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ)
    (hBulk : HasFDerivAt bulkAction bulkEuler field)
    (hBoundary : HasFDerivAt boundaryAction boundaryFlux
      (interface.trace field)) :
    fderiv ℝ (sectorAction interface bulkAction boundaryAction) field =
      sectorFirstVariation interface bulkEuler boundaryFlux :=
  (sectorAction_hasFDerivAt interface bulkAction boundaryAction field
    bulkEuler boundaryFlux hBulk hBoundary).fderiv

/-- A linear first variation annihilates all declared admissible directions. -/
def AnnihilatesAdmissible
    (firstVariation : Field →L[ℝ] ℝ)
    (admissible : Submodule ℝ Field) : Prop :=
  ∀ variation, variation ∈ admissible → firstVariation variation = 0

/-- Exact bulk/boundary separation.  Stationarity on admissible variations is
equivalent to the bulk Euler functional vanishing on interior variations and
the lifted bulk contribution cancelling the boundary flux for every admissible
boundary mode. -/
theorem sectorFirstVariation_annihilates_iff_bulk_boundary_balance
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ) :
    AnnihilatesAdmissible
        (sectorFirstVariation interface bulkEuler boundaryFlux)
        interface.admissible ↔
      (∀ interior, interior ∈ interface.trace.ker →
        bulkEuler interior = 0) ∧
      (∀ boundary, boundary ∈ interface.boundaryAdmissible →
        bulkEuler (interface.boundaryLift boundary) +
          boundaryFlux boundary = 0) := by
  constructor
  · intro hStationary
    constructor
    · intro interior hInterior
      have hTotal := hStationary interior
        (interface.interior_admissible hInterior)
      have hTrace : interface.trace interior = 0 := hInterior
      simpa [sectorFirstVariation, hTrace] using hTotal
    · intro boundary hBoundary
      have hTotal := hStationary (interface.boundaryLift boundary)
        (interface.boundaryLift_admissible boundary hBoundary)
      simpa [sectorFirstVariation,
        interface.trace_boundaryLift_apply boundary hBoundary] using hTotal
  · rintro ⟨hInterior, hBoundary⟩ variation hVariation
    let boundary := interface.trace variation
    let interior := variation - interface.boundaryLift boundary
    have hBoundaryMembership : boundary ∈ interface.boundaryAdmissible :=
      interface.admissible_trace variation hVariation
    have hTraceInterior : interface.trace interior = 0 := by
      simp [interior, boundary,
        interface.trace_boundaryLift_apply boundary hBoundaryMembership]
    have hInteriorMembership : interior ∈ interface.trace.ker :=
      hTraceInterior
    have hInteriorZero := hInterior interior hInteriorMembership
    have hBoundaryZero := hBoundary boundary hBoundaryMembership
    rw [sectorFirstVariation_apply]
    have hBulkDecomposition :
        bulkEuler variation =
          bulkEuler interior + bulkEuler (interface.boundaryLift boundary) := by
      simp [interior, boundary]
    rw [hBulkDecomposition, hInteriorZero]
    simpa [boundary] using hBoundaryZero

/-- Actual stationarity of a sector action on its admissible directions. -/
def SectorStationaryAt
    (action : Field → ℝ)
    (admissible : Submodule ℝ Field)
    (field : Field) : Prop :=
  ∀ variation, variation ∈ admissible →
    fderiv ℝ action field variation = 0

/-- Exact stationarity criterion for the genuine sector action. -/
theorem sectorStationaryAt_iff_bulk_boundary_balance
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (field : Field)
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ)
    (hBulk : HasFDerivAt bulkAction bulkEuler field)
    (hBoundary : HasFDerivAt boundaryAction boundaryFlux
      (interface.trace field)) :
    SectorStationaryAt
        (sectorAction interface bulkAction boundaryAction)
        interface.admissible field ↔
      (∀ interior, interior ∈ interface.trace.ker →
        bulkEuler interior = 0) ∧
      (∀ boundary, boundary ∈ interface.boundaryAdmissible →
        bulkEuler (interface.boundaryLift boundary) +
          boundaryFlux boundary = 0) := by
  unfold SectorStationaryAt
  rw [show fderiv ℝ (sectorAction interface bulkAction boundaryAction) field =
      sectorFirstVariation interface bulkEuler boundaryFlux from
    sectorAction_fderiv interface bulkAction boundaryAction field
      bulkEuler boundaryFlux hBulk hBoundary]
  exact sectorFirstVariation_annihilates_iff_bulk_boundary_balance
    interface bulkEuler boundaryFlux

/-- If the bulk Euler functional is already zero, any nonzero accessible
boundary flux obstructs actual stationarity. -/
theorem nonzero_boundary_flux_blocks_sector_stationarity
    (interface : BoundaryVariationInterface
      (Field := Field) (Boundary := Boundary))
    (bulkAction : Field → ℝ)
    (boundaryAction : Boundary → ℝ)
    (field : Field)
    (bulkEuler : Field →L[ℝ] ℝ)
    (boundaryFlux : Boundary →L[ℝ] ℝ)
    (hBulk : HasFDerivAt bulkAction bulkEuler field)
    (hBoundary : HasFDerivAt boundaryAction boundaryFlux
      (interface.trace field))
    (hBulkOnShell : bulkEuler = 0)
    (hFlux : ¬ AnnihilatesAdmissible
      boundaryFlux interface.boundaryAdmissible) :
    ¬ SectorStationaryAt
      (sectorAction interface bulkAction boundaryAction)
      interface.admissible field := by
  intro hStationary
  have hBalance :=
    (sectorStationaryAt_iff_bulk_boundary_balance
      interface bulkAction boundaryAction field bulkEuler boundaryFlux
      hBulk hBoundary).1 hStationary |>.2
  apply hFlux
  intro boundary hBoundary
  have hBoundaryZero := hBalance boundary hBoundary
  simpa [hBulkOnShell] using hBoundaryZero

variable {PlusField : Type u} {PlusBoundary : Type v}
variable {MinusField : Type w} {MinusBoundary : Type x}
variable [NormedAddCommGroup PlusField] [NormedSpace ℝ PlusField]
variable [NormedAddCommGroup PlusBoundary] [NormedSpace ℝ PlusBoundary]
variable [NormedAddCommGroup MinusField] [NormedSpace ℝ MinusField]
variable [NormedAddCommGroup MinusBoundary] [NormedSpace ℝ MinusBoundary]

/-- Sum of the two independent bulk-plus-boundary sector actions. -/
def twoSectorAction
    (plusInterface : BoundaryVariationInterface
      (Field := PlusField) (Boundary := PlusBoundary))
    (minusInterface : BoundaryVariationInterface
      (Field := MinusField) (Boundary := MinusBoundary))
    (plusBulkAction : PlusField → ℝ)
    (plusBoundaryAction : PlusBoundary → ℝ)
    (minusBulkAction : MinusField → ℝ)
    (minusBoundaryAction : MinusBoundary → ℝ)
    (field : PlusField × MinusField) : ℝ :=
  sectorAction plusInterface plusBulkAction plusBoundaryAction field.1 +
    sectorAction minusInterface minusBulkAction minusBoundaryAction field.2

/-- Independent sum of the two displayed sector first variations. -/
def twoSectorFirstVariation
    (plusVariation : PlusField →L[ℝ] ℝ)
    (minusVariation : MinusField →L[ℝ] ℝ) :
    PlusField × MinusField →L[ℝ] ℝ :=
  plusVariation.comp (ContinuousLinearMap.fst ℝ PlusField MinusField) +
    minusVariation.comp (ContinuousLinearMap.snd ℝ PlusField MinusField)

@[simp]
theorem twoSectorFirstVariation_apply
    (plusVariation : PlusField →L[ℝ] ℝ)
    (minusVariation : MinusField →L[ℝ] ℝ)
    (variation : PlusField × MinusField) :
    twoSectorFirstVariation plusVariation minusVariation variation =
      plusVariation variation.1 + minusVariation variation.2 := by
  rfl

/-- Genuine joint Frechet derivative of the two-sector action. -/
theorem twoSectorAction_hasFDerivAt
    (plusInterface : BoundaryVariationInterface
      (Field := PlusField) (Boundary := PlusBoundary))
    (minusInterface : BoundaryVariationInterface
      (Field := MinusField) (Boundary := MinusBoundary))
    (plusBulkAction : PlusField → ℝ)
    (plusBoundaryAction : PlusBoundary → ℝ)
    (minusBulkAction : MinusField → ℝ)
    (minusBoundaryAction : MinusBoundary → ℝ)
    (field : PlusField × MinusField)
    (plusBulkEuler : PlusField →L[ℝ] ℝ)
    (plusBoundaryFlux : PlusBoundary →L[ℝ] ℝ)
    (minusBulkEuler : MinusField →L[ℝ] ℝ)
    (minusBoundaryFlux : MinusBoundary →L[ℝ] ℝ)
    (hPlusBulk : HasFDerivAt plusBulkAction plusBulkEuler field.1)
    (hPlusBoundary : HasFDerivAt plusBoundaryAction plusBoundaryFlux
      (plusInterface.trace field.1))
    (hMinusBulk : HasFDerivAt minusBulkAction minusBulkEuler field.2)
    (hMinusBoundary : HasFDerivAt minusBoundaryAction minusBoundaryFlux
      (minusInterface.trace field.2)) :
    HasFDerivAt
      (twoSectorAction plusInterface minusInterface plusBulkAction
        plusBoundaryAction minusBulkAction minusBoundaryAction)
      (twoSectorFirstVariation
        (sectorFirstVariation plusInterface plusBulkEuler plusBoundaryFlux)
        (sectorFirstVariation minusInterface minusBulkEuler minusBoundaryFlux))
      field := by
  have hPlus := sectorAction_hasFDerivAt plusInterface plusBulkAction
    plusBoundaryAction field.1 plusBulkEuler plusBoundaryFlux
    hPlusBulk hPlusBoundary
  have hMinus := sectorAction_hasFDerivAt minusInterface minusBulkAction
    minusBoundaryAction field.2 minusBulkEuler minusBoundaryFlux
    hMinusBulk hMinusBoundary
  change HasFDerivAt
    (fun point : PlusField × MinusField =>
      sectorAction plusInterface plusBulkAction plusBoundaryAction point.1 +
        sectorAction minusInterface minusBulkAction minusBoundaryAction point.2)
    _ field
  exact
    (hPlus.comp field hasFDerivAt_fst).add
      (hMinus.comp field hasFDerivAt_snd)

/-- Genuine directional derivative of the two-sector action along every
affine pair of variations. -/
theorem twoSectorAction_line_hasDerivAt
    (plusInterface : BoundaryVariationInterface
      (Field := PlusField) (Boundary := PlusBoundary))
    (minusInterface : BoundaryVariationInterface
      (Field := MinusField) (Boundary := MinusBoundary))
    (plusBulkAction : PlusField → ℝ)
    (plusBoundaryAction : PlusBoundary → ℝ)
    (minusBulkAction : MinusField → ℝ)
    (minusBoundaryAction : MinusBoundary → ℝ)
    (field variation : PlusField × MinusField)
    (plusBulkEuler : PlusField →L[ℝ] ℝ)
    (plusBoundaryFlux : PlusBoundary →L[ℝ] ℝ)
    (minusBulkEuler : MinusField →L[ℝ] ℝ)
    (minusBoundaryFlux : MinusBoundary →L[ℝ] ℝ)
    (hPlusBulk : HasFDerivAt plusBulkAction plusBulkEuler field.1)
    (hPlusBoundary : HasFDerivAt plusBoundaryAction plusBoundaryFlux
      (plusInterface.trace field.1))
    (hMinusBulk : HasFDerivAt minusBulkAction minusBulkEuler field.2)
    (hMinusBoundary : HasFDerivAt minusBoundaryAction minusBoundaryFlux
      (minusInterface.trace field.2)) :
    HasDerivAt
      (fun t => twoSectorAction plusInterface minusInterface plusBulkAction
        plusBoundaryAction minusBulkAction minusBoundaryAction
        (affineVariation field variation t))
      (twoSectorFirstVariation
        (sectorFirstVariation plusInterface plusBulkEuler plusBoundaryFlux)
        (sectorFirstVariation minusInterface minusBulkEuler minusBoundaryFlux)
        variation) 0 := by
  simpa [Function.comp_def] using
    (twoSectorAction_hasFDerivAt plusInterface minusInterface plusBulkAction
      plusBoundaryAction minusBulkAction minusBoundaryAction field
      plusBulkEuler plusBoundaryFlux minusBulkEuler minusBoundaryFlux
      hPlusBulk hPlusBoundary hMinusBulk hMinusBoundary).comp_hasDerivAt_of_eq
        0 (affineVariation_hasDerivAt field variation)
        (by simp [affineVariation])

/-- Exact joint Frechet derivative of the two-sector action. -/
theorem twoSectorAction_fderiv
    (plusInterface : BoundaryVariationInterface
      (Field := PlusField) (Boundary := PlusBoundary))
    (minusInterface : BoundaryVariationInterface
      (Field := MinusField) (Boundary := MinusBoundary))
    (plusBulkAction : PlusField → ℝ)
    (plusBoundaryAction : PlusBoundary → ℝ)
    (minusBulkAction : MinusField → ℝ)
    (minusBoundaryAction : MinusBoundary → ℝ)
    (field : PlusField × MinusField)
    (plusBulkEuler : PlusField →L[ℝ] ℝ)
    (plusBoundaryFlux : PlusBoundary →L[ℝ] ℝ)
    (minusBulkEuler : MinusField →L[ℝ] ℝ)
    (minusBoundaryFlux : MinusBoundary →L[ℝ] ℝ)
    (hPlusBulk : HasFDerivAt plusBulkAction plusBulkEuler field.1)
    (hPlusBoundary : HasFDerivAt plusBoundaryAction plusBoundaryFlux
      (plusInterface.trace field.1))
    (hMinusBulk : HasFDerivAt minusBulkAction minusBulkEuler field.2)
    (hMinusBoundary : HasFDerivAt minusBoundaryAction minusBoundaryFlux
      (minusInterface.trace field.2)) :
    fderiv ℝ
        (twoSectorAction plusInterface minusInterface plusBulkAction
          plusBoundaryAction minusBulkAction minusBoundaryAction) field =
      twoSectorFirstVariation
        (sectorFirstVariation plusInterface plusBulkEuler plusBoundaryFlux)
        (sectorFirstVariation minusInterface minusBulkEuler minusBoundaryFlux) :=
  (twoSectorAction_hasFDerivAt plusInterface minusInterface plusBulkAction
    plusBoundaryAction minusBulkAction minusBoundaryAction field
    plusBulkEuler plusBoundaryFlux minusBulkEuler minusBoundaryFlux
    hPlusBulk hPlusBoundary hMinusBulk hMinusBoundary).fderiv

/-- Actual stationarity under all independent pairs of admissible variations. -/
def TwoSectorStationaryAt
    (action : PlusField × MinusField → ℝ)
    (plusAdmissible : Submodule ℝ PlusField)
    (minusAdmissible : Submodule ℝ MinusField)
    (field : PlusField × MinusField) : Prop :=
  ∀ plusVariation, plusVariation ∈ plusAdmissible →
    ∀ minusVariation, minusVariation ∈ minusAdmissible →
      fderiv ℝ action field (plusVariation, minusVariation) = 0

theorem independent_variations_annihilate_iff_sectors
    (plusVariation : PlusField →L[ℝ] ℝ)
    (minusVariation : MinusField →L[ℝ] ℝ)
    (plusAdmissible : Submodule ℝ PlusField)
    (minusAdmissible : Submodule ℝ MinusField) :
    (∀ plusDirection, plusDirection ∈ plusAdmissible →
      ∀ minusDirection, minusDirection ∈ minusAdmissible →
        plusVariation plusDirection + minusVariation minusDirection = 0) ↔
      AnnihilatesAdmissible plusVariation plusAdmissible ∧
      AnnihilatesAdmissible minusVariation minusAdmissible := by
  constructor
  · intro hStationary
    constructor
    · intro plusDirection hPlus
      simpa using hStationary plusDirection hPlus 0
        minusAdmissible.zero_mem
    · intro minusDirection hMinus
      simpa using hStationary 0 plusAdmissible.zero_mem
        minusDirection hMinus
  · rintro ⟨hPlus, hMinus⟩ plusDirection hPlusMem
      minusDirection hMinusMem
    rw [hPlus plusDirection hPlusMem, hMinus minusDirection hMinusMem]
    simp

/-- Exact two-sector stationarity criterion: each sector independently obeys
its interior bulk equation and its lifted bulk/boundary balance. -/
theorem twoSectorStationaryAt_iff_bulk_boundary_balance
    (plusInterface : BoundaryVariationInterface
      (Field := PlusField) (Boundary := PlusBoundary))
    (minusInterface : BoundaryVariationInterface
      (Field := MinusField) (Boundary := MinusBoundary))
    (plusBulkAction : PlusField → ℝ)
    (plusBoundaryAction : PlusBoundary → ℝ)
    (minusBulkAction : MinusField → ℝ)
    (minusBoundaryAction : MinusBoundary → ℝ)
    (field : PlusField × MinusField)
    (plusBulkEuler : PlusField →L[ℝ] ℝ)
    (plusBoundaryFlux : PlusBoundary →L[ℝ] ℝ)
    (minusBulkEuler : MinusField →L[ℝ] ℝ)
    (minusBoundaryFlux : MinusBoundary →L[ℝ] ℝ)
    (hPlusBulk : HasFDerivAt plusBulkAction plusBulkEuler field.1)
    (hPlusBoundary : HasFDerivAt plusBoundaryAction plusBoundaryFlux
      (plusInterface.trace field.1))
    (hMinusBulk : HasFDerivAt minusBulkAction minusBulkEuler field.2)
    (hMinusBoundary : HasFDerivAt minusBoundaryAction minusBoundaryFlux
      (minusInterface.trace field.2)) :
    TwoSectorStationaryAt
        (twoSectorAction plusInterface minusInterface plusBulkAction
          plusBoundaryAction minusBulkAction minusBoundaryAction)
        plusInterface.admissible minusInterface.admissible field ↔
      ((∀ interior, interior ∈ plusInterface.trace.ker →
          plusBulkEuler interior = 0) ∧
        (∀ boundary, boundary ∈ plusInterface.boundaryAdmissible →
          plusBulkEuler (plusInterface.boundaryLift boundary) +
            plusBoundaryFlux boundary = 0)) ∧
      ((∀ interior, interior ∈ minusInterface.trace.ker →
          minusBulkEuler interior = 0) ∧
        (∀ boundary, boundary ∈ minusInterface.boundaryAdmissible →
          minusBulkEuler (minusInterface.boundaryLift boundary) +
            minusBoundaryFlux boundary = 0)) := by
  have hDerivative := twoSectorAction_fderiv
    plusInterface minusInterface plusBulkAction plusBoundaryAction
    minusBulkAction minusBoundaryAction field plusBulkEuler plusBoundaryFlux
    minusBulkEuler minusBoundaryFlux hPlusBulk hPlusBoundary
    hMinusBulk hMinusBoundary
  unfold TwoSectorStationaryAt
  rw [hDerivative]
  simp only [twoSectorFirstVariation_apply]
  rw [independent_variations_annihilate_iff_sectors]
  rw [sectorFirstVariation_annihilates_iff_bulk_boundary_balance,
    sectorFirstVariation_annihilates_iff_bulk_boundary_balance]

/-- In the actual two-sector action, a nonzero accessible boundary flux in
either bulk-on-shell sector obstructs total stationarity. -/
theorem nonzero_boundary_flux_blocks_two_sector_stationarity
    (plusInterface : BoundaryVariationInterface
      (Field := PlusField) (Boundary := PlusBoundary))
    (minusInterface : BoundaryVariationInterface
      (Field := MinusField) (Boundary := MinusBoundary))
    (plusBulkAction : PlusField → ℝ)
    (plusBoundaryAction : PlusBoundary → ℝ)
    (minusBulkAction : MinusField → ℝ)
    (minusBoundaryAction : MinusBoundary → ℝ)
    (field : PlusField × MinusField)
    (plusBulkEuler : PlusField →L[ℝ] ℝ)
    (plusBoundaryFlux : PlusBoundary →L[ℝ] ℝ)
    (minusBulkEuler : MinusField →L[ℝ] ℝ)
    (minusBoundaryFlux : MinusBoundary →L[ℝ] ℝ)
    (hPlusBulk : HasFDerivAt plusBulkAction plusBulkEuler field.1)
    (hPlusBoundary : HasFDerivAt plusBoundaryAction plusBoundaryFlux
      (plusInterface.trace field.1))
    (hMinusBulk : HasFDerivAt minusBulkAction minusBulkEuler field.2)
    (hMinusBoundary : HasFDerivAt minusBoundaryAction minusBoundaryFlux
      (minusInterface.trace field.2))
    (hNonzeroFlux :
      (plusBulkEuler = 0 ∧
        ¬ AnnihilatesAdmissible
          plusBoundaryFlux plusInterface.boundaryAdmissible) ∨
      (minusBulkEuler = 0 ∧
        ¬ AnnihilatesAdmissible
          minusBoundaryFlux minusInterface.boundaryAdmissible)) :
    ¬ TwoSectorStationaryAt
      (twoSectorAction plusInterface minusInterface plusBulkAction
        plusBoundaryAction minusBulkAction minusBoundaryAction)
      plusInterface.admissible minusInterface.admissible field := by
  intro hStationary
  have hConditions :=
    (twoSectorStationaryAt_iff_bulk_boundary_balance
      plusInterface minusInterface plusBulkAction plusBoundaryAction
      minusBulkAction minusBoundaryAction field plusBulkEuler plusBoundaryFlux
      minusBulkEuler minusBoundaryFlux hPlusBulk hPlusBoundary
      hMinusBulk hMinusBoundary).1 hStationary
  rcases hNonzeroFlux with ⟨hBulkZero, hFlux⟩ | ⟨hBulkZero, hFlux⟩
  · apply hFlux
    intro boundary hBoundary
    have hBoundaryZero := hConditions.1.2 boundary hBoundary
    simpa [hBulkZero] using hBoundaryZero
  · apply hFlux
    intro boundary hBoundary
    have hBoundaryZero := hConditions.2.2 boundary hBoundary
    simpa [hBulkZero] using hBoundaryZero

end

end P0EFTJanusTwoSectorBulkBoundaryFrechetVariation
end JanusFormal
