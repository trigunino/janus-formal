import Mathlib

/-!
# Five-sector orthogonal product resolution

A physical sector resolution should not start from five unrelated projectors.
The natural input is one effective orthogonal coordinate system

`E ≃ M × A × S × L × B`,

where the factors represent metric/diffeomorphism, Abelian gauge, primitive
SpinC matter, longitudinal/LL and boundary/finite-BV directions.

This file constructs the five coordinate projectors and proves automatically:

* idempotence;
* self-adjointness;
* pairwise orthogonality;
* pairwise zero composition;
* resolution of the identity.

The construction is generic and can be transported to the actual Candidate-A
Hilbert space by one continuous linear equivalence preserving the inner
product.  No projector or Pythagorean identity is supplied independently.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open Set Topology
open scoped BigOperators InnerProductSpace

/-- The five D10-free physical slots. -/
inductive FiveSectorSlot
  | metricDiffeomorphism
  | abelianGauge
  | primitiveSpinCMatter
  | longitudinalLL
  | boundaryFiniteBV
  deriving DecidableEq, Fintype

/-- Right-associated five-factor product used by the coordinate resolution. -/
abbrev FiveSectorProduct
    (MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*) :=
  MetricDiffeomorphism ×
    (AbelianGauge ×
      (PrimitiveSpinCMatter ×
        (LongitudinalLL × BoundaryFiniteBV)))

section Product

variable
  {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
    BoundaryFiniteBV : Type*}
  [NormedAddCommGroup MetricDiffeomorphism]
  [NormedSpace Real MetricDiffeomorphism]
  [NormedAddCommGroup AbelianGauge]
  [NormedSpace Real AbelianGauge]
  [NormedAddCommGroup PrimitiveSpinCMatter]
  [NormedSpace Real PrimitiveSpinCMatter]
  [NormedAddCommGroup LongitudinalLL]
  [NormedSpace Real LongitudinalLL]
  [NormedAddCommGroup BoundaryFiniteBV]
  [NormedSpace Real BoundaryFiniteBV]

private abbrev Tail1 :=
  AbelianGauge ×
    (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV))

private abbrev Tail2 :=
  PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV)

private abbrev Tail3 := LongitudinalLL × BoundaryFiniteBV

/-- Coordinate projector onto the metric/diffeomorphism slot. -/
def fiveSectorMetricProjection :
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV →L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  (ContinuousLinearMap.fst Real MetricDiffeomorphism Tail1).prod 0

/-- Coordinate projector onto the Abelian gauge slot. -/
def fiveSectorAbelianProjection :
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV →L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  let tail : Tail1 →L[Real] Tail1 :=
    (ContinuousLinearMap.fst Real AbelianGauge Tail2).prod 0
  (0 : FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
      LongitudinalLL BoundaryFiniteBV →L[Real] MetricDiffeomorphism).prod
    (tail.comp
      (ContinuousLinearMap.snd Real MetricDiffeomorphism Tail1))

/-- Coordinate projector onto the primitive SpinC matter slot. -/
def fiveSectorSpinCProjection :
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV →L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  let tail2 : Tail2 →L[Real] Tail2 :=
    (ContinuousLinearMap.fst Real PrimitiveSpinCMatter Tail3).prod 0
  let tail1 : Tail1 →L[Real] Tail1 :=
    (0 : Tail1 →L[Real] AbelianGauge).prod
      (tail2.comp (ContinuousLinearMap.snd Real AbelianGauge Tail2))
  (0 : FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
      LongitudinalLL BoundaryFiniteBV →L[Real] MetricDiffeomorphism).prod
    (tail1.comp
      (ContinuousLinearMap.snd Real MetricDiffeomorphism Tail1))

/-- Coordinate projector onto the longitudinal/LL slot. -/
def fiveSectorLLProjection :
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV →L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  let tail3 : Tail3 →L[Real] Tail3 :=
    (ContinuousLinearMap.fst Real LongitudinalLL BoundaryFiniteBV).prod 0
  let tail2 : Tail2 →L[Real] Tail2 :=
    (0 : Tail2 →L[Real] PrimitiveSpinCMatter).prod
      (tail3.comp
        (ContinuousLinearMap.snd Real PrimitiveSpinCMatter Tail3))
  let tail1 : Tail1 →L[Real] Tail1 :=
    (0 : Tail1 →L[Real] AbelianGauge).prod
      (tail2.comp (ContinuousLinearMap.snd Real AbelianGauge Tail2))
  (0 : FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
      LongitudinalLL BoundaryFiniteBV →L[Real] MetricDiffeomorphism).prod
    (tail1.comp
      (ContinuousLinearMap.snd Real MetricDiffeomorphism Tail1))

/-- Coordinate projector onto the boundary/finite-BV slot. -/
def fiveSectorBoundaryProjection :
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV →L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  let tail3 : Tail3 →L[Real] Tail3 :=
    (0 : Tail3 →L[Real] LongitudinalLL).prod
      (ContinuousLinearMap.snd Real LongitudinalLL BoundaryFiniteBV)
  let tail2 : Tail2 →L[Real] Tail2 :=
    (0 : Tail2 →L[Real] PrimitiveSpinCMatter).prod
      (tail3.comp
        (ContinuousLinearMap.snd Real PrimitiveSpinCMatter Tail3))
  let tail1 : Tail1 →L[Real] Tail1 :=
    (0 : Tail1 →L[Real] AbelianGauge).prod
      (tail2.comp (ContinuousLinearMap.snd Real AbelianGauge Tail2))
  (0 : FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
      LongitudinalLL BoundaryFiniteBV →L[Real] MetricDiffeomorphism).prod
    (tail1.comp
      (ContinuousLinearMap.snd Real MetricDiffeomorphism Tail1))

/-- Coordinate projector selected by a physical sector. -/
def fiveSectorProductProjection
    (sector : FiveSectorSlot) :
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV →L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  match sector with
  | .metricDiffeomorphism => fiveSectorMetricProjection
  | .abelianGauge => fiveSectorAbelianProjection
  | .primitiveSpinCMatter => fiveSectorSpinCProjection
  | .longitudinalLL => fiveSectorLLProjection
  | .boundaryFiniteBV => fiveSectorBoundaryProjection

@[simp]
theorem fiveSectorMetricProjection_apply
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorMetricProjection state = (state.1, 0) :=
  rfl

@[simp]
theorem fiveSectorAbelianProjection_apply
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorAbelianProjection state = (0, (state.2.1, 0)) :=
  rfl

@[simp]
theorem fiveSectorSpinCProjection_apply
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorSpinCProjection state =
      (0, (0, (state.2.2.1, 0))) :=
  rfl

@[simp]
theorem fiveSectorLLProjection_apply
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorLLProjection state =
      (0, (0, (0, (state.2.2.2.1, 0)))) :=
  rfl

@[simp]
theorem fiveSectorBoundaryProjection_apply
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorBoundaryProjection state =
      (0, (0, (0, (0, state.2.2.2.2)))) :=
  rfl

/-- Every coordinate projector is idempotent. -/
theorem fiveSectorProductProjection_idempotent
    (sector : FiveSectorSlot)
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorProductProjection sector
        (fiveSectorProductProjection sector state) =
      fiveSectorProductProjection sector state := by
  cases sector <;>
    rcases state with ⟨metric, abelian, spinC, ll, boundary⟩ <;>
    simp [fiveSectorProductProjection, fiveSectorMetricProjection,
      fiveSectorAbelianProjection, fiveSectorSpinCProjection,
      fiveSectorLLProjection, fiveSectorBoundaryProjection]

/-- Distinct coordinate projectors compose to zero. -/
theorem fiveSectorProductProjection_comp_zero
    (first second : FiveSectorSlot) (hDistinct : first ≠ second) :
    (fiveSectorProductProjection first).comp
        (fiveSectorProductProjection second) =
      (0 : FiveSectorProduct MetricDiffeomorphism AbelianGauge
          PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV →L[Real]
        FiveSectorProduct MetricDiffeomorphism AbelianGauge
          PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) := by
  apply ContinuousLinearMap.ext
  intro state
  cases first <;> cases second <;>
    simp_all [fiveSectorProductProjection, fiveSectorMetricProjection,
      fiveSectorAbelianProjection, fiveSectorSpinCProjection,
      fiveSectorLLProjection, fiveSectorBoundaryProjection]

/-- The five coordinate projectors resolve the identity. -/
theorem fiveSectorProductProjection_sum_apply
    (state : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    (∑ sector : FiveSectorSlot,
      fiveSectorProductProjection sector state) = state := by
  have hUniv : (Finset.univ : Finset FiveSectorSlot) =
      {.metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV} := by
    ext sector
    cases sector <;> simp
  rw [hUniv]
  rcases state with ⟨metric, abelian, spinC, ll, boundary⟩
  simp [fiveSectorProductProjection, fiveSectorMetricProjection,
    fiveSectorAbelianProjection, fiveSectorSpinCProjection,
    fiveSectorLLProjection, fiveSectorBoundaryProjection]

end Product

section InnerProduct

variable
  {MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
    BoundaryFiniteBV : Type*}
  [NormedAddCommGroup MetricDiffeomorphism]
  [InnerProductSpace Real MetricDiffeomorphism]
  [NormedAddCommGroup AbelianGauge]
  [InnerProductSpace Real AbelianGauge]
  [NormedAddCommGroup PrimitiveSpinCMatter]
  [InnerProductSpace Real PrimitiveSpinCMatter]
  [NormedAddCommGroup LongitudinalLL]
  [InnerProductSpace Real LongitudinalLL]
  [NormedAddCommGroup BoundaryFiniteBV]
  [InnerProductSpace Real BoundaryFiniteBV]

/-- Sum inner product on the five coordinates (independent of the product's
max norm). -/
def fiveSectorProductInner
    (first second : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) : Real :=
  inner Real first.1 second.1 +
    inner Real first.2.1 second.2.1 +
    inner Real first.2.2.1 second.2.2.1 +
    inner Real first.2.2.2.1 second.2.2.2.1 +
    inner Real first.2.2.2.2 second.2.2.2.2

/-- Coordinate projectors are self-adjoint. -/
theorem fiveSectorProductProjection_selfAdjoint
    (sector : FiveSectorSlot)
    (first second : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorProductInner (fiveSectorProductProjection sector first) second =
      fiveSectorProductInner first (fiveSectorProductProjection sector second) := by
  cases sector <;>
    rcases first with ⟨metric₁, abelian₁, spinC₁, ll₁, boundary₁⟩ <;>
    rcases second with ⟨metric₂, abelian₂, spinC₂, ll₂, boundary₂⟩ <;>
    simp [fiveSectorProductInner, fiveSectorProductProjection,
      fiveSectorMetricProjection,
      fiveSectorAbelianProjection, fiveSectorSpinCProjection,
      fiveSectorLLProjection, fiveSectorBoundaryProjection]

/-- Images of distinct coordinate projectors are orthogonal. -/
theorem fiveSectorProductProjection_orthogonal
    (firstSector secondSector : FiveSectorSlot)
    (hDistinct : firstSector ≠ secondSector)
    (first second : FiveSectorProduct MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorProductInner (fiveSectorProductProjection firstSector first)
      (fiveSectorProductProjection secondSector second) = 0 := by
  cases firstSector <;> cases secondSector <;>
    rcases first with ⟨metric₁, abelian₁, spinC₁, ll₁, boundary₁⟩ <;>
    rcases second with ⟨metric₂, abelian₂, spinC₂, ll₂, boundary₂⟩ <;>
    simp_all [fiveSectorProductInner, fiveSectorProductProjection,
      fiveSectorMetricProjection,
      fiveSectorAbelianProjection, fiveSectorSpinCProjection,
      fiveSectorLLProjection, fiveSectorBoundaryProjection]

end InnerProduct

section Transport

variable
  {E MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
    BoundaryFiniteBV : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup MetricDiffeomorphism]
  [InnerProductSpace Real MetricDiffeomorphism]
  [NormedAddCommGroup AbelianGauge]
  [InnerProductSpace Real AbelianGauge]
  [NormedAddCommGroup PrimitiveSpinCMatter]
  [InnerProductSpace Real PrimitiveSpinCMatter]
  [NormedAddCommGroup LongitudinalLL]
  [InnerProductSpace Real LongitudinalLL]
  [NormedAddCommGroup BoundaryFiniteBV]
  [InnerProductSpace Real BoundaryFiniteBV]

/-- One effective orthogonal coordinate decomposition of an ambient Hilbert
space.  Inner-product preservation is recorded explicitly so that the
construction does not depend on a particular isometry API. -/
structure FiveSectorOrthogonalProductDecomposition where
  decomposition : E ≃L[Real]
    FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
      LongitudinalLL BoundaryFiniteBV
  inner_map : ∀ first second : E,
    fiveSectorProductInner (decomposition first) (decomposition second) =
      inner Real first second

/-- Sector projector transported to the ambient Hilbert space. -/
def FiveSectorOrthogonalProductDecomposition.projection
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (sector : FiveSectorSlot) : E →L[Real] E :=
  data.decomposition.symm.toContinuousLinearMap.comp
    ((fiveSectorProductProjection sector).comp
      data.decomposition.toContinuousLinearMap)

@[simp]
theorem FiveSectorOrthogonalProductDecomposition.projection_apply
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (sector : FiveSectorSlot) (state : E) :
    data.projection sector state =
      data.decomposition.symm
        (fiveSectorProductProjection sector (data.decomposition state)) :=
  rfl

/-- Transported projectors are idempotent. -/
theorem FiveSectorOrthogonalProductDecomposition.projection_idempotent
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (sector : FiveSectorSlot) (state : E) :
    data.projection sector (data.projection sector state) =
      data.projection sector state := by
  apply data.decomposition.injective
  simp [FiveSectorOrthogonalProductDecomposition.projection,
    fiveSectorProductProjection_idempotent]

/-- Distinct transported projectors compose to zero. -/
theorem FiveSectorOrthogonalProductDecomposition.projection_comp_zero
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (first second : FiveSectorSlot) (hDistinct : first ≠ second) :
    (data.projection first).comp (data.projection second) = 0 := by
  ext state
  apply data.decomposition.injective
  simpa [FiveSectorOrthogonalProductDecomposition.projection] using
    congrArg
      (fun map :
        FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
            LongitudinalLL BoundaryFiniteBV →L[Real]
          FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
            LongitudinalLL BoundaryFiniteBV => map (data.decomposition state))
      (fiveSectorProductProjection_comp_zero first second hDistinct)

/-- Transported projectors are self-adjoint. -/
theorem FiveSectorOrthogonalProductDecomposition.projection_selfAdjoint
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (sector : FiveSectorSlot) (first second : E) :
    inner Real (data.projection sector first) second =
      inner Real first (data.projection sector second) := by
  calc
    inner Real (data.projection sector first) second =
        fiveSectorProductInner (data.decomposition (data.projection sector first))
          (data.decomposition second) :=
      (data.inner_map (data.projection sector first) second).symm
    _ = fiveSectorProductInner (fiveSectorProductProjection sector (data.decomposition first))
          (data.decomposition second) := by
      simp [FiveSectorOrthogonalProductDecomposition.projection]
    _ = fiveSectorProductInner (data.decomposition first)
          (fiveSectorProductProjection sector (data.decomposition second)) :=
      fiveSectorProductProjection_selfAdjoint sector _ _
    _ = fiveSectorProductInner (data.decomposition first)
          (data.decomposition (data.projection sector second)) := by
      simp [FiveSectorOrthogonalProductDecomposition.projection]
    _ = inner Real first (data.projection sector second) :=
      data.inner_map first (data.projection sector second)

/-- Images of distinct transported projectors are orthogonal. -/
theorem FiveSectorOrthogonalProductDecomposition.projection_orthogonal
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (firstSector secondSector : FiveSectorSlot)
    (hDistinct : firstSector ≠ secondSector)
    (first second : E) :
    inner Real (data.projection firstSector first)
      (data.projection secondSector second) = 0 := by
  rw [← data.inner_map]
  simp only [FiveSectorOrthogonalProductDecomposition.projection_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact fiveSectorProductProjection_orthogonal firstSector secondSector
    hDistinct (data.decomposition first) (data.decomposition second)

/-- The transported projectors resolve the identity. -/
theorem FiveSectorOrthogonalProductDecomposition.sum_projection_apply
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV))
    (state : E) :
    (∑ sector : FiveSectorSlot, data.projection sector state) = state := by
  apply data.decomposition.injective
  simp only [map_sum,
    FiveSectorOrthogonalProductDecomposition.projection_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact fiveSectorProductProjection_sum_apply (data.decomposition state)

/-- Public orthogonal product-resolution checkpoint. -/
theorem five_sector_orthogonal_product_resolution_gate
    (data : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV)) :
    (∀ sector state,
      data.projection sector (data.projection sector state) =
        data.projection sector state) ∧
      (∀ first second, first ≠ second →
        (data.projection first).comp (data.projection second) = 0) ∧
      (∀ sector first second,
        inner Real (data.projection sector first) second =
          inner Real first (data.projection sector second)) ∧
      (∀ first second, first ≠ second → ∀ x y,
        inner Real (data.projection first x) (data.projection second y) = 0) ∧
      (∀ state, ∑ sector : FiveSectorSlot,
        data.projection sector state = state) :=
  ⟨data.projection_idempotent,
    data.projection_comp_zero,
    data.projection_selfAdjoint,
    data.projection_orthogonal,
    data.sum_projection_apply⟩

end Transport

end
end P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
end JanusFormal
