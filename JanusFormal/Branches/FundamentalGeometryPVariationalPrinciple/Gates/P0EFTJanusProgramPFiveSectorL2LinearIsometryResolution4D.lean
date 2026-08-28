import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D

/-!
# Five-sector L² linear-isometry resolution

The ordinary product used by the legacy five-sector resolution carries the
maximum norm, so it is not the target of a Hilbert direct-sum isometry.  This
module uses nested `WithLp 2` products for the genuine Hilbert target, then
forgets the L² norms through a continuous linear equivalence to the ordinary
right-associated product.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2LinearIsometryResolution4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D

/-- Innermost L² tail of the five-sector product. -/
abbrev FiveSectorL2Tail3 (LongitudinalLL BoundaryFiniteBV : Type*) :=
  WithLp 2 (LongitudinalLL × BoundaryFiniteBV)

/-- Second L² tail of the five-sector product. -/
abbrev FiveSectorL2Tail2
    (PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV : Type*) :=
  WithLp 2
    (PrimitiveSpinCMatter ×
      FiveSectorL2Tail3 LongitudinalLL BoundaryFiniteBV)

/-- First L² tail of the five-sector product. -/
abbrev FiveSectorL2Tail1
    (AbelianGauge PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV : Type*) :=
  WithLp 2
    (AbelianGauge ×
      FiveSectorL2Tail2 PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV)

/-- Right-associated Hilbert L² product of the five physical sectors. -/
abbrev FiveSectorL2Product
    (MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
      BoundaryFiniteBV : Type*) :=
  WithLp 2
    (MetricDiffeomorphism ×
      FiveSectorL2Tail1 AbelianGauge PrimitiveSpinCMatter LongitudinalLL
        BoundaryFiniteBV)

section Forget

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

/-- Forget the innermost L² norm while retaining the vector coordinates. -/
def fiveSectorL2Tail3Forget :
    FiveSectorL2Tail3 LongitudinalLL BoundaryFiniteBV ≃L[Real]
      LongitudinalLL × BoundaryFiniteBV :=
  WithLp.prodContinuousLinearEquiv 2 Real LongitudinalLL BoundaryFiniteBV

/-- Forget the second L² tail, recursively. -/
def fiveSectorL2Tail2Forget :
    FiveSectorL2Tail2 PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV ≃L[Real]
      PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV) :=
  (WithLp.prodContinuousLinearEquiv 2 Real PrimitiveSpinCMatter
      (FiveSectorL2Tail3 LongitudinalLL BoundaryFiniteBV)).trans
    ((ContinuousLinearEquiv.refl Real PrimitiveSpinCMatter).prodCongr
      fiveSectorL2Tail3Forget)

/-- Forget the first L² tail, recursively. -/
def fiveSectorL2Tail1Forget :
    FiveSectorL2Tail1 AbelianGauge PrimitiveSpinCMatter LongitudinalLL
        BoundaryFiniteBV ≃L[Real]
      AbelianGauge ×
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV)) :=
  (WithLp.prodContinuousLinearEquiv 2 Real AbelianGauge
      (FiveSectorL2Tail2 PrimitiveSpinCMatter LongitudinalLL
        BoundaryFiniteBV)).trans
    ((ContinuousLinearEquiv.refl Real AbelianGauge).prodCongr
      fiveSectorL2Tail2Forget)

/-- Continuous linear forgetting map from the Hilbert L² product to the raw
right-associated product.  It is deliberately not claimed to be an isometry:
the codomain carries the ordinary product (maximum) norm. -/
def fiveSectorL2Forget :
    FiveSectorL2Product MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV ≃L[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV :=
  (WithLp.prodContinuousLinearEquiv 2 Real MetricDiffeomorphism
      (FiveSectorL2Tail1 AbelianGauge PrimitiveSpinCMatter LongitudinalLL
        BoundaryFiniteBV)).trans
    ((ContinuousLinearEquiv.refl Real MetricDiffeomorphism).prodCongr
      fiveSectorL2Tail1Forget)

@[simp]
theorem fiveSectorL2Forget_apply
    (state : FiveSectorL2Product MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorL2Forget state =
      (state.fst,
        (state.snd.fst,
          (state.snd.snd.fst,
            (state.snd.snd.snd.fst, state.snd.snd.snd.snd)))) := by
  rfl

/-- The recursively forgotten coordinates carry exactly the explicit sum
inner product used by `FiveSectorOrthogonalProductDecomposition`. -/
theorem fiveSectorL2Forget_inner
    (first second : FiveSectorL2Product MetricDiffeomorphism AbelianGauge
      PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    fiveSectorProductInner (fiveSectorL2Forget first)
        (fiveSectorL2Forget second) =
      inner Real first second := by
  simp [fiveSectorProductInner, WithLp.prod_inner_apply]
  ring

end Forget

section Axes

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

/-- Continuous metric/diffeomorphism axis in the L² product. -/
def fiveSectorL2MetricAxis :
    MetricDiffeomorphism →L[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV :=
  fiveSectorL2Forget.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl Real MetricDiffeomorphism
      (AbelianGauge ×
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV))))

/-- Continuous Abelian-gauge axis in the L² product. -/
def fiveSectorL2AbelianAxis :
    AbelianGauge →L[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV :=
  fiveSectorL2Forget.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr Real MetricDiffeomorphism
      (AbelianGauge ×
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV)))).comp
      (ContinuousLinearMap.inl Real AbelianGauge
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV))))

/-- Continuous primitive-SpinC-matter axis in the L² product. -/
def fiveSectorL2SpinCAxis :
    PrimitiveSpinCMatter →L[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV :=
  fiveSectorL2Forget.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr Real MetricDiffeomorphism
      (AbelianGauge ×
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV)))).comp
      ((ContinuousLinearMap.inr Real AbelianGauge
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV))).comp
        (ContinuousLinearMap.inl Real PrimitiveSpinCMatter
          (LongitudinalLL × BoundaryFiniteBV))))

/-- Continuous longitudinal/LL axis in the L² product. -/
def fiveSectorL2LongitudinalAxis :
    LongitudinalLL →L[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV :=
  fiveSectorL2Forget.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr Real MetricDiffeomorphism
      (AbelianGauge ×
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV)))).comp
      ((ContinuousLinearMap.inr Real AbelianGauge
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV))).comp
        ((ContinuousLinearMap.inr Real PrimitiveSpinCMatter
          (LongitudinalLL × BoundaryFiniteBV)).comp
            (ContinuousLinearMap.inl Real LongitudinalLL BoundaryFiniteBV))))

/-- Continuous boundary/finite-BV axis in the L² product. -/
def fiveSectorL2BoundaryAxis :
    BoundaryFiniteBV →L[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV :=
  fiveSectorL2Forget.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr Real MetricDiffeomorphism
      (AbelianGauge ×
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV)))).comp
      ((ContinuousLinearMap.inr Real AbelianGauge
        (PrimitiveSpinCMatter × (LongitudinalLL × BoundaryFiniteBV))).comp
        ((ContinuousLinearMap.inr Real PrimitiveSpinCMatter
          (LongitudinalLL × BoundaryFiniteBV)).comp
            (ContinuousLinearMap.inr Real LongitudinalLL BoundaryFiniteBV))))

@[simp]
theorem fiveSectorL2Forget_metricAxis_apply (metric : MetricDiffeomorphism) :
    fiveSectorL2Forget
        (fiveSectorL2MetricAxis
          (MetricDiffeomorphism := MetricDiffeomorphism)
          (AbelianGauge := AbelianGauge)
          (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
          (LongitudinalLL := LongitudinalLL)
          (BoundaryFiniteBV := BoundaryFiniteBV) metric) =
      (metric, 0) := by
  simp [fiveSectorL2MetricAxis]

@[simp]
theorem fiveSectorL2Forget_abelianAxis_apply (abelian : AbelianGauge) :
    fiveSectorL2Forget
        (fiveSectorL2AbelianAxis
          (MetricDiffeomorphism := MetricDiffeomorphism)
          (AbelianGauge := AbelianGauge)
          (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
          (LongitudinalLL := LongitudinalLL)
          (BoundaryFiniteBV := BoundaryFiniteBV) abelian) =
      (0, (abelian, 0)) := by
  simp [fiveSectorL2AbelianAxis]

@[simp]
theorem fiveSectorL2Forget_spinCAxis_apply (spinC : PrimitiveSpinCMatter) :
    fiveSectorL2Forget
        (fiveSectorL2SpinCAxis
          (MetricDiffeomorphism := MetricDiffeomorphism)
          (AbelianGauge := AbelianGauge)
          (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
          (LongitudinalLL := LongitudinalLL)
          (BoundaryFiniteBV := BoundaryFiniteBV) spinC) =
      (0, (0, (spinC, 0))) := by
  simp [fiveSectorL2SpinCAxis]

@[simp]
theorem fiveSectorL2Forget_longitudinalAxis_apply (longitudinal : LongitudinalLL) :
    fiveSectorL2Forget
        (fiveSectorL2LongitudinalAxis
          (MetricDiffeomorphism := MetricDiffeomorphism)
          (AbelianGauge := AbelianGauge)
          (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
          (LongitudinalLL := LongitudinalLL)
          (BoundaryFiniteBV := BoundaryFiniteBV) longitudinal) =
      (0, (0, (0, (longitudinal, 0)))) := by
  simp [fiveSectorL2LongitudinalAxis]

@[simp]
theorem fiveSectorL2Forget_boundaryAxis_apply (boundary : BoundaryFiniteBV) :
    fiveSectorL2Forget
        (fiveSectorL2BoundaryAxis
          (MetricDiffeomorphism := MetricDiffeomorphism)
          (AbelianGauge := AbelianGauge)
          (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
          (LongitudinalLL := LongitudinalLL)
          (BoundaryFiniteBV := BoundaryFiniteBV) boundary) =
      (0, (0, (0, (0, boundary)))) := by
  simp [fiveSectorL2BoundaryAxis]

end Axes

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

/-- Turn a genuine Hilbert L² isometry into the legacy raw-product
decomposition without identifying the L² norm with the product maximum norm. -/
def fiveSectorOrthogonalProductDecompositionOfL2Isometry
    (frame : E ≃ₗᵢ[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV) :
    FiveSectorOrthogonalProductDecomposition
      (E := E)
      (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV) where
  decomposition := frame.toContinuousLinearEquiv.trans fiveSectorL2Forget
  inner_map := by
    intro first second
    change fiveSectorProductInner
      (fiveSectorL2Forget (frame first))
      (fiveSectorL2Forget (frame second)) = inner Real first second
    calc
      _ = inner Real (frame first) (frame second) :=
        fiveSectorL2Forget_inner (frame first) (frame second)
      _ = inner Real first second := frame.inner_map_map first second

/-- Pythagoras gate generated from one Hilbert L² coordinate isometry. -/
theorem five_sector_l2_linear_isometry_pythagoras_gate
    (frame : E ≃ₗᵢ[Real]
      FiveSectorL2Product MetricDiffeomorphism AbelianGauge
        PrimitiveSpinCMatter LongitudinalLL BoundaryFiniteBV)
    (state : E) :
    ‖state‖ ^ 2 =
      ∑ sector : FiveSectorSlot,
        ‖(fiveSectorOrthogonalProductDecompositionOfL2Isometry frame).projection
          sector state‖ ^ 2 :=
  fiveSectorProjection_norm_sq_sum
    (fiveSectorOrthogonalProductDecompositionOfL2Isometry frame) state

end Transport

end

end P0EFTJanusProgramPFiveSectorL2LinearIsometryResolution4D
end JanusFormal
