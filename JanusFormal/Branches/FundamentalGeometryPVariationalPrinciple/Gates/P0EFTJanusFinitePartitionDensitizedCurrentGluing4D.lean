import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace JanusFormal
namespace P0EFTJanusFinitePartitionDensitizedCurrentGluing4D
set_option autoImplicit false
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem finite_partition_derivative_cancellation
    (weight dWeight : ι → Real → Real) (point : Real)
    (hWeight : ∀ index, HasDerivAt (weight index) (dWeight index point) point)
    (hPartition : ∀ coordinate, ∑ index, weight index coordinate = 1) :
    ∑ index, dWeight index point = 0 := by
  have hSum : HasDerivAt (fun coordinate => ∑ index, weight index coordinate)
      (∑ index, dWeight index point) point := by
    exact HasDerivAt.fun_sum (fun index _ => hWeight index)
  have hConst : HasDerivAt (fun _ : Real => (1 : Real)) 0 point :=
    hasDerivAt_const point 1
  have hConst' : HasDerivAt (fun coordinate => ∑ index, weight index coordinate)
      0 point := by
    convert hConst using 1
    funext coordinate
    exact hPartition coordinate
  exact hSum.unique hConst'

theorem finite_partition_weighted_current_hasDerivAt
    (weight dWeight : ι → Real → Real)
    (current divergence : Real → Real) (point : Real)
    (hWeight : ∀ index, HasDerivAt (weight index) (dWeight index point) point)
    (hCurrent : HasDerivAt current (divergence point) point) :
    HasDerivAt
      (fun coordinate => ∑ index, weight index coordinate * current coordinate)
      (∑ index,
        (dWeight index point * current point +
          weight index point * divergence point)) point := by
  exact HasDerivAt.fun_sum (fun index _ => (hWeight index).mul hCurrent)

theorem finite_partition_densitized_leibniz_cancellation
    (weight dWeight : ι → Real → Real)
    (current divergence : Real → Real) (point : Real)
    (hWeight : ∀ index, HasDerivAt (weight index) (dWeight index point) point)
    (hPartition : ∀ coordinate, ∑ index, weight index coordinate = 1) :
    (∑ index,
        (dWeight index point * current point +
          weight index point * divergence point)) = divergence point := by
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hCancel := finite_partition_derivative_cancellation
    weight dWeight point hWeight hPartition
  rw [hCancel, zero_mul]
  rw [← Finset.sum_mul]
  rw [hPartition point, one_mul, zero_add]

/-- A finite partition of unity glues identical real current representatives:
the partition-weighted sum has exactly the original divergence. -/
theorem finite_partition_glued_current_hasDerivAt
    (weight dWeight : ι → Real → Real)
    (current divergence : Real → Real) (point : Real)
    (hWeight : ∀ index, HasDerivAt (weight index) (dWeight index point) point)
    (hPartition : ∀ coordinate, ∑ index, weight index coordinate = 1)
    (hCurrent : HasDerivAt current (divergence point) point) :
    HasDerivAt
      (fun coordinate => ∑ index, weight index coordinate * current coordinate)
      (divergence point) point := by
  convert finite_partition_weighted_current_hasDerivAt
    weight dWeight current divergence point hWeight hCurrent using 1
  exact (finite_partition_densitized_leibniz_cancellation
    weight dWeight current divergence point hWeight hPartition).symm

theorem finite_partition_glued_current_eq_current
    (weight : ι → Real → Real) (current : Real → Real)
    (hPartition : ∀ coordinate, ∑ index, weight index coordinate = 1)
    (coordinate : Real) :
    (∑ index, weight index coordinate * current coordinate) = current coordinate := by
  rw [← Finset.sum_mul, hPartition coordinate, one_mul]

end
end P0EFTJanusFinitePartitionDensitizedCurrentGluing4D
end JanusFormal
