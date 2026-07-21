import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D

/-!
# Exact collar--cap overlap on the fiber cover

The abstract range of the restricted tubular diffeomorphism is exactly the
strict latitude band `0 < latitude < sin 1`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D

theorem mem_positiveUnitLatitudeBandOpen_iff
    (point : equatorialSphericalBandOpen) :
    point ∈ positiveUnitLatitudeBandOpen ↔
      0 < point.1.1 0 ∧ point.1.1 0 < Real.sin 1 := by
  constructor
  · rintro ⟨parameter, rfl⟩
    change 0 < Real.sin parameter.1.2.1 ∧
      Real.sin parameter.1.2.1 < Real.sin 1
    have hNormalRange : parameter.1.2.1 ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨parameter.1.2.2.1.le, parameter.1.2.2.2.le⟩
    have hZeroRange : (0 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hOneRange : (1 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_three]
    constructor
    · simpa using Real.strictMonoOn_sin hZeroRange hNormalRange parameter.2.1
    · exact Real.strictMonoOn_sin hNormalRange hOneRange parameter.2.2
  · rintro ⟨hPositive, hUpper⟩
    let inverse := equatorialTubularSmoothInverse point
    have hMap : equatorialTubularSmoothMap inverse = point :=
      equatorialTubularSmoothMap_inverse point
    have hSin : Real.sin inverse.2.1 = point.1.1 0 := by
      exact congrArg (fun value : equatorialSphericalBandOpen => value.1.1 0)
        hMap
    have hNormalRange : inverse.2.1 ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨inverse.2.2.1.le, inverse.2.2.2.le⟩
    have hZeroRange : (0 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hOneRange : (1 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_three]
    have hNormalPositive : 0 < inverse.2.1 :=
      (Real.strictMonoOn_sin.lt_iff_lt hZeroRange hNormalRange).mp (by
        simpa [hSin] using hPositive)
    have hNormalUpper : inverse.2.1 < 1 :=
      (Real.strictMonoOn_sin.lt_iff_lt hNormalRange hOneRange).mp (by
        simpa [hSin] using hUpper)
    exact ⟨⟨inverse, hNormalPositive, hNormalUpper⟩, hMap⟩

end
end P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D
end JanusFormal
