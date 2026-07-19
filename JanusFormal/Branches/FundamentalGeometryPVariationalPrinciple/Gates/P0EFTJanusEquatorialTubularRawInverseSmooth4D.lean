import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularRawInverseSmooth4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D

def rawEquatorialTubularTailInverse
    (point : Fin 4 → Real) : Fin 3 → Real :=
  fun index => point index.succ /
    Real.cos (rawEquatorialTubularNormalInverse point)

theorem rawEquatorialTubularTailInverse_contDiffOn :
    ContDiffOn Real ∞ rawEquatorialTubularTailInverse RawSphericalTubularBand := by
  rw [contDiffOn_pi]
  intro index point hPoint
  change |point 0| < 1 at hPoint
  have hNormalSmooth : ContDiffWithinAt Real ∞
      rawEquatorialTubularNormalInverse RawSphericalTubularBand point :=
    rawEquatorialTubularNormalInverse_contDiffOn point hPoint
  have hDenominatorSmooth : ContDiffWithinAt Real ∞
      (fun coordinate => Real.cos (rawEquatorialTubularNormalInverse coordinate))
      RawSphericalTubularBand point :=
    Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt point hNormalSmooth
  have hArcsin : Real.arcsin (point 0) ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hPoint).1,
      Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp hPoint).2⟩
  have hCos : Real.cos (rawEquatorialTubularNormalInverse point) ≠ 0 := by
    exact (Real.cos_pos_of_mem_Ioo hArcsin).ne'
  exact ((contDiffAt_apply (𝕜 := Real) (E := Real) (n := ∞)
    index.succ point).contDiffWithinAt).div hDenominatorSmooth hCos

theorem rawEquatorialTubularTailInverse_continuousOn :
    ContinuousOn rawEquatorialTubularTailInverse RawSphericalTubularBand :=
  rawEquatorialTubularTailInverse_contDiffOn.continuousOn

theorem rawEquatorialTubularInverse_contDiffOn :
    ContDiffOn Real ∞
      (fun point =>
        (rawEquatorialTubularTailInverse point,
          rawEquatorialTubularNormalInverse point))
      RawSphericalTubularBand :=
  rawEquatorialTubularTailInverse_contDiffOn.prodMk
    rawEquatorialTubularNormalInverse_contDiffOn

end
end P0EFTJanusEquatorialTubularRawInverseSmooth4D
end JanusFormal
