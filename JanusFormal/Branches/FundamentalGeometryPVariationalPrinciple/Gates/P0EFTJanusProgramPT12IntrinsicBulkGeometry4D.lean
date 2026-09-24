import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D

/-! A concrete intrinsic Candidate-A geometry with a proved invertible Sylvester operator. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Equal unit conformal factors on the existing intrinsic Lorentz metric. -/
def intrinsicBulkGeometry : GlobalCandidateAGeometry period hPeriod :=
  conformalGlobalCandidateAGeometry period hPeriod
    (constantSmoothField period hPeriod Real 1) (constantSmoothField period hPeriod Real 1)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one)

theorem intrinsicBulkGeometry_rootAt (point : EffectiveQuotient period hPeriod) :
    (intrinsicBulkGeometry period hPeriod).rootAt point =
      ContinuousLinearMap.id Real (TangentSpace coverModelWithCorners point) := by
  change Real.sqrt ((1 : Real) / 1) • ContinuousLinearMap.id Real _ = _
  simp

theorem intrinsicBulkGeometry_sylvester_apply
    (point : EffectiveQuotient period hPeriod)
    (variation : TangentSpace coverModelWithCorners point →L[Real]
      TangentSpace coverModelWithCorners point) :
    intrinsicCandidateASylvesterAt period hPeriod (intrinsicBulkGeometry period hPeriod)
        point variation = (2 : Real) • variation := by
  rw [intrinsicCandidateASylvesterAt_apply, intrinsicBulkGeometry_rootAt]
  simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  exact (two_smul Real variation).symm

/-- The inverse is multiplication by one half, proved on the actual intrinsic endomorphisms. -/
theorem intrinsicBulkGeometry_sylvester_bijective
    (point : EffectiveQuotient period hPeriod) :
    Function.Bijective (intrinsicCandidateASylvesterAt period hPeriod
      (intrinsicBulkGeometry period hPeriod) point) := by
  constructor
  · intro first second hEqual
    have hScaled := congrArg (fun variation => (1 / 2 : Real) • variation) hEqual
    simpa only [intrinsicBulkGeometry_sylvester_apply, smul_smul,
      show (1 / 2 : Real) * 2 = 1 by norm_num, one_smul] using hScaled
  · intro variation
    refine ⟨(1 / 2 : Real) • variation, ?_⟩
    rw [intrinsicBulkGeometry_sylvester_apply, smul_smul]
    norm_num

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
