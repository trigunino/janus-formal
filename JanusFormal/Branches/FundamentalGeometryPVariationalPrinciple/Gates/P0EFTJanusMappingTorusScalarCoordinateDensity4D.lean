import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCoordinateFields4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! The seven explicit smooth coordinates separate the full mapping torus. -/
namespace JanusFormal.P0EFTJanusMappingTorusScalarCoordinateDensity4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusScalarCoordinateFields4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D
variable (period : Real) [hPos : Fact (0 < period)]
private abbrev Base := MappingTorus (reflectedSphereData period hPos.out.ne')
local instance : ChartedSpace CoverModel (Base period) :=
  reflectedSphereQuotientChartedSpace period hPos.out.ne'
local instance : IsManifold coverModelWithCorners ω (Base period) :=
  reflectedSphereQuotient_isManifold period hPos.out.ne'
local instance : CompactSpace (Base period) :=
  reflectedSphereQuotientCompactSpace period hPos.out.ne'

theorem scalarCoordinates_injective :
    Function.Injective (fun point : Base period => fun index => scalarCoordinate period index point) := by
  intro first second hEqual
  obtain ⟨p, rfl⟩ := mappingTorusMk_surjective _ first
  obtain ⟨q, rfl⟩ := mappingTorusMk_surjective _ second
  have hFields (i) := congrFun hEqual i
  have hFourier : fourier 1 (p.time : AddCircle period) = fourier 1 (q.time : AddCircle period) := by
    apply Complex.ext
    · simpa only [scalarCoordinate_time_re_mk] using hFields (.inr (.inr 0))
    · simpa only [scalarCoordinate_time_im_mk] using hFields (.inr (.inr 1))
  have hTimeCircle : (p.time : AddCircle period) = (q.time : AddCircle period) := by
    rw [fourier_one, fourier_one] at hFourier
    exact AddCircle.injective_toCircle hPos.out.ne' (Subtype.ext hFourier)
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp hTimeCircle)
  have hTime : p.time = (n +ᵥ q).time := by
    change p.time = q.time + (n : Real) * period
    simp only [zsmul_eq_mul] at hn
    linarith
  have hClass : mappingTorusMk _ (n +ᵥ q) = mappingTorusMk _ q :=
    (mappingTorusMk_eq_iff_exists_vadd _ _ _).mpr ⟨n, rfl⟩
  have hShift (i) : scalarCoordinate period i (mappingTorusMk _ p) =
      scalarCoordinate period i (mappingTorusMk _ (n +ᵥ q)) :=
    (hFields i).trans (congrArg (scalarCoordinate period i) hClass).symm
  have hFiber : p.fiber = (n +ᵥ q).fiber := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun axis => ?_) i
    · obtain ⟨phase, hPhase⟩ := exists_canonicalNormalRotationPhase_ne_zero period p.time
      have h := hShift (.inr (.inl phase))
      simp only [scalarCoordinate_twisted_mk] at h
      rw [← hTime] at h
      exact mul_right_cancel₀ hPhase h
    · exact hShift (.inl axis)
  exact (mappingTorusMk_eq_iff_exists_vadd _ _ _).mpr
    ⟨n, MappingTorusCover.ext hFiber.symm hTime.symm⟩

def scalarCoordinateContinuous (i : ScalarCoordinateIndex) : C(Base period, Real) :=
  ⟨scalarCoordinate period i, (scalarCoordinate period i).contMDiff_toFun.continuous⟩

def scalarCoordinateAlgebra : Subalgebra Real C(Base period, Real) :=
  Algebra.adjoin Real (Set.range (scalarCoordinateContinuous period))

theorem scalarCoordinateAlgebra_separatesPoints : (scalarCoordinateAlgebra period).SeparatesPoints := by
  intro p q hNe
  have hIndex : ∃ i, scalarCoordinate period i p ≠ scalarCoordinate period i q := by
    by_contra h
    push Not at h
    exact hNe (scalarCoordinates_injective period (funext h))
  obtain ⟨i, hi⟩ := hIndex
  exact ⟨_, ⟨scalarCoordinateContinuous period i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, hi⟩

theorem scalarCoordinateAlgebra_smooth (f : scalarCoordinateAlgebra period) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞ (f.val : Base period → Real) := by
  rcases f with ⟨f, hf⟩
  change ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞ f
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact (scalarCoordinate period i).contMDiff_toFun
  | algebraMap r => exact contMDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg

theorem scalarCoordinateAlgebra_dense : Dense (scalarCoordinateAlgebra period : Set C(Base period, Real)) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (scalarCoordinateAlgebra period) (scalarCoordinateAlgebra_separatesPoints period)
  rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, h]
  rfl

end
end JanusFormal.P0EFTJanusMappingTorusScalarCoordinateDensity4D
