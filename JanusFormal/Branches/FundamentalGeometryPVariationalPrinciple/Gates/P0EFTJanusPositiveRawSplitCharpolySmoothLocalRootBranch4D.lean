import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

/-!
# Smooth finite-matrix local root branches

Matrix squaring is polynomial, so the existing inverse-function charts have
smooth inverse branches.  This upgrades the former order-two interface to
`C∞` without changing its source or target.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawSplitCharpolySmoothLocalRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius RightActions Topology
open Set
open P0EFTJanusPositiveRawSplitCharpolyLocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D

abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

theorem canonicalMatrixSquare_contDiff_infty :
    ContDiff Real ∞ canonicalMatrixSquare := by
  change @ContDiff Real _ Matrix4
    NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace Matrix4) Matrix4
    NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace Matrix4) ∞
    (fun root : Matrix4 => root * root)
  simpa using (contDiff_id.mul contDiff_id :
    ContDiff Real ∞ (fun root : Matrix4 => root * root))

/-- The existing canonical local inverse branch is actually smooth. -/
theorem canonicalC2LocalRootBranchAt_contDiffAt_infty
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    ContDiffAt Real ∞ (canonicalC2LocalRootBranchAt root hBijective)
      (canonicalMatrixSquare root) := by
  have hTarget : canonicalMatrixSquare root ∈
      (canonicalC2LocalSquareChartAt root hBijective).target :=
    (canonicalC2LocalSquareChartAt root hBijective).map_source
      (root_mem_canonicalC2LocalSquareChartAt_source root hBijective)
  apply (canonicalC2LocalSquareChartAt root hBijective).contDiffAt_symm
    hTarget (f₀' := canonicalSylvesterEquivOfBijective root hBijective)
  · have hCenter :
        (canonicalC2LocalSquareChartAt root hBijective).symm
            (canonicalMatrixSquare root) = root :=
      (canonicalC2LocalSquareChartAt root hBijective).left_inv
        (root_mem_canonicalC2LocalSquareChartAt_source root hBijective)
    have hEquiv :
        (canonicalSylvesterEquivOfBijective root hBijective :
          Matrix4 →L[Real] Matrix4) =
          canonicalSylvesterOperator
            ((canonicalC2LocalSquareChartAt root hBijective).symm
              (canonicalMatrixSquare root)) := by
      rw [hCenter]
      exact canonicalSylvesterEquivOfBijective_forward_eq root hBijective
    exact (canonicalMatrixSquare_hasFDerivAt
      ((canonicalC2LocalSquareChartAt root hBijective).symm
        (canonicalMatrixSquare root))).congr_fderiv hEquiv.symm
  · exact canonicalMatrixSquare_contDiff_infty.contDiffAt

/-- A continuous regular root of a smooth finite-matrix target is smooth at
the selected point. -/
theorem continuousRegularRootLift_contDiffAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (target rootLift : E → Matrix4) (point : E)
    (hBijective : Function.Bijective
      (canonicalSylvesterOperator (rootLift point)))
    (hRoot : ContinuousAt rootLift point)
    (hSquare : ∀ nearby,
      canonicalMatrixSquare (rootLift nearby) = target nearby)
    (hTarget : ContDiffAt Real ∞ target point) :
    ContDiffAt Real ∞ rootLift point := by
  have hBase : target point = canonicalMatrixSquare (rootLift point) :=
    (hSquare point).symm
  have hBranch : ContDiffAt Real ∞
      (canonicalC2LocalRootBranchAt (rootLift point) hBijective)
      (target point) := by
    simpa only [hBase] using
      canonicalC2LocalRootBranchAt_contDiffAt_infty
        (rootLift point) hBijective
  have hLocal : ContDiffAt Real ∞
      (canonicalC2LocalTargetLift target (rootLift point) hBijective) point :=
    hBranch.comp point hTarget
  exact hLocal.congr_of_eventuallyEq
    (continuousRegularRootLift_eventuallyEq_canonicalC2LocalTargetLift
      target rootLift point hBijective hRoot hSquare)

theorem continuousRegularRootLift_contDiff_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (target rootLift : E → Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (rootLift point)))
    (hRoot : Continuous rootLift)
    (hSquare : ∀ point,
      canonicalMatrixSquare (rootLift point) = target point)
    (hTarget : ContDiff Real ∞ target) :
    ContDiff Real ∞ rootLift := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact continuousRegularRootLift_contDiffAt_infty target rootLift point
    (hRegular point) hRoot.continuousAt hSquare hTarget.contDiffAt

/-- The positive raw inverse branch is smooth at every point of its existing
open target. -/
theorem positiveRawContDiffLocalRootBranch_contDiffAt_infty
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target)
    (nearby : Matrix4)
    (hNearby : nearby ∈
      positiveRawContDiffLocalRootTarget target hSpectrum) :
    ContDiffAt Real ∞
      (positiveRawContDiffLocalRootBranch target hSpectrum) nearby := by
  have hSource :=
    (positiveRawContDiffLocalSquareChart target hSpectrum).map_target hNearby
  rw [positiveRawContDiffLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  apply (positiveRawContDiffLocalSquareChart target hSpectrum).contDiffAt_symm
    hNearby (f₀' := equiv)
  · exact (canonicalMatrixSquare_hasFDerivAt
      ((positiveRawContDiffLocalSquareChart target hSpectrum).symm nearby)
        ).congr_fderiv hEquiv.symm
  · exact canonicalMatrixSquare_contDiff_infty.contDiffAt

theorem positiveRawContDiffLocalRootBranch_contDiffOn_infty
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    ContDiffOn Real ∞
      (positiveRawContDiffLocalRootBranch target hSpectrum)
      (positiveRawContDiffLocalRootTarget target hSpectrum) := by
  intro nearby hNearby
  exact (positiveRawContDiffLocalRootBranch_contDiffAt_infty
    target hSpectrum nearby hNearby).contDiffWithinAt

/-- Gate marker for the smooth local finite-matrix square-root branch. -/
theorem positive_raw_split_charpoly_smooth_local_root_branch_gate
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsOpen (positiveRawContDiffLocalRootTarget target hSpectrum) ∧
      target ∈ positiveRawContDiffLocalRootTarget target hSpectrum ∧
      ContDiffOn Real ∞
        (positiveRawContDiffLocalRootBranch target hSpectrum)
        (positiveRawContDiffLocalRootTarget target hSpectrum) :=
  ⟨positiveRawContDiffLocalRootTarget_isOpen target hSpectrum,
    target_mem_positiveRawContDiffLocalRootTarget target hSpectrum,
    positiveRawContDiffLocalRootBranch_contDiffOn_infty target hSpectrum⟩

end

end P0EFTJanusPositiveRawSplitCharpolySmoothLocalRootBranch4D
end JanusFormal
