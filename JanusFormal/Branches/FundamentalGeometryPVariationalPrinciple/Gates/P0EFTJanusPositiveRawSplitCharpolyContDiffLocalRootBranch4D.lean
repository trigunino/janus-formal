import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolyLocalRootBranch4D

/-!
# Smooth local root branches on the positive split raw locus

The existing spectral root and Sylvester-bijectivity bricks build a `C²`
inverse-function chart, restricted to the open set where its derivative stays
a continuous linear equivalence. Translating the raw matrix target gives an
open perturbation domain containing `0`, as required by the local
variational-chart interface.

This is a general pointwise matrix statement around every positive split raw
target.  It is not a diagonal or Minkowski specialization and does not claim a
global smooth-field lift.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius RightActions Topology
open Set
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRawSplitCharpolyLocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D

abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyLocalRootBranch4D.Matrix4

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

/-- Matrix squaring in the canonical normed-algebra topology. -/
def canonicalMatrixSquare (root : Matrix4) : Matrix4 := root * root

/-- Canonical-topology Sylvester family. -/
def canonicalSylvesterFamily :
    Matrix4 →L[Real] Matrix4 →L[Real] Matrix4 :=
  ContinuousLinearMap.mul Real Matrix4 +
    (ContinuousLinearMap.mul Real Matrix4).flip

def canonicalSylvesterOperator (root : Matrix4) :
    Matrix4 →L[Real] Matrix4 :=
  canonicalSylvesterFamily root

@[simp]
theorem canonicalSylvesterOperator_apply (root variation : Matrix4) :
    canonicalSylvesterOperator root variation =
      root * variation + variation * root :=
  rfl

/-- Its derivative is the canonical Sylvester operator. -/
theorem canonicalMatrixSquare_hasFDerivAt (root : Matrix4) :
    HasFDerivAt canonicalMatrixSquare
      (canonicalSylvesterOperator root) root := by
  have hIdentity : HasFDerivAt (fun point : Matrix4 => point)
      (ContinuousLinearMap.id Real Matrix4) root :=
    hasFDerivAt_id root
  exact (hIdentity.mul' hIdentity).congr_fderiv rfl

/-- Matrix squaring has the `C²` regularity needed by the Hessian interface. -/
theorem canonicalMatrixSquare_contDiff_two :
    ContDiff Real 2 canonicalMatrixSquare := by
  change @ContDiff Real _ Matrix4
    NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace Matrix4) Matrix4
    NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace Matrix4) 2
    (fun root : Matrix4 => root * root)
  simpa using (contDiff_id.mul contDiff_id :
    ContDiff Real 2 (fun root : Matrix4 => root * root))

/-- A bijective canonical Sylvester derivative, packaged as a continuous
linear equivalence. -/
def canonicalSylvesterEquivOfBijective
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    Matrix4 ≃L[Real] Matrix4 :=
  (LinearEquiv.ofBijective
    (canonicalSylvesterOperator root).toLinearMap hBijective)
      |>.toContinuousLinearEquiv

theorem canonicalSylvesterEquivOfBijective_forward_eq
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    (canonicalSylvesterEquivOfBijective root hBijective :
      Matrix4 →L[Real] Matrix4) = canonicalSylvesterOperator root := by
  apply ContinuousLinearMap.ext
  intro variation
  rfl

/-- The `C²` inverse-function chart at an arbitrary Sylvester-regular root. -/
def canonicalC2LocalSquareChartAt
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    OpenPartialHomeomorph Matrix4 Matrix4 :=
  canonicalMatrixSquare_contDiff_two.contDiffAt.toOpenPartialHomeomorph
    canonicalMatrixSquare
    ((canonicalMatrixSquare_hasFDerivAt root).congr_fderiv
      (canonicalSylvesterEquivOfBijective_forward_eq
        root hBijective).symm)
    (by norm_num)

theorem root_mem_canonicalC2LocalSquareChartAt_source
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    root ∈ (canonicalC2LocalSquareChartAt root hBijective).source := by
  exact canonicalMatrixSquare_contDiff_two.contDiffAt
    |>.mem_toOpenPartialHomeomorph_source
      ((canonicalMatrixSquare_hasFDerivAt root).congr_fderiv
        (canonicalSylvesterEquivOfBijective_forward_eq
          root hBijective).symm)
      (by norm_num)

/-- Canonical `C²` square-root branch at an arbitrary regular root. -/
def canonicalC2LocalRootBranchAt
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    Matrix4 → Matrix4 :=
  (canonicalC2LocalSquareChartAt root hBijective).symm

theorem canonicalC2LocalRootBranchAt_center
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    canonicalC2LocalRootBranchAt root hBijective
        (canonicalMatrixSquare root) = root := by
  exact (canonicalC2LocalSquareChartAt root hBijective).left_inv
    (root_mem_canonicalC2LocalSquareChartAt_source root hBijective)

theorem canonicalC2LocalRootBranchAt_contDiffAt
    (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    ContDiffAt Real 2 (canonicalC2LocalRootBranchAt root hBijective)
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
  · exact canonicalMatrixSquare_contDiff_two.contDiffAt

/-- Pull the canonical `C²` local root branch back along a target family. -/
def canonicalC2LocalTargetLift {E : Type*}
    (target : E → Matrix4) (root : Matrix4)
    (hBijective : Function.Bijective (canonicalSylvesterOperator root)) :
    E → Matrix4 :=
  fun point => canonicalC2LocalRootBranchAt root hBijective (target point)

/-- A continuous square-root lift agrees locally with the canonical `C²`
branch based at its current value. -/
theorem continuousRegularRootLift_eventuallyEq_canonicalC2LocalTargetLift
    {E : Type*} [TopologicalSpace E]
    (target rootLift : E → Matrix4) (point : E)
    (hBijective : Function.Bijective
      (canonicalSylvesterOperator (rootLift point)))
    (hRoot : ContinuousAt rootLift point)
    (hSquare : ∀ nearby,
      canonicalMatrixSquare (rootLift nearby) = target nearby) :
    rootLift =ᶠ[𝓝 point]
      canonicalC2LocalTargetLift target (rootLift point) hBijective := by
  have hLeft :=
    (canonicalC2LocalSquareChartAt (rootLift point) hBijective)
      |>.eventually_left_inverse
        (root_mem_canonicalC2LocalSquareChartAt_source
          (rootLift point) hBijective)
  have hAlong := hRoot.eventually hLeft
  filter_upwards [hAlong] with nearby hNearby
  change rootLift nearby =
    canonicalC2LocalRootBranchAt (rootLift point) hBijective
      (target nearby)
  rw [← hSquare nearby]
  exact hNearby.symm

/-- Continuity, the square identity, and Sylvester regularity upgrade a root
lift to `C²` whenever its target is `C²`. -/
theorem continuousRegularRootLift_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (target rootLift : E → Matrix4) (point : E)
    (hBijective : Function.Bijective
      (canonicalSylvesterOperator (rootLift point)))
    (hRoot : ContinuousAt rootLift point)
    (hSquare : ∀ nearby,
      canonicalMatrixSquare (rootLift nearby) = target nearby)
    (hTarget : ContDiffAt Real 2 target point) :
    ContDiffAt Real 2 rootLift point := by
  have hBase : target point = canonicalMatrixSquare (rootLift point) :=
    (hSquare point).symm
  have hBranch : ContDiffAt Real 2
      (canonicalC2LocalRootBranchAt (rootLift point) hBijective)
      (target point) := by
    simpa only [hBase] using
      canonicalC2LocalRootBranchAt_contDiffAt (rootLift point) hBijective
  have hLocal : ContDiffAt Real 2
      (canonicalC2LocalTargetLift target (rootLift point) hBijective) point :=
    hBranch.comp point hTarget
  exact hLocal.congr_of_eventuallyEq
    (continuousRegularRootLift_eventuallyEq_canonicalC2LocalTargetLift
      target rootLift point hBijective hRoot hSquare)

/-- Pointwise regularity gives the global `C²` continuation theorem. -/
theorem continuousRegularRootLift_contDiff_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (target rootLift : E → Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (rootLift point)))
    (hRoot : Continuous rootLift)
    (hSquare : ∀ point,
      canonicalMatrixSquare (rootLift point) = target point)
    (hTarget : ContDiff Real 2 target) :
    ContDiff Real 2 rootLift := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact continuousRegularRootLift_contDiffAt_two target rootLift point
    (hRegular point) hRoot.continuousAt hSquare hTarget.contDiffAt

/-- Open locus on which the Sylvester derivative is represented by a
continuous linear equivalence. -/
def sylvesterRegularRootSet : Set Matrix4 :=
  canonicalSylvesterOperator ⁻¹'
    Set.range ((↑) : (Matrix4 ≃L[Real] Matrix4) →
      Matrix4 →L[Real] Matrix4)

theorem sylvesterRegularRootSet_isOpen : IsOpen sylvesterRegularRootSet := by
  apply ContinuousLinearEquiv.isOpen.preimage
  change Continuous canonicalSylvesterOperator
  exact canonicalSylvesterFamily.continuous

theorem canonicalPositiveRawSylvester_bijective
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Function.Bijective
      (canonicalSylvesterOperator
        (positiveRawRegularRoot target hSpectrum)) := by
  have hExisting :=
    positiveRawRegularRoot_sylvester_bijective target hSpectrum
  constructor
  · intro first second hEqual
    apply hExisting.1
    simpa only [canonicalSylvesterOperator_apply,
      sylvesterOperator_apply] using hEqual
  · intro output
    obtain ⟨input, hInput⟩ := hExisting.2 output
    exact ⟨input, by
      simpa only [canonicalSylvesterOperator_apply,
        sylvesterOperator_apply] using hInput⟩

/-- Canonical-norm continuous equivalence supplied by the already proved
Sylvester bijectivity at every positive split raw target. -/
def positiveRawCanonicalSylvesterEquiv
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Matrix4 ≃L[Real] Matrix4 :=
  (LinearEquiv.ofBijective
    (canonicalSylvesterOperator
      (positiveRawRegularRoot target hSpectrum)).toLinearMap
    (canonicalPositiveRawSylvester_bijective target hSpectrum))
      |>.toContinuousLinearEquiv

theorem positiveRawCanonicalSylvesterEquiv_forward_eq
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    (positiveRawCanonicalSylvesterEquiv target hSpectrum :
      Matrix4 →L[Real] Matrix4) =
      canonicalSylvesterOperator
        (positiveRawRegularRoot target hSpectrum) := by
  apply ContinuousLinearMap.ext
  intro variation
  rfl

theorem positiveRawRegularRoot_mem_sylvesterRegularRootSet
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    positiveRawRegularRoot target hSpectrum ∈ sylvesterRegularRootSet := by
  exact ⟨positiveRawCanonicalSylvesterEquiv target hSpectrum,
    positiveRawCanonicalSylvesterEquiv_forward_eq target hSpectrum⟩

/-- `C²` inverse-function chart before restricting its source to regular
Sylvester roots. -/
def positiveRawC2BaseSquareChart
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    OpenPartialHomeomorph Matrix4 Matrix4 :=
  canonicalMatrixSquare_contDiff_two.contDiffAt.toOpenPartialHomeomorph
    canonicalMatrixSquare
    ((canonicalMatrixSquare_hasFDerivAt
      (positiveRawRegularRoot target hSpectrum)).congr_fderiv
        (positiveRawCanonicalSylvesterEquiv_forward_eq
          target hSpectrum).symm)
    (by norm_num)

/-- Restrict the existing IFT chart to roots whose Sylvester derivative stays
invertible. -/
def positiveRawContDiffLocalSquareChart
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    OpenPartialHomeomorph Matrix4 Matrix4 :=
  (positiveRawC2BaseSquareChart target hSpectrum).restrOpen
    sylvesterRegularRootSet sylvesterRegularRootSet_isOpen

/-- Open target of the smooth local root branch. -/
def positiveRawContDiffLocalRootTarget
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Set Matrix4 :=
  (positiveRawContDiffLocalSquareChart target hSpectrum).target

theorem positiveRawContDiffLocalRootTarget_isOpen
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsOpen (positiveRawContDiffLocalRootTarget target hSpectrum) :=
  (positiveRawContDiffLocalSquareChart target hSpectrum).open_target

theorem positiveRawRegularRoot_mem_contDiff_source
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    positiveRawRegularRoot target hSpectrum ∈
      (positiveRawContDiffLocalSquareChart target hSpectrum).source := by
  rw [positiveRawContDiffLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨canonicalMatrixSquare_contDiff_two.contDiffAt
      |>.mem_toOpenPartialHomeomorph_source
        ((canonicalMatrixSquare_hasFDerivAt
          (positiveRawRegularRoot target hSpectrum)).congr_fderiv
            (positiveRawCanonicalSylvesterEquiv_forward_eq
              target hSpectrum).symm)
        (by norm_num),
    positiveRawRegularRoot_mem_sylvesterRegularRootSet target hSpectrum⟩

theorem target_mem_positiveRawContDiffLocalRootTarget
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    target ∈ positiveRawContDiffLocalRootTarget target hSpectrum := by
  have hImage :=
    (positiveRawContDiffLocalSquareChart target hSpectrum).map_source
      (positiveRawRegularRoot_mem_contDiff_source target hSpectrum)
  change canonicalMatrixSquare
      (positiveRawRegularRoot target hSpectrum) ∈
    positiveRawContDiffLocalRootTarget target hSpectrum at hImage
  change positiveRawRegularRoot target hSpectrum *
      positiveRawRegularRoot target hSpectrum ∈
    positiveRawContDiffLocalRootTarget target hSpectrum at hImage
  rwa [positiveRawRegularRoot_square] at hImage

/-- The smooth local square-root branch. -/
def positiveRawContDiffLocalRootBranch
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Matrix4 → Matrix4 :=
  (positiveRawContDiffLocalSquareChart target hSpectrum).symm

theorem positiveRawContDiffLocalRootBranch_square
    {target nearby : Matrix4}
    {hSpectrum : PositiveRealSplitCharpoly4 target}
    (hNearby : nearby ∈
      positiveRawContDiffLocalRootTarget target hSpectrum) :
    canonicalMatrixSquare
        (positiveRawContDiffLocalRootBranch target hSpectrum nearby) =
      nearby := by
  exact (positiveRawContDiffLocalSquareChart target hSpectrum).right_inv hNearby

theorem positiveRawContDiffLocalRootBranch_at_center
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    positiveRawContDiffLocalRootBranch target hSpectrum target =
      positiveRawRegularRoot target hSpectrum := by
  have hLeft :=
    (positiveRawContDiffLocalSquareChart target hSpectrum).left_inv
      (positiveRawRegularRoot_mem_contDiff_source target hSpectrum)
  change positiveRawContDiffLocalRootBranch target hSpectrum
      (canonicalMatrixSquare
        (positiveRawRegularRoot target hSpectrum)) =
    positiveRawRegularRoot target hSpectrum at hLeft
  change positiveRawContDiffLocalRootBranch target hSpectrum
      (positiveRawRegularRoot target hSpectrum *
        positiveRawRegularRoot target hSpectrum) =
    positiveRawRegularRoot target hSpectrum at hLeft
  rwa [positiveRawRegularRoot_square] at hLeft

/-- The inverse branch is smooth at every point of its open target. -/
theorem positiveRawContDiffLocalRootBranch_contDiffAt
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target)
    (nearby : Matrix4)
    (hNearby : nearby ∈
      positiveRawContDiffLocalRootTarget target hSpectrum) :
    ContDiffAt Real 2
      (positiveRawContDiffLocalRootBranch target hSpectrum) nearby := by
  have hSource :=
    (positiveRawContDiffLocalSquareChart target hSpectrum).map_target hNearby
  rw [positiveRawContDiffLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  apply (positiveRawContDiffLocalSquareChart target hSpectrum).contDiffAt_symm
    hNearby (f₀' := equiv)
  · have hDerivative :=
      (canonicalMatrixSquare_hasFDerivAt
        ((positiveRawContDiffLocalSquareChart target hSpectrum).symm nearby))
        
    exact hDerivative.congr_fderiv hEquiv.symm
  · exact canonicalMatrixSquare_contDiff_two.contDiffAt

theorem positiveRawContDiffLocalRootBranch_contDiffOn
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    ContDiffOn Real 2
      (positiveRawContDiffLocalRootBranch target hSpectrum)
      (positiveRawContDiffLocalRootTarget target hSpectrum) := by
  intro nearby hNearby
  exact (positiveRawContDiffLocalRootBranch_contDiffAt
    target hSpectrum nearby hNearby).contDiffWithinAt

/-- Translate the raw target to an open perturbation domain centered at
zero. -/
def positiveRawRootPerturbationDomain
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Set Matrix4 :=
  (fun variation : Matrix4 => target + variation) ⁻¹'
    positiveRawContDiffLocalRootTarget target hSpectrum

theorem positiveRawRootPerturbationDomain_isOpen
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsOpen (positiveRawRootPerturbationDomain target hSpectrum) := by
  exact (positiveRawContDiffLocalRootTarget_isOpen target hSpectrum).preimage
    (continuous_const.add continuous_id)

theorem zero_mem_positiveRawRootPerturbationDomain
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    (0 : Matrix4) ∈ positiveRawRootPerturbationDomain target hSpectrum := by
  simpa [positiveRawRootPerturbationDomain] using
    target_mem_positiveRawContDiffLocalRootTarget target hSpectrum

/-- Root selection in perturbation coordinates. -/
def positiveRawRootPerturbationBranch
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Matrix4 → Matrix4 :=
  fun variation =>
    positiveRawContDiffLocalRootBranch target hSpectrum (target + variation)

theorem positiveRawRootPerturbationBranch_square
    {target variation : Matrix4}
    {hSpectrum : PositiveRealSplitCharpoly4 target}
    (hVariation : variation ∈
      positiveRawRootPerturbationDomain target hSpectrum) :
    canonicalMatrixSquare
        (positiveRawRootPerturbationBranch target hSpectrum variation) =
      target + variation :=
  positiveRawContDiffLocalRootBranch_square hVariation

theorem positiveRawRootPerturbationBranch_contDiffOn
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    ContDiffOn Real 2
      (positiveRawRootPerturbationBranch target hSpectrum)
      (positiveRawRootPerturbationDomain target hSpectrum) := by
  intro variation hVariation
  have hOuter := positiveRawContDiffLocalRootBranch_contDiffAt
    target hSpectrum (target + variation) hVariation
  have hInner : ContDiffAt Real 2
      (fun current : Matrix4 => target + current) variation :=
    contDiffAt_const.add contDiffAt_id
  rw [show positiveRawRootPerturbationBranch target hSpectrum =
      positiveRawContDiffLocalRootBranch target hSpectrum ∘
        (fun current : Matrix4 => target + current) by rfl]
  exact (hOuter.comp variation hInner).contDiffWithinAt

/-- Complete general local-root certificate in the `0 ∈ U` coordinates used
by the local Candidate-A variational interface. -/
theorem positive_raw_contDiff_local_root_gate
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsOpen (positiveRawRootPerturbationDomain target hSpectrum) ∧
      (0 : Matrix4) ∈ positiveRawRootPerturbationDomain target hSpectrum ∧
      ContDiffOn Real 2
        (positiveRawRootPerturbationBranch target hSpectrum)
        (positiveRawRootPerturbationDomain target hSpectrum) ∧
      ∀ variation,
        variation ∈ positiveRawRootPerturbationDomain target hSpectrum →
        canonicalMatrixSquare
            (positiveRawRootPerturbationBranch target hSpectrum variation) =
          target + variation := by
  exact ⟨positiveRawRootPerturbationDomain_isOpen target hSpectrum,
    zero_mem_positiveRawRootPerturbationDomain target hSpectrum,
    positiveRawRootPerturbationBranch_contDiffOn target hSpectrum,
    fun _ hVariation =>
      positiveRawRootPerturbationBranch_square hVariation⟩

end

end P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
end JanusFormal
