import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Compact
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

/-!
# C² local root branches for continuous matrix fields

On a compact base, continuous `4 × 4` matrix fields form a Banach algebra in
the uniform norm. Pointwise Sylvester bijectivity gives a genuine bounded
Sylvester equivalence on that field space: continuity of the inverse family is
obtained from continuity of inversion in the Banach algebra of endomorphisms.
The inverse-function theorem then supplies an open, zero-centered `C²` root
chart for whole fields.

This closes the continuous-field root layer. It does not claim the stronger
Sobolev regularity needed by the Einstein--Hilbert action.
-/

namespace JanusFormal
namespace P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius RightActions Topology
open Set
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

local instance canonicalMatrixAddCommGroup : AddCommGroup Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toAddCommGroup

local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace

local instance canonicalMatrixTopologicalSpace : TopologicalSpace Matrix4 :=
  canonicalMatrixUniformSpace.toTopologicalSpace

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

abbrev MatrixField (X : Type*) [TopologicalSpace X] := C(X, Matrix4)

/-- The pointwise Sylvester equivalence represented as a unit of the Banach
algebra of continuous linear endomorphisms. -/
def pointwiseSylvesterUnit
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (point : X) : (Matrix4 →L[Real] Matrix4)ˣ :=
  (canonicalSylvesterEquivOfBijective
    (root point) (hRegular point)).toUnit

theorem pointwiseSylvesterUnit_coe
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (point : X) :
    (pointwiseSylvesterUnit root hRegular point :
      Matrix4 →L[Real] Matrix4) =
      canonicalSylvesterOperator (root point) :=
  canonicalSylvesterEquivOfBijective_forward_eq
    (root point) (hRegular point)

/-- The chosen pointwise units vary continuously because their forward maps
are the canonical continuous Sylvester family. -/
theorem pointwiseSylvesterUnit_continuous
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Continuous (pointwiseSylvesterUnit root hRegular) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  change Continuous (fun point =>
    (pointwiseSylvesterUnit root hRegular point :
      Matrix4 →L[Real] Matrix4))
  simp_rw [pointwiseSylvesterUnit_coe]
  exact canonicalSylvesterFamily.continuous.comp root.continuous

/-- Continuous field of inverse Sylvester operators. -/
def pointwiseInverseSylvesterField
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    C(X, Matrix4 →L[Real] Matrix4) where
  toFun point :=
    ((↑((pointwiseSylvesterUnit root hRegular point)⁻¹)) :
      Matrix4 →L[Real] Matrix4)
  continuous_toFun :=
    Units.continuous_coe_inv.comp
      (pointwiseSylvesterUnit_continuous root hRegular)

/-- Apply the inverse Sylvester family pointwise to a continuous field. -/
def continuousMatrixFieldInverseSylvesterApply
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : MatrixField X) : MatrixField X where
  toFun point := pointwiseInverseSylvesterField root hRegular point
    (variation point)
  continuous_toFun :=
    (pointwiseInverseSylvesterField root hRegular).continuous.clm_apply
      variation.continuous

theorem pointwiseInverseSylvesterField_left
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (point : X) (variation : Matrix4) :
    pointwiseInverseSylvesterField root hRegular point
      (canonicalSylvesterOperator (root point) variation) =
      variation := by
  unfold pointwiseInverseSylvesterField pointwiseSylvesterUnit
  change (canonicalSylvesterEquivOfBijective
      (root point) (hRegular point)).symm
      (canonicalSylvesterOperator (root point) variation) = variation
  rw [← canonicalSylvesterEquivOfBijective_forward_eq
    (root point) (hRegular point)]
  exact (canonicalSylvesterEquivOfBijective
    (root point) (hRegular point)).symm_apply_apply variation

theorem pointwiseInverseSylvesterField_right
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (point : X) (variation : Matrix4) :
    canonicalSylvesterOperator (root point)
        (pointwiseInverseSylvesterField root hRegular point variation) =
      variation := by
  unfold pointwiseInverseSylvesterField pointwiseSylvesterUnit
  change canonicalSylvesterOperator (root point)
      ((canonicalSylvesterEquivOfBijective
        (root point) (hRegular point)).symm variation) = variation
  rw [← canonicalSylvesterEquivOfBijective_forward_eq
    (root point) (hRegular point)]
  exact (canonicalSylvesterEquivOfBijective
    (root point) (hRegular point)).apply_symm_apply variation

/-- Linear pointwise inverse before installing its uniform norm bound. -/
def continuousMatrixFieldInverseSylvesterLinearMap
    {X : Type*} [TopologicalSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    MatrixField X →ₗ[Real] MatrixField X where
  toFun := continuousMatrixFieldInverseSylvesterApply root hRegular
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    exact (pointwiseInverseSylvesterField root hRegular point).map_add
      (first point) (second point)
  map_smul' scalar variation := by
    apply ContinuousMap.ext
    intro point
    exact (pointwiseInverseSylvesterField root hRegular point).map_smul
      scalar (variation point)

theorem continuousMatrixFieldInverseSylvesterApply_norm_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : MatrixField X) :
    ‖continuousMatrixFieldInverseSylvesterApply root hRegular variation‖ ≤
      ‖pointwiseInverseSylvesterField root hRegular‖ * ‖variation‖ := by
  apply (ContinuousMap.norm_le
    (continuousMatrixFieldInverseSylvesterApply root hRegular variation)
    (mul_nonneg
      (norm_nonneg (pointwiseInverseSylvesterField root hRegular))
      (norm_nonneg variation))).2
  intro point
  calc
    ‖pointwiseInverseSylvesterField root hRegular point
        (variation point)‖ ≤
        ‖pointwiseInverseSylvesterField root hRegular point‖ *
          ‖variation point‖ :=
      (pointwiseInverseSylvesterField root hRegular point).le_opNorm
        (variation point)
    _ ≤ ‖pointwiseInverseSylvesterField root hRegular‖ * ‖variation‖ :=
      mul_le_mul
        ((pointwiseInverseSylvesterField root hRegular).norm_coe_le_norm point)
        (variation.norm_coe_le_norm point)
        (norm_nonneg (variation point))
        (norm_nonneg (pointwiseInverseSylvesterField root hRegular))

/-- Bounded inverse Sylvester operator on the uniform field space. -/
def continuousMatrixFieldInverseSylvesterOperator
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    MatrixField X →L[Real] MatrixField X :=
  (continuousMatrixFieldInverseSylvesterLinearMap root hRegular).mkContinuous
    ‖pointwiseInverseSylvesterField root hRegular‖
    (continuousMatrixFieldInverseSylvesterApply_norm_le
      root hRegular)

@[simp]
theorem continuousMatrixFieldInverseSylvesterOperator_apply_at
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : MatrixField X) (point : X) :
    continuousMatrixFieldInverseSylvesterOperator root hRegular variation point =
      pointwiseInverseSylvesterField root hRegular point (variation point) :=
  rfl

/-- Sylvester family on the Banach algebra of continuous matrix fields. -/
def continuousMatrixFieldSylvesterFamily
    {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    MatrixField X →L[Real] MatrixField X →L[Real] MatrixField X :=
  ContinuousLinearMap.mul Real (MatrixField X) +
    (ContinuousLinearMap.mul Real (MatrixField X)).flip

def continuousMatrixFieldSylvesterOperator
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X) : MatrixField X →L[Real] MatrixField X :=
  continuousMatrixFieldSylvesterFamily root

@[simp]
theorem continuousMatrixFieldSylvesterOperator_apply_at
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root variation : MatrixField X) (point : X) :
    continuousMatrixFieldSylvesterOperator root variation point =
      root point * variation point + variation point * root point :=
  rfl

/-- Pointwise Sylvester regularity is sufficient for a genuine continuous
linear equivalence on the full uniform field space. -/
def continuousMatrixFieldSylvesterEquiv
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    MatrixField X ≃L[Real] MatrixField X where
  toFun := continuousMatrixFieldSylvesterOperator root
  invFun := continuousMatrixFieldInverseSylvesterOperator root hRegular
  left_inv variation := by
    apply ContinuousMap.ext
    intro point
    rw [continuousMatrixFieldInverseSylvesterOperator_apply_at,
      continuousMatrixFieldSylvesterOperator_apply_at]
    exact pointwiseInverseSylvesterField_left root hRegular point
      (variation point)
  right_inv variation := by
    apply ContinuousMap.ext
    intro point
    rw [continuousMatrixFieldSylvesterOperator_apply_at,
      continuousMatrixFieldInverseSylvesterOperator_apply_at]
    exact pointwiseInverseSylvesterField_right root hRegular point
      (variation point)
  map_add' first second := by simp
  map_smul' scalar variation := by simp
  continuous_toFun :=
    (continuousMatrixFieldSylvesterOperator root).continuous
  continuous_invFun :=
    (continuousMatrixFieldInverseSylvesterOperator root hRegular).continuous

theorem continuousMatrixFieldSylvesterEquiv_forward_eq
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    (continuousMatrixFieldSylvesterEquiv root hRegular :
      MatrixField X →L[Real] MatrixField X) =
      continuousMatrixFieldSylvesterOperator root :=
  rfl

/-- Pointwise squaring on the Banach algebra of continuous matrix fields. -/
def continuousMatrixFieldSquare
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X) : MatrixField X :=
  root * root

@[simp]
theorem continuousMatrixFieldSquare_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X) (point : X) :
    continuousMatrixFieldSquare root point = root point * root point :=
  rfl

theorem continuousMatrixFieldSquare_hasFDerivAt
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X) :
    HasFDerivAt continuousMatrixFieldSquare
      (continuousMatrixFieldSylvesterOperator root) root := by
  have hIdentity : HasFDerivAt (fun field : MatrixField X => field)
      (ContinuousLinearMap.id Real (MatrixField X)) root :=
    hasFDerivAt_id root
  exact (hIdentity.mul' hIdentity).congr_fderiv rfl

theorem continuousMatrixFieldSquare_contDiff_two
    {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    ContDiff Real 2
      (continuousMatrixFieldSquare : MatrixField X → MatrixField X) := by
  change @ContDiff Real _ (MatrixField X)
    NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace (MatrixField X))
    (MatrixField X) NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace (MatrixField X)) 2
    (fun field : MatrixField X => field * field)
  simpa using (contDiff_id.mul contDiff_id :
    ContDiff Real 2 (fun field : MatrixField X => field * field))

/-- Open field-space locus on which the Sylvester derivative is represented by
a continuous linear equivalence. -/
def continuousMatrixFieldSylvesterRegularRootSet
    {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    Set (MatrixField X) :=
  continuousMatrixFieldSylvesterOperator ⁻¹'
    Set.range ((↑) :
      (MatrixField X ≃L[Real] MatrixField X) →
        MatrixField X →L[Real] MatrixField X)

theorem continuousMatrixFieldSylvesterRegularRootSet_isOpen
    {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    IsOpen (continuousMatrixFieldSylvesterRegularRootSet (X := X)) := by
  apply ContinuousLinearEquiv.isOpen.preimage
  change Continuous
    (continuousMatrixFieldSylvesterOperator :
      MatrixField X → MatrixField X →L[Real] MatrixField X)
  exact continuousMatrixFieldSylvesterFamily.continuous

theorem continuousMatrixField_mem_sylvesterRegularRootSet
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    root ∈ continuousMatrixFieldSylvesterRegularRootSet := by
  exact ⟨continuousMatrixFieldSylvesterEquiv root hRegular,
    continuousMatrixFieldSylvesterEquiv_forward_eq root hRegular⟩

/-- `C²` inverse-function chart at a pointwise Sylvester-regular continuous
root field. -/
def continuousMatrixFieldC2BaseSquareChart
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    OpenPartialHomeomorph (MatrixField X) (MatrixField X) :=
  continuousMatrixFieldSquare_contDiff_two.contDiffAt.toOpenPartialHomeomorph
    continuousMatrixFieldSquare
    ((continuousMatrixFieldSquare_hasFDerivAt root).congr_fderiv
      (continuousMatrixFieldSylvesterEquiv_forward_eq
        root hRegular).symm)
    (by norm_num)

/-- Restrict the IFT chart to fields whose full Sylvester derivative remains
invertible. -/
def continuousMatrixFieldContDiffLocalSquareChart
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    OpenPartialHomeomorph (MatrixField X) (MatrixField X) :=
  (continuousMatrixFieldC2BaseSquareChart root hRegular).restrOpen
    continuousMatrixFieldSylvesterRegularRootSet
      continuousMatrixFieldSylvesterRegularRootSet_isOpen

def continuousMatrixFieldContDiffLocalRootTarget
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Set (MatrixField X) :=
  (continuousMatrixFieldContDiffLocalSquareChart root hRegular).target

theorem continuousMatrixFieldContDiffLocalRootTarget_isOpen
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (continuousMatrixFieldContDiffLocalRootTarget root hRegular) :=
  (continuousMatrixFieldContDiffLocalSquareChart root hRegular).open_target

theorem continuousMatrixField_mem_contDiff_source
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    root ∈ (continuousMatrixFieldContDiffLocalSquareChart
      root hRegular).source := by
  rw [continuousMatrixFieldContDiffLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨continuousMatrixFieldSquare_contDiff_two.contDiffAt
      |>.mem_toOpenPartialHomeomorph_source
        ((continuousMatrixFieldSquare_hasFDerivAt root).congr_fderiv
          (continuousMatrixFieldSylvesterEquiv_forward_eq
            root hRegular).symm)
        (by norm_num),
    continuousMatrixField_mem_sylvesterRegularRootSet root hRegular⟩

theorem continuousMatrixFieldSquare_mem_contDiff_target
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    continuousMatrixFieldSquare root ∈
      continuousMatrixFieldContDiffLocalRootTarget root hRegular := by
  have hImage :=
    (continuousMatrixFieldContDiffLocalSquareChart root hRegular).map_source
      (continuousMatrixField_mem_contDiff_source root hRegular)
  change continuousMatrixFieldSquare root ∈
    continuousMatrixFieldContDiffLocalRootTarget root hRegular at hImage
  exact hImage

/-- Local `C²` root branch for whole continuous matrix fields. -/
def continuousMatrixFieldContDiffLocalRootBranch
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    MatrixField X → MatrixField X :=
  (continuousMatrixFieldContDiffLocalSquareChart root hRegular).symm

theorem continuousMatrixFieldContDiffLocalRootBranch_square
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {root nearby : MatrixField X}
    {hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))}
    (hNearby : nearby ∈
      continuousMatrixFieldContDiffLocalRootTarget root hRegular) :
    continuousMatrixFieldSquare
        (continuousMatrixFieldContDiffLocalRootBranch
          root hRegular nearby) = nearby := by
  have hRight :=
    (continuousMatrixFieldContDiffLocalSquareChart root hRegular).right_inv
      hNearby
  change continuousMatrixFieldSquare
      (continuousMatrixFieldContDiffLocalRootBranch
        root hRegular nearby) = nearby at hRight
  exact hRight

theorem continuousMatrixFieldContDiffLocalRootBranch_at_center
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    continuousMatrixFieldContDiffLocalRootBranch root hRegular
        (continuousMatrixFieldSquare root) = root := by
  have hLeft :=
    (continuousMatrixFieldContDiffLocalSquareChart root hRegular).left_inv
      (continuousMatrixField_mem_contDiff_source root hRegular)
  change continuousMatrixFieldContDiffLocalRootBranch root hRegular
      (continuousMatrixFieldSquare root) = root at hLeft
  exact hLeft

theorem continuousMatrixFieldContDiffLocalRootBranch_contDiffAt
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : MatrixField X)
    (hNearby : nearby ∈
      continuousMatrixFieldContDiffLocalRootTarget root hRegular) :
    ContDiffAt Real 2
      (continuousMatrixFieldContDiffLocalRootBranch root hRegular) nearby := by
  have hSource :=
    (continuousMatrixFieldContDiffLocalSquareChart root hRegular).map_target
      hNearby
  rw [continuousMatrixFieldContDiffLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  apply (continuousMatrixFieldContDiffLocalSquareChart
    root hRegular).contDiffAt_symm hNearby (f₀' := equiv)
  · exact (continuousMatrixFieldSquare_hasFDerivAt
      ((continuousMatrixFieldContDiffLocalSquareChart
        root hRegular).symm nearby)).congr_fderiv hEquiv.symm
  · exact continuousMatrixFieldSquare_contDiff_two.contDiffAt

theorem continuousMatrixFieldContDiffLocalRootBranch_contDiffOn
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContDiffOn Real 2
      (continuousMatrixFieldContDiffLocalRootBranch root hRegular)
      (continuousMatrixFieldContDiffLocalRootTarget root hRegular) := by
  intro nearby hNearby
  exact (continuousMatrixFieldContDiffLocalRootBranch_contDiffAt
    root hRegular nearby hNearby).contDiffWithinAt

/-- Translate the field target to a perturbation domain centered at zero. -/
def continuousMatrixFieldRootPerturbationDomain
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Set (MatrixField X) :=
  (fun variation => continuousMatrixFieldSquare root + variation) ⁻¹'
    continuousMatrixFieldContDiffLocalRootTarget root hRegular

theorem continuousMatrixFieldRootPerturbationDomain_isOpen
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (continuousMatrixFieldRootPerturbationDomain root hRegular) := by
  exact (continuousMatrixFieldContDiffLocalRootTarget_isOpen root hRegular)
    |>.preimage (continuous_const.add continuous_id)

theorem zero_mem_continuousMatrixFieldRootPerturbationDomain
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    (0 : MatrixField X) ∈
      continuousMatrixFieldRootPerturbationDomain root hRegular := by
  simpa [continuousMatrixFieldRootPerturbationDomain] using
    continuousMatrixFieldSquare_mem_contDiff_target root hRegular

def continuousMatrixFieldRootPerturbationBranch
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    MatrixField X → MatrixField X :=
  fun variation => continuousMatrixFieldContDiffLocalRootBranch
    root hRegular (continuousMatrixFieldSquare root + variation)

theorem continuousMatrixFieldRootPerturbationBranch_square
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {root variation : MatrixField X}
    {hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))}
    (hVariation : variation ∈
      continuousMatrixFieldRootPerturbationDomain root hRegular) :
    continuousMatrixFieldSquare
        (continuousMatrixFieldRootPerturbationBranch
          root hRegular variation) =
      continuousMatrixFieldSquare root + variation :=
  continuousMatrixFieldContDiffLocalRootBranch_square hVariation

theorem continuousMatrixFieldRootPerturbationBranch_contDiffOn
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContDiffOn Real 2
      (continuousMatrixFieldRootPerturbationBranch root hRegular)
      (continuousMatrixFieldRootPerturbationDomain root hRegular) := by
  intro variation hVariation
  have hOuter := continuousMatrixFieldContDiffLocalRootBranch_contDiffAt
    root hRegular (continuousMatrixFieldSquare root + variation) hVariation
  have hInner : ContDiffAt Real 2
      (fun current : MatrixField X =>
        continuousMatrixFieldSquare root + current) variation :=
    contDiffAt_const.add contDiffAt_id
  rw [show continuousMatrixFieldRootPerturbationBranch root hRegular =
      continuousMatrixFieldContDiffLocalRootBranch root hRegular ∘
        (fun current : MatrixField X =>
          continuousMatrixFieldSquare root + current) by rfl]
  exact (hOuter.comp variation hInner).contDiffWithinAt

/-- Complete `0 ∈ U` continuous-field root certificate. -/
theorem continuous_matrix_field_contDiff_local_root_gate
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (root : MatrixField X)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (continuousMatrixFieldRootPerturbationDomain root hRegular) ∧
      (0 : MatrixField X) ∈
        continuousMatrixFieldRootPerturbationDomain root hRegular ∧
      ContDiffOn Real 2
        (continuousMatrixFieldRootPerturbationBranch root hRegular)
        (continuousMatrixFieldRootPerturbationDomain root hRegular) ∧
      ∀ variation,
        variation ∈
            continuousMatrixFieldRootPerturbationDomain root hRegular →
          continuousMatrixFieldSquare
              (continuousMatrixFieldRootPerturbationBranch
                root hRegular variation) =
            continuousMatrixFieldSquare root + variation := by
  exact ⟨continuousMatrixFieldRootPerturbationDomain_isOpen root hRegular,
    zero_mem_continuousMatrixFieldRootPerturbationDomain root hRegular,
    continuousMatrixFieldRootPerturbationBranch_contDiffOn root hRegular,
    fun _ hVariation =>
      continuousMatrixFieldRootPerturbationBranch_square hVariation⟩

end

end P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D
end JanusFormal
