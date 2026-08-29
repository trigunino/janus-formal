import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D

/-!
# Local matrix-root chart on the uniform C² core

The existing smooth inverse-Sylvester coefficients are lifted through the C²
scalar product.  Density identifies the resulting bounded inverse with the
exact derivative of matrix squaring on the uniform C²-jet core.  The Banach
inverse-function theorem then supplies a genuine local C² root branch on an
open neighborhood in the full ambient tangent space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius RightActions Topology
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev SmoothMatrix :=
  P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D.SmoothFiniteMatrix
    period hPeriod 4

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

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Exact coordinatewise lift of a smooth matrix root into the C² core. -/
def smoothMatrixFieldToC2
    (root : SmoothQuotientField period hPeriod Matrix4) :
    C2Matrix period hPeriod :=
  smoothFiniteMatrixToC2 period hPeriod 4
    (smoothMatrixFieldCoefficients period hPeriod root)

theorem c2FiniteMatrixSylvester_smooth
    (root : SmoothQuotientField period hPeriod Matrix4)
    (variation : SmoothMatrix period hPeriod) :
    c2FiniteMatrixSylvester period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod root)
        (smoothFiniteMatrixToC2 period hPeriod 4 variation) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) variation) := by
  change c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (smoothFiniteMatrixToC2 period hPeriod 4
          (smoothMatrixFieldCoefficients period hPeriod root))
        (smoothFiniteMatrixToC2 period hPeriod 4 variation) +
      c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (smoothFiniteMatrixToC2 period hPeriod 4 variation)
        (smoothFiniteMatrixToC2 period hPeriod 4
          (smoothMatrixFieldCoefficients period hPeriod root)) = _
  rw [c2FiniteMatrixProduct_smooth, c2FiniteMatrixProduct_smooth]
  rw [← (smoothFiniteMatrixToC2 period hPeriod 4).map_add]
  rfl

/-- Existing smooth inverse-Sylvester coefficient lifted to the C² core. -/
def inverseSylvesterCoefficientC2
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (outputRow outputColumn inputRow inputColumn : Fin 4) :
    C2Scalar period hPeriod :=
  smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (inverseSylvesterCoefficient period hPeriod root hRegular
      outputRow outputColumn inputRow inputColumn)

def c2InverseSylvesterCoordinate
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (outputRow outputColumn : Fin 4) :
    C2Matrix period hPeriod →L[Real] C2Scalar period hPeriod :=
  ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (inverseSylvesterCoefficientC2 period hPeriod root hRegular
        outputRow outputColumn inputRow inputColumn)).comp
      ((ContinuousLinearMap.proj inputColumn :
          (Fin 4 → C2Scalar period hPeriod) →L[Real]
            C2Scalar period hPeriod).comp
        (ContinuousLinearMap.proj inputRow :
          C2Matrix period hPeriod →L[Real]
            (Fin 4 → C2Scalar period hPeriod)))

/-- Bounded inverse candidate assembled from the smooth coefficients. -/
def c2InverseSylvesterOperator
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  ContinuousLinearMap.pi fun outputRow : Fin 4 =>
    ContinuousLinearMap.pi fun outputColumn : Fin 4 =>
      c2InverseSylvesterCoordinate
        period hPeriod root hRegular outputRow outputColumn

@[simp]
theorem c2InverseSylvesterOperator_apply
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : C2Matrix period hPeriod)
    (outputRow outputColumn : Fin 4) :
    c2InverseSylvesterOperator period hPeriod root hRegular variation
        outputRow outputColumn =
      ∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (inverseSylvesterCoefficientC2 period hPeriod root hRegular
            outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn) := by
  simp [c2InverseSylvesterOperator, c2InverseSylvesterCoordinate]

theorem c2InverseSylvesterOperator_smooth
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : SmoothMatrix period hPeriod) :
    c2InverseSylvesterOperator period hPeriod root hRegular
        (smoothFiniteMatrixToC2 period hPeriod 4 variation) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothInverseSylvesterApply
          period hPeriod root hRegular variation) := by
  funext outputRow outputColumn
  rw [c2InverseSylvesterOperator_apply]
  change (∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (inverseSylvesterCoefficient period hPeriod root hRegular
            outputRow outputColumn inputRow inputColumn))
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (variation inputRow inputColumn))) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (∑ inputRow : Fin 4, ∑ inputColumn : Fin 4,
        smoothScalarFieldMul period hPeriod
          (inverseSylvesterCoefficient period hPeriod root hRegular
            outputRow outputColumn inputRow inputColumn)
          (variation inputRow inputColumn))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputRow _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputColumn _
  exact canonicalPhysicalScalarC2JetCoreProduct_smooth
    period hPeriod
      (inverseSylvesterCoefficient period hPeriod root hRegular
        outputRow outputColumn inputRow inputColumn)
      (variation inputRow inputColumn)

theorem c2InverseSylvesterOperator_left
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : C2Matrix period hPeriod) :
    c2InverseSylvesterOperator period hPeriod root hRegular
        (c2FiniteMatrixSylvester period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root) variation) =
      variation := by
  let inverse := c2InverseSylvesterOperator
    period hPeriod root hRegular
  let sylvester := c2FiniteMatrixSylvester period hPeriod 4
    (smoothMatrixFieldToC2 period hPeriod root)
  refine DenseRange.induction_on
    (smoothFiniteMatrixToC2_denseRange period hPeriod 4) variation
    (isClosed_eq (inverse.comp sylvester).continuous
      (ContinuousLinearMap.id Real (C2Matrix period hPeriod)).continuous) ?_
  intro smooth
  change inverse (sylvester
      (smoothFiniteMatrixToC2 period hPeriod 4 smooth)) =
    smoothFiniteMatrixToC2 period hPeriod 4 smooth
  rw [show sylvester (smoothFiniteMatrixToC2 period hPeriod 4 smooth) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root) smooth) from
    c2FiniteMatrixSylvester_smooth period hPeriod root smooth]
  rw [show inverse (smoothFiniteMatrixToC2 period hPeriod 4
      (smoothMatrixSylvester period hPeriod
        (smoothMatrixFieldCoefficients period hPeriod root) smooth)) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothInverseSylvesterApply period hPeriod root hRegular
          (smoothMatrixSylvester period hPeriod
            (smoothMatrixFieldCoefficients period hPeriod root) smooth)) from
    c2InverseSylvesterOperator_smooth period hPeriod root hRegular _]
  rw [smoothInverseSylvesterApply_left]

theorem c2InverseSylvesterOperator_right
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : C2Matrix period hPeriod) :
    c2FiniteMatrixSylvester period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod root)
        (c2InverseSylvesterOperator period hPeriod root hRegular variation) =
      variation := by
  let inverse := c2InverseSylvesterOperator
    period hPeriod root hRegular
  let sylvester := c2FiniteMatrixSylvester period hPeriod 4
    (smoothMatrixFieldToC2 period hPeriod root)
  refine DenseRange.induction_on
    (smoothFiniteMatrixToC2_denseRange period hPeriod 4) variation
    (isClosed_eq (sylvester.comp inverse).continuous
      (ContinuousLinearMap.id Real (C2Matrix period hPeriod)).continuous) ?_
  intro smooth
  change sylvester (inverse
      (smoothFiniteMatrixToC2 period hPeriod 4 smooth)) =
    smoothFiniteMatrixToC2 period hPeriod 4 smooth
  rw [show inverse (smoothFiniteMatrixToC2 period hPeriod 4 smooth) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothInverseSylvesterApply
          period hPeriod root hRegular smooth) from
    c2InverseSylvesterOperator_smooth
      period hPeriod root hRegular smooth]
  rw [show sylvester (smoothFiniteMatrixToC2 period hPeriod 4
      (smoothInverseSylvesterApply period hPeriod root hRegular smooth)) =
      smoothFiniteMatrixToC2 period hPeriod 4
        (smoothMatrixSylvester period hPeriod
          (smoothMatrixFieldCoefficients period hPeriod root)
          (smoothInverseSylvesterApply
            period hPeriod root hRegular smooth)) from
    c2FiniteMatrixSylvester_smooth period hPeriod root _]
  rw [smoothInverseSylvesterApply_right]

/-- Bounded Sylvester equivalence on the uniform C² matrix core. -/
def c2MatrixSylvesterEquiv
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    C2Matrix period hPeriod ≃L[Real] C2Matrix period hPeriod where
  toFun := c2FiniteMatrixSylvester period hPeriod 4
    (smoothMatrixFieldToC2 period hPeriod root)
  invFun := c2InverseSylvesterOperator period hPeriod root hRegular
  left_inv := c2InverseSylvesterOperator_left
    period hPeriod root hRegular
  right_inv := c2InverseSylvesterOperator_right
    period hPeriod root hRegular
  map_add' first second := by simp
  map_smul' scalar variation := by simp
  continuous_toFun := (c2FiniteMatrixSylvester period hPeriod 4
    (smoothMatrixFieldToC2 period hPeriod root)).continuous
  continuous_invFun :=
    (c2InverseSylvesterOperator period hPeriod root hRegular).continuous

theorem c2MatrixSylvesterEquiv_forward_eq
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    (c2MatrixSylvesterEquiv period hPeriod root hRegular :
      C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod) =
      c2FiniteMatrixSylvester period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod root) :=
  rfl

/-- Sylvester derivative as a continuous family over the C² matrix core. -/
def c2MatrixSylvesterFamily :
    C2Matrix period hPeriod →L[Real]
      C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  exact product + product.flip

@[simp]
theorem c2MatrixSylvesterFamily_apply
    (root : C2Matrix period hPeriod) :
    c2MatrixSylvesterFamily period hPeriod root =
      c2FiniteMatrixSylvester period hPeriod 4 root :=
  rfl

theorem c2MatrixSquare_contDiff_two :
    ContDiff Real 2 (c2FiniteMatrixSquare period hPeriod 4) :=
  (c2FiniteMatrixSquare_contDiff period hPeriod 4).of_le
    (show (2 : ℕ∞ω) ≤ ∞ by
      exact WithTop.coe_le_coe.mpr le_top)

/-- Open locus on which the C² Sylvester derivative is a bounded equivalence. -/
def c2MatrixSylvesterRegularRootSet :
    Set (C2Matrix period hPeriod) :=
  c2MatrixSylvesterFamily period hPeriod ⁻¹'
    Set.range ((↑) :
      (C2Matrix period hPeriod ≃L[Real] C2Matrix period hPeriod) →
      C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod)

theorem c2MatrixSylvesterRegularRootSet_isOpen :
    IsOpen (c2MatrixSylvesterRegularRootSet period hPeriod) := by
  apply ContinuousLinearEquiv.isOpen.preimage
  exact (c2MatrixSylvesterFamily period hPeriod).continuous

theorem smoothMatrixFieldToC2_mem_sylvesterRegularRootSet
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    smoothMatrixFieldToC2 period hPeriod root ∈
      c2MatrixSylvesterRegularRootSet period hPeriod := by
  exact ⟨c2MatrixSylvesterEquiv period hPeriod root hRegular,
    c2MatrixSylvesterEquiv_forward_eq period hPeriod root hRegular⟩

/-- Base inverse-function chart for squaring on the complete C² core. -/
def c2MatrixBaseSquareChart
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    OpenPartialHomeomorph (C2Matrix period hPeriod)
      (C2Matrix period hPeriod) :=
  (c2MatrixSquare_contDiff_two period hPeriod).contDiffAt
    |>.toOpenPartialHomeomorph
      (c2FiniteMatrixSquare period hPeriod 4)
      ((c2FiniteMatrixSquare_hasFDerivAt period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod root)).congr_fderiv
          (c2MatrixSylvesterEquiv_forward_eq
            period hPeriod root hRegular).symm)
      (by norm_num)

/-- Restriction to the open regular-derivative locus. -/
def c2MatrixLocalSquareChart
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    OpenPartialHomeomorph (C2Matrix period hPeriod)
      (C2Matrix period hPeriod) :=
  (c2MatrixBaseSquareChart period hPeriod root hRegular).restrOpen
    (c2MatrixSylvesterRegularRootSet period hPeriod)
    (c2MatrixSylvesterRegularRootSet_isOpen period hPeriod)

def c2MatrixLocalRootTarget
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Set (C2Matrix period hPeriod) :=
  (c2MatrixLocalSquareChart period hPeriod root hRegular).target

theorem c2MatrixLocalRootTarget_isOpen
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (c2MatrixLocalRootTarget period hPeriod root hRegular) :=
  (c2MatrixLocalSquareChart period hPeriod root hRegular).open_target

theorem smoothMatrixFieldToC2_mem_localSquareChart_source
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    smoothMatrixFieldToC2 period hPeriod root ∈
      (c2MatrixLocalSquareChart period hPeriod root hRegular).source := by
  rw [c2MatrixLocalSquareChart, OpenPartialHomeomorph.restrOpen_source]
  exact ⟨(c2MatrixSquare_contDiff_two period hPeriod).contDiffAt
      |>.mem_toOpenPartialHomeomorph_source
        ((c2FiniteMatrixSquare_hasFDerivAt period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root)).congr_fderiv
            (c2MatrixSylvesterEquiv_forward_eq
              period hPeriod root hRegular).symm)
        (by norm_num),
    smoothMatrixFieldToC2_mem_sylvesterRegularRootSet
      period hPeriod root hRegular⟩

theorem smoothMatrixFieldSquare_mem_localRootTarget
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    c2FiniteMatrixSquare period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod root) ∈
      c2MatrixLocalRootTarget period hPeriod root hRegular := by
  exact (c2MatrixLocalSquareChart period hPeriod root hRegular).map_source
    (smoothMatrixFieldToC2_mem_localSquareChart_source
      period hPeriod root hRegular)

/-- Local root branch on the uniform C² matrix core. -/
def c2MatrixLocalRootBranch
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    C2Matrix period hPeriod → C2Matrix period hPeriod :=
  (c2MatrixLocalSquareChart period hPeriod root hRegular).symm

theorem c2MatrixLocalRootBranch_square
    {root : SmoothQuotientField period hPeriod Matrix4}
    {hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))}
    {nearby : C2Matrix period hPeriod}
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    c2FiniteMatrixSquare period hPeriod 4
        (c2MatrixLocalRootBranch period hPeriod root hRegular nearby) =
      nearby := by
  exact (c2MatrixLocalSquareChart period hPeriod root hRegular).right_inv
    hNearby

theorem c2MatrixLocalRootBranch_at_center
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    c2MatrixLocalRootBranch period hPeriod root hRegular
        (c2FiniteMatrixSquare period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root)) =
      smoothMatrixFieldToC2 period hPeriod root := by
  exact (c2MatrixLocalSquareChart period hPeriod root hRegular).left_inv
    (smoothMatrixFieldToC2_mem_localSquareChart_source
      period hPeriod root hRegular)

theorem c2MatrixLocalRootBranch_contDiffAt
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    ContDiffAt Real 2
      (c2MatrixLocalRootBranch period hPeriod root hRegular) nearby := by
  have hSource :=
    (c2MatrixLocalSquareChart period hPeriod root hRegular).map_target hNearby
  rw [c2MatrixLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  rcases hSource.2 with ⟨equiv, hEquiv⟩
  apply (c2MatrixLocalSquareChart period hPeriod root hRegular)
    |>.contDiffAt_symm hNearby (f₀' := equiv)
  · exact (c2FiniteMatrixSquare_hasFDerivAt period hPeriod 4
      ((c2MatrixLocalSquareChart period hPeriod root hRegular).symm
        nearby)).congr_fderiv hEquiv.symm
  · exact (c2MatrixSquare_contDiff_two period hPeriod).contDiffAt

theorem c2MatrixLocalRootBranch_contDiffOn
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContDiffOn Real 2
      (c2MatrixLocalRootBranch period hPeriod root hRegular)
      (c2MatrixLocalRootTarget period hPeriod root hRegular) := by
  intro nearby hNearby
  exact (c2MatrixLocalRootBranch_contDiffAt
    period hPeriod root hRegular nearby hNearby).contDiffWithinAt

/-- Zero-centered open perturbation domain in the full C² tangent space. -/
def c2MatrixRootPerturbationDomain
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    Set (C2Matrix period hPeriod) :=
  (fun variation =>
    c2FiniteMatrixSquare period hPeriod 4
      (smoothMatrixFieldToC2 period hPeriod root) + variation) ⁻¹'
    c2MatrixLocalRootTarget period hPeriod root hRegular

theorem c2MatrixRootPerturbationDomain_isOpen
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (c2MatrixRootPerturbationDomain
      period hPeriod root hRegular) := by
  exact (c2MatrixLocalRootTarget_isOpen period hPeriod root hRegular)
    |>.preimage (continuous_const.add continuous_id)

theorem zero_mem_c2MatrixRootPerturbationDomain
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    (0 : C2Matrix period hPeriod) ∈
      c2MatrixRootPerturbationDomain period hPeriod root hRegular := by
  simpa [c2MatrixRootPerturbationDomain] using
    smoothMatrixFieldSquare_mem_localRootTarget
      period hPeriod root hRegular

def c2MatrixRootPerturbationBranch
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    C2Matrix period hPeriod → C2Matrix period hPeriod :=
  fun variation => c2MatrixLocalRootBranch period hPeriod root hRegular
    (c2FiniteMatrixSquare period hPeriod 4
      (smoothMatrixFieldToC2 period hPeriod root) + variation)

theorem c2MatrixRootPerturbationBranch_square
    {root : SmoothQuotientField period hPeriod Matrix4}
    {hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))}
    {variation : C2Matrix period hPeriod}
    (hVariation : variation ∈ c2MatrixRootPerturbationDomain
      period hPeriod root hRegular) :
    c2FiniteMatrixSquare period hPeriod 4
        (c2MatrixRootPerturbationBranch
          period hPeriod root hRegular variation) =
      c2FiniteMatrixSquare period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root) + variation :=
  c2MatrixLocalRootBranch_square period hPeriod hVariation

theorem c2MatrixRootPerturbationBranch_contDiffOn
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    ContDiffOn Real 2
      (c2MatrixRootPerturbationBranch period hPeriod root hRegular)
      (c2MatrixRootPerturbationDomain period hPeriod root hRegular) := by
  intro variation hVariation
  have hOuter := c2MatrixLocalRootBranch_contDiffAt period hPeriod
    root hRegular
      (c2FiniteMatrixSquare period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod root) + variation)
      hVariation
  have hInner : ContDiffAt Real 2
      (fun current : C2Matrix period hPeriod =>
        c2FiniteMatrixSquare period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root) + current)
      variation :=
    contDiffAt_const.add contDiffAt_id
  rw [show c2MatrixRootPerturbationBranch period hPeriod root hRegular =
      c2MatrixLocalRootBranch period hPeriod root hRegular ∘
        (fun current : C2Matrix period hPeriod =>
          c2FiniteMatrixSquare period hPeriod 4
            (smoothMatrixFieldToC2 period hPeriod root) + current) by rfl]
  exact (hOuter.comp variation hInner).contDiffWithinAt

/-- Complete local-root certificate on a genuine open neighborhood of zero. -/
theorem canonical_physical_c2_local_root_gate
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point))) :
    IsOpen (c2MatrixRootPerturbationDomain
      period hPeriod root hRegular) ∧
      (0 : C2Matrix period hPeriod) ∈
        c2MatrixRootPerturbationDomain period hPeriod root hRegular ∧
      ContDiffOn Real 2
        (c2MatrixRootPerturbationBranch period hPeriod root hRegular)
        (c2MatrixRootPerturbationDomain period hPeriod root hRegular) ∧
      ∀ variation,
        variation ∈ c2MatrixRootPerturbationDomain
            period hPeriod root hRegular →
          c2FiniteMatrixSquare period hPeriod 4
              (c2MatrixRootPerturbationBranch
                period hPeriod root hRegular variation) =
            c2FiniteMatrixSquare period hPeriod 4
                (smoothMatrixFieldToC2 period hPeriod root) + variation := by
  exact ⟨c2MatrixRootPerturbationDomain_isOpen
      period hPeriod root hRegular,
    zero_mem_c2MatrixRootPerturbationDomain
      period hPeriod root hRegular,
    c2MatrixRootPerturbationBranch_contDiffOn
      period hPeriod root hRegular,
    fun _ hVariation =>
      c2MatrixRootPerturbationBranch_square period hPeriod hVariation⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
end JanusFormal
