import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Polynomial density on the primitive SpinC sphere

The ambient coordinate polynomials separate points of the monopole sphere.
Stone--Weierstrass therefore makes their restrictions dense first in the
uniform topology and then in the geometric sphere `L²` space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D

set_option autoImplicit false
noncomputable section

open Set
open MeasureTheory
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D

/-- A complex-valued ambient coordinate restricted to the monopole sphere. -/
def primitiveSpinCSphereCoordinateContinuousMap (coordinate : Fin 3) :
    C(MonopoleSphere, Complex) where
  toFun point :=
    Complex.ofReal (monopoleSphereCoordinate point coordinate)
  continuous_toFun :=
    Complex.continuous_ofReal.comp
      (monopoleSphereCoordinate_continuous coordinate)

/-- The coordinate-polynomial star subalgebra on the monopole sphere. -/
def primitiveSpinCSpherePolynomialStarSubalgebra :
    StarSubalgebra Complex C(MonopoleSphere, Complex) where
  toSubalgebra :=
    Algebra.adjoin Complex
      (Set.range primitiveSpinCSphereCoordinateContinuousMap)
  star_mem' := by
    change
      Algebra.adjoin Complex
          (Set.range primitiveSpinCSphereCoordinateContinuousMap) ≤
        star (Algebra.adjoin Complex
          (Set.range primitiveSpinCSphereCoordinateContinuousMap))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨coordinate, rfl⟩
    exact Algebra.subset_adjoin ⟨coordinate, by
      ext point
      simp [primitiveSpinCSphereCoordinateContinuousMap]⟩

theorem primitiveSpinCSpherePolynomialStarSubalgebra_separatesPoints :
    primitiveSpinCSpherePolynomialStarSubalgebra.SeparatesPoints := by
  intro point₁ point₂ hne
  have hCoordinate :
      ∃ coordinate : Fin 3,
        monopoleSphereCoordinate point₁ coordinate ≠
          monopoleSphereCoordinate point₂ coordinate := by
    by_contra h
    push Not at h
    apply hne
    apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    exact h coordinate
  obtain ⟨coordinate, hCoordinate⟩ := hCoordinate
  refine ⟨_, ⟨primitiveSpinCSphereCoordinateContinuousMap coordinate,
    Algebra.subset_adjoin ⟨coordinate, rfl⟩, rfl⟩, ?_⟩
  exact Complex.ofReal_injective.ne hCoordinate

/-- Coordinate polynomials are uniformly dense on the monopole sphere. -/
theorem primitiveSpinCSpherePolynomialStarSubalgebra_closure_eq_top :
    primitiveSpinCSpherePolynomialStarSubalgebra.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    primitiveSpinCSpherePolynomialStarSubalgebra
    primitiveSpinCSpherePolynomialStarSubalgebra_separatesPoints

/-- Restriction of an ambient three-variable polynomial to the unit sphere. -/
def primitiveSpinCSpherePolynomialRestriction :
    PrimitiveSpinCSolidPolynomial →ₐ[Complex]
      C(MonopoleSphere, Complex) :=
  MvPolynomial.aeval primitiveSpinCSphereCoordinateContinuousMap

/-- The range of polynomial restriction is uniformly dense. -/
theorem primitiveSpinCSpherePolynomialRestriction_range_closure_eq_top :
    (primitiveSpinCSpherePolynomialRestriction.range.toSubmodule
      ).topologicalClosure = ⊤ := by
  unfold primitiveSpinCSpherePolynomialRestriction
  rw [MvPolynomial.aeval_range]
  exact
    congr_arg
      (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
      primitiveSpinCSpherePolynomialStarSubalgebra_closure_eq_top

/-- The standard geometric surface measure on the monopole sphere. -/
def primitiveSpinCSphereMeasure : Measure MonopoleSphere :=
  (volume : Measure (EuclideanSpace Real (Fin 3))).toSphere

local instance primitiveSpinCSphereMeasureFinite :
    IsFiniteMeasure primitiveSpinCSphereMeasure := by
  unfold primitiveSpinCSphereMeasure
  infer_instance

local instance primitiveSpinCSphereMeasureWeaklyRegular :
    primitiveSpinCSphereMeasure.WeaklyRegular := by
  infer_instance

/-- Continuous coordinate-polynomial functions, as a complex submodule. -/
def primitiveSpinCSpherePolynomialContinuousSubmodule :
    Submodule Complex C(MonopoleSphere, Complex) :=
  primitiveSpinCSpherePolynomialRestriction.range.toSubmodule

/-- Inclusion of continuous coordinate polynomials into geometric sphere
`L²`. -/
def primitiveSpinCSpherePolynomialToL2 :
    primitiveSpinCSpherePolynomialContinuousSubmodule →L[Complex]
      Lp Complex (2 : ENNReal) primitiveSpinCSphereMeasure :=
  (ContinuousMap.toLp (2 : ENNReal) primitiveSpinCSphereMeasure Complex).comp
    primitiveSpinCSpherePolynomialContinuousSubmodule.subtypeL

/-- Coordinate polynomials are dense in geometric sphere `L²`. -/
theorem primitiveSpinCSpherePolynomialToL2_denseRange :
    DenseRange primitiveSpinCSpherePolynomialToL2 := by
  have hLp :
      DenseRange
        (ContinuousMap.toLp (2 : ENNReal)
          primitiveSpinCSphereMeasure Complex) :=
    ContinuousMap.toLp_denseRange Complex
      primitiveSpinCSphereMeasure Complex
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hSubtype :
      DenseRange
        primitiveSpinCSpherePolynomialContinuousSubmodule.subtypeL := by
    change Dense
      (Set.range primitiveSpinCSpherePolynomialContinuousSubmodule.subtypeL)
    rw [show
      Set.range primitiveSpinCSpherePolynomialContinuousSubmodule.subtypeL =
        (primitiveSpinCSpherePolynomialContinuousSubmodule :
          Set C(MonopoleSphere, Complex)) by
      ext continuousFunction
      constructor
      · rintro ⟨polynomialFunction, rfl⟩
        exact polynomialFunction.property
      · intro hPolynomial
        exact ⟨⟨continuousFunction, hPolynomial⟩, rfl⟩]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      primitiveSpinCSpherePolynomialRestriction_range_closure_eq_top
  unfold primitiveSpinCSpherePolynomialToL2
  simpa only [ContinuousLinearMap.coe_comp] using
    hLp.comp hSubtype
      (ContinuousMap.toLp (2 : ENNReal)
        primitiveSpinCSphereMeasure Complex).continuous

/-- Auditable polynomial-density certificate. -/
structure PrimitiveSpinCSpherePolynomialDensityCertificate4D : Prop where
  uniform_density :
    (primitiveSpinCSpherePolynomialRestriction.range.toSubmodule
      ).topologicalClosure = ⊤
  l2_density :
    DenseRange primitiveSpinCSpherePolynomialToL2

def primitiveSpinCSpherePolynomialDensityCertificate4D :
    PrimitiveSpinCSpherePolynomialDensityCertificate4D where
  uniform_density :=
    primitiveSpinCSpherePolynomialRestriction_range_closure_eq_top
  l2_density :=
    primitiveSpinCSpherePolynomialToL2_denseRange

theorem primitiveSpinCSpherePolynomialDensityGate4D :
    Nonempty PrimitiveSpinCSpherePolynomialDensityCertificate4D :=
  ⟨primitiveSpinCSpherePolynomialDensityCertificate4D⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D
end JanusFormal
