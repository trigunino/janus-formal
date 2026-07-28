import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSolidHarmonicCompleteness4D
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier--monopole product density

The exact solid-harmonic packet is combined with the ordinary characters of
the additive circle.  Their products form a uniformly dense subspace of
continuous functions on `S² × S¹`, hence a dense subspace of the associated
geometric `L²` space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleProductDensity4D

set_option autoImplicit false

open Set

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private def starSubalgebraProductSet
    (A : StarSubalgebra ℂ C(X, ℂ))
    (B : StarSubalgebra ℂ C(Y, ℂ)) : Set C(X × Y, ℂ) :=
  {h | ∃ f : A, ∃ g : B, h = ContinuousMap.prodMul f.1 g.1}

def starSubalgebraProduct
    (A : StarSubalgebra ℂ C(X, ℂ))
    (B : StarSubalgebra ℂ C(Y, ℂ)) :
    StarSubalgebra ℂ C(X × Y, ℂ) where
  toSubalgebra :=
    { carrier := Submodule.span ℂ (starSubalgebraProductSet A B)
      add_mem' := (Submodule.span ℂ (starSubalgebraProductSet A B)).add_mem
      mul_mem' := by
        intro first second hFirst hSecond
        refine Submodule.span_induction₂
          (p := fun first second _ _ =>
            first * second ∈
              Submodule.span ℂ (starSubalgebraProductSet A B))
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ hFirst hSecond
        · intro _ _ hFirst hSecond
          rcases hFirst with ⟨f₁, g₁, rfl⟩
          rcases hSecond with ⟨f₂, g₂, rfl⟩
          apply Submodule.subset_span
          exact ⟨⟨f₁ * f₂, mul_mem f₁.2 f₂.2⟩,
            ⟨g₁ * g₂, mul_mem g₁.2 g₂.2⟩, by
              ext point
              simp [ContinuousMap.prodMul_apply]
              ring⟩
        · simp
        · simp
        · intro x y z _ _ _ hx hy
          simpa [add_mul] using Submodule.add_mem _ hx hy
        · intro x y z _ _ _ hx hy
          simpa [mul_add] using Submodule.add_mem _ hx hy
        · intro scalar x y _ _ hx
          simpa [smul_mul_assoc] using
            Submodule.smul_mem
              (Submodule.span ℂ (starSubalgebraProductSet A B)) scalar hx
        · intro scalar x y _ _ hx
          simpa [mul_smul_comm] using
            Submodule.smul_mem
              (Submodule.span ℂ (starSubalgebraProductSet A B)) scalar hx
      algebraMap_mem' := by
        intro scalar
        apply Submodule.subset_span
        refine ⟨⟨algebraMap ℂ C(X, ℂ) scalar, A.algebraMap_mem scalar⟩,
          ⟨1, B.one_mem⟩, ?_⟩
        ext point
        simp [ContinuousMap.prodMul_apply] }
  star_mem' := by
    intro value hValue
    refine Submodule.span_induction
      (p := fun value _ =>
        star value ∈
          Submodule.span ℂ (starSubalgebraProductSet A B))
      ?_ ?_ ?_ ?_ hValue
    · intro value hValue
      rcases hValue with ⟨f, g, rfl⟩
      apply Submodule.subset_span
      exact ⟨⟨star f.1, A.star_mem' f.2⟩,
        ⟨star g.1, B.star_mem' g.2⟩, by
          ext point
          simp [ContinuousMap.prodMul_apply]⟩
    · simp
    · intro x y _ _ hx hy
      simpa [star_add] using Submodule.add_mem _ hx hy
    · intro scalar x _ hx
      simpa [star_smul] using
        Submodule.smul_mem
          (Submodule.span ℂ (starSubalgebraProductSet A B))
            (star scalar) hx

theorem starSubalgebraProduct_separatesPoints
    (A : StarSubalgebra ℂ C(X, ℂ))
    (B : StarSubalgebra ℂ C(Y, ℂ))
    (hA : A.SeparatesPoints) (hB : B.SeparatesPoints) :
    (starSubalgebraProduct A B).SeparatesPoints := by
  intro first second hne
  by_cases hFirst : first.1 = second.1
  · have hSecond : first.2 ≠ second.2 := by
      intro h
      exact hne (Prod.ext hFirst h)
    obtain ⟨_, ⟨g, hg, rfl⟩, hgNe⟩ := hB hSecond
    refine ⟨_, ⟨ContinuousMap.prodMul 1 g,
      Submodule.subset_span ?_, rfl⟩, ?_⟩
    · exact ⟨⟨1, A.one_mem⟩, ⟨g, hg⟩, rfl⟩
    · simpa [ContinuousMap.prodMul_apply] using hgNe
  · obtain ⟨_, ⟨f, hf, rfl⟩, hfNe⟩ := hA hFirst
    refine ⟨_, ⟨ContinuousMap.prodMul f 1,
      Submodule.subset_span ?_, rfl⟩, ?_⟩
    · exact ⟨⟨f, hf⟩, ⟨1, B.one_mem⟩, rfl⟩
    · simpa [ContinuousMap.prodMul_apply] using hfNe

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

theorem starSubalgebraProduct_closure_eq_top
    (A : StarSubalgebra ℂ C(X, ℂ))
    (B : StarSubalgebra ℂ C(Y, ℂ))
    (hA : A.SeparatesPoints) (hB : B.SeparatesPoints) :
    (starSubalgebraProduct A B).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (starSubalgebraProduct A B)
    (starSubalgebraProduct_separatesPoints A B hA hB)

open AddCircle
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCSolidHarmonicCompleteness4D
open P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D

variable (T : ℝ) [Fact (0 < T)]

abbrev FourierMonopoleLabel :=
  SolidHarmonicPacketLabel × ℤ

def fourierMonopoleProduct
    (label : FourierMonopoleLabel) :
    C(MonopoleSphere × AddCircle T, ℂ) :=
  ContinuousMap.prodMul
    (solidHarmonicPacketSphereRestriction label.1)
    (fourier label.2)

def fourierMonopoleProductSpan :
    Submodule ℂ C(MonopoleSphere × AddCircle T, ℂ) :=
  Submodule.span ℂ
    (Set.range (fourierMonopoleProduct (T := T)))

private theorem spherePolynomialRange_eq_starSubalgebra :
    primitiveSpinCSpherePolynomialRestriction.range =
      primitiveSpinCSpherePolynomialStarSubalgebra.toSubalgebra := by
  unfold primitiveSpinCSpherePolynomialRestriction
    primitiveSpinCSpherePolynomialStarSubalgebra
  rw [MvPolynomial.aeval_range]

omit [Fact (0 < T)] in
private theorem product_mem_fourierMonopoleProductSpan
    (sphereFunction : C(MonopoleSphere, ℂ))
    (circleFunction : C(AddCircle T, ℂ))
    (hSphere :
      sphereFunction ∈ solidHarmonicPacketSphereSpan)
    (hCircle :
      circleFunction ∈ Submodule.span ℂ (Set.range (@fourier T))) :
    ContinuousMap.prodMul sphereFunction circleFunction ∈
      fourierMonopoleProductSpan T := by
  refine Submodule.span_induction₂
    (p := fun sphereFunction circleFunction _ _ =>
      ContinuousMap.prodMul sphereFunction circleFunction ∈
        fourierMonopoleProductSpan T)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hSphere hCircle
  · rintro _ _ ⟨sphereLabel, rfl⟩ ⟨circleLabel, rfl⟩
    exact Submodule.subset_span
      ⟨(sphereLabel, circleLabel), rfl⟩
  · simp
  · simp
  · intro x y z _ _ _ hx hy
    simpa [ContinuousMap.prodMul_def, add_mul] using
      (fourierMonopoleProductSpan T).add_mem hx hy
  · intro x y z _ _ _ hx hy
    simpa [ContinuousMap.prodMul_def, mul_add] using
      (fourierMonopoleProductSpan T).add_mem hx hy
  · intro scalar x y _ _ hx
    simpa [ContinuousMap.prodMul_def, smul_mul_assoc] using
      (fourierMonopoleProductSpan T).smul_mem scalar hx
  · intro scalar x y _ _ hx
    simpa [ContinuousMap.prodMul_def, mul_smul_comm] using
      (fourierMonopoleProductSpan T).smul_mem scalar hx

omit [Fact (0 < T)] in
theorem fourierMonopoleProductSpan_eq_productStarSubalgebra :
    fourierMonopoleProductSpan T =
      (starSubalgebraProduct
        primitiveSpinCSpherePolynomialStarSubalgebra
        (@fourierSubalgebra T)).toSubalgebra.toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨label, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨solidHarmonicPacketSphereRestriction label.1, ?_⟩,
      ⟨fourier label.2, ?_⟩, rfl⟩
    · change
        solidHarmonicPacketSphereRestriction label.1 ∈
          primitiveSpinCSpherePolynomialStarSubalgebra.toSubalgebra
      rw [← spherePolynomialRange_eq_starSubalgebra]
      exact
        ⟨primitiveSpinCSolidHarmonicPacket label.1.1 label.1.2, rfl⟩
    · exact Algebra.subset_adjoin ⟨label.2, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨sphereFunction, circleFunction, rfl⟩
    apply product_mem_fourierMonopoleProductSpan T
    · rw [solidHarmonicPacketSphereSpan_eq_polynomialSubmodule]
      change
        sphereFunction.1 ∈
          primitiveSpinCSpherePolynomialRestriction.range.toSubmodule
      rw [spherePolynomialRange_eq_starSubalgebra]
      exact sphereFunction.2
    · rw [← fourierSubalgebra_coe]
      exact circleFunction.2

theorem fourierMonopoleProductSpan_closure_eq_top :
    (fourierMonopoleProductSpan T).topologicalClosure = ⊤ := by
  rw [fourierMonopoleProductSpan_eq_productStarSubalgebra]
  exact congr_arg
    (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (starSubalgebraProduct
        primitiveSpinCSpherePolynomialStarSubalgebra
        (@fourierSubalgebra T))
      (starSubalgebraProduct_separatesPoints
        primitiveSpinCSpherePolynomialStarSubalgebra
        (@fourierSubalgebra T)
        primitiveSpinCSpherePolynomialStarSubalgebra_separatesPoints
        fourierSubalgebra_separatesPoints))

def fourierMonopoleProductMeasure :
    MeasureTheory.Measure (MonopoleSphere × AddCircle T) :=
  primitiveSpinCSphereMeasure.prod (@haarAddCircle T _)

local instance fourierMonopoleProductMeasureFinite :
    MeasureTheory.IsFiniteMeasure (fourierMonopoleProductMeasure T) := by
  unfold fourierMonopoleProductMeasure primitiveSpinCSphereMeasure
  infer_instance

local instance fourierMonopoleProductMeasureWeaklyRegular :
    (fourierMonopoleProductMeasure T).WeaklyRegular := by
  unfold fourierMonopoleProductMeasure primitiveSpinCSphereMeasure
  infer_instance

def fourierMonopoleProductToL2 :
    fourierMonopoleProductSpan T →L[ℂ]
      MeasureTheory.Lp ℂ (2 : ENNReal)
        (fourierMonopoleProductMeasure T) :=
  (ContinuousMap.toLp
      (2 : ENNReal) (fourierMonopoleProductMeasure T) ℂ).comp
    (fourierMonopoleProductSpan T).subtypeL

theorem fourierMonopoleProductToL2_denseRange :
    DenseRange (fourierMonopoleProductToL2 T) := by
  have hLp :
      DenseRange
        (ContinuousMap.toLp
          (2 : ENNReal) (fourierMonopoleProductMeasure T) ℂ) :=
    ContinuousMap.toLp_denseRange ℂ
      (fourierMonopoleProductMeasure T) ℂ
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hSubtype :
      DenseRange (fourierMonopoleProductSpan T).subtypeL := by
    change Dense (Set.range (fourierMonopoleProductSpan T).subtypeL)
    rw [show
      Set.range (fourierMonopoleProductSpan T).subtypeL =
        (fourierMonopoleProductSpan T :
          Set C(MonopoleSphere × AddCircle T, ℂ)) by
      ext continuousFunction
      constructor
      · rintro ⟨packetFunction, rfl⟩
        exact packetFunction.property
      · intro hPacket
        exact ⟨⟨continuousFunction, hPacket⟩, rfl⟩]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (fourierMonopoleProductSpan_closure_eq_top T)
  unfold fourierMonopoleProductToL2
  simpa only [ContinuousLinearMap.coe_comp] using
    hLp.comp hSubtype
      (ContinuousMap.toLp
        (2 : ENNReal) (fourierMonopoleProductMeasure T) ℂ).continuous

end
end P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleProductDensity4D
end JanusFormal
