import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D

/-!
# Canonical uniform second-jet core on the compact quotient

The existing finite smooth tangent generators give genuine first and ordered
second derivatives of every smooth scalar.  Their value, first derivative and
second derivative form one continuous finite jet on the compact quotient.
Taking the closed smooth range produces a complete uniform `C²`-jet core.

The exact second-order Leibniz rule supplies a bounded bilinear product on the
ambient continuous jets.  The smooth range is stable under this product, so
the product restricts to the closed core.  No Sobolev embedding, global frame
or extra regularity axiom is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

private abbrev physicalFrame := finiteSmoothTangentFrame period hPeriod

/-- Value, finite-frame first derivatives and ordered second derivatives. -/
abbrev ScalarFrameJet2 (Index : Type*) :=
  Real × ((Index → Real) × (Index → Index → Real))

private abbrev PhysicalScalarJet2Fiber :=
  ScalarFrameJet2 (Fin (physicalFrame period hPeriod).count)

/-- A first derivative component, retained as a genuine smooth scalar field. -/
def frameDerivativeComponentField
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (index : Fin frame.count) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    frameDerivative period hPeriod Real frame field point index
  contMDiff_toFun :=
    (contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real frame field)) index

theorem frameDerivativeComponentField_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real)
    (index : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame (first + second) index =
      frameDerivativeComponentField period hPeriod frame first index +
        frameDerivativeComponentField period hPeriod frame second index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact congrFun (congrFun
    (frameDerivative_add period hPeriod Real frame first second) point) index

theorem frameDerivativeComponentField_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real) (field : SmoothQuotientField period hPeriod Real)
    (index : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame (scalar • field) index =
      scalar • frameDerivativeComponentField period hPeriod frame field index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact congrFun (congrFun
    (frameDerivative_smul period hPeriod Real frame scalar field) point) index

/-- Ordered derivatives `X_outer (X_inner field)` in the finite spanning
family.  Symmetry is not asserted because the generators need not commute. -/
def frameSecondDerivative
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    Fin frame.count → Fin frame.count → Real :=
  fun outer inner =>
    frameDerivative period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame field inner)
      point outer

theorem frameSecondDerivative_contMDiff
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ContMDiff coverModelWithCorners
      𝓘(Real, Fin frame.count → Fin frame.count → Real) ∞
      (frameSecondDerivative period hPeriod frame field) := by
  rw [contMDiff_pi_space]
  intro outer
  rw [contMDiff_pi_space]
  intro inner
  exact (contMDiff_pi_space.mp
    (frameDerivative_contMDiff period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame field inner))) outer

theorem frameSecondDerivative_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    frameSecondDerivative period hPeriod frame (first + second) =
      frameSecondDerivative period hPeriod frame first +
        frameSecondDerivative period hPeriod frame second := by
  funext point outer inner
  change frameDerivative period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame
        (first + second) inner) point outer = _
  rw [frameDerivativeComponentField_add,
    frameDerivative_add]
  rfl

theorem frameSecondDerivative_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real) (field : SmoothQuotientField period hPeriod Real) :
    frameSecondDerivative period hPeriod frame (scalar • field) =
      scalar • frameSecondDerivative period hPeriod frame field := by
  funext point outer inner
  change frameDerivative period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame
        (scalar • field) inner) point outer = _
  rw [frameDerivativeComponentField_smul,
    frameDerivative_smul]
  rfl

/-- The genuine global uniform second jet of one smooth scalar. -/
def smoothScalarFrameJet2
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    ScalarFrameJet2 (Fin frame.count) :=
  (field point,
    (frameDerivative period hPeriod Real frame field point,
      frameSecondDerivative period hPeriod frame field point))

theorem smoothScalarFrameJet2_contMDiff
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ContMDiff coverModelWithCorners
      𝓘(Real, ScalarFrameJet2 (Fin frame.count)) ∞
      (smoothScalarFrameJet2 period hPeriod frame field) :=
  field.contMDiff_toFun.prodMk_space
    ((frameDerivative_contMDiff period hPeriod Real frame field).prodMk_space
      (frameSecondDerivative_contMDiff period hPeriod frame field))

theorem smoothScalarFrameJet2_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    smoothScalarFrameJet2 period hPeriod frame (first + second) =
      smoothScalarFrameJet2 period hPeriod frame first +
        smoothScalarFrameJet2 period hPeriod frame second := by
  funext point
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrFun
        (frameDerivative_add period hPeriod Real frame first second) point
    · exact congrFun
        (frameSecondDerivative_add period hPeriod frame first second) point

theorem smoothScalarFrameJet2_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real) (field : SmoothQuotientField period hPeriod Real) :
    smoothScalarFrameJet2 period hPeriod frame (scalar • field) =
      scalar • smoothScalarFrameJet2 period hPeriod frame field := by
  funext point
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrFun
        (frameDerivative_smul period hPeriod Real frame scalar field) point
    · exact congrFun
        (frameSecondDerivative_smul period hPeriod frame scalar field) point

/-- Continuous uniform second jets on the compact quotient. -/
abbrev CanonicalPhysicalScalarC2JetAmbient :=
  C(EffectiveQuotient period hPeriod, PhysicalScalarJet2Fiber period hPeriod)

/-- Exact smooth second-jet map into the uniform Banach ambient space. -/
def smoothScalarFrameJet2ContinuousLinearMap :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarC2JetAmbient period hPeriod where
  toFun field :=
    ⟨smoothScalarFrameJet2 period hPeriod (physicalFrame period hPeriod) field,
      (smoothScalarFrameJet2_contMDiff period hPeriod
        (physicalFrame period hPeriod) field).continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    exact congrFun
      (smoothScalarFrameJet2_add period hPeriod
        (physicalFrame period hPeriod) first second) point
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro point
    exact congrFun
      (smoothScalarFrameJet2_smul period hPeriod
        (physicalFrame period hPeriod) scalar field) point

/-- Closed uniform second-jet core generated by actual smooth scalars. -/
def canonicalPhysicalScalarC2JetCoreSubmodule :
    Submodule Real (CanonicalPhysicalScalarC2JetAmbient period hPeriod) :=
  (LinearMap.range
    (smoothScalarFrameJet2ContinuousLinearMap
      period hPeriod)).topologicalClosure

/-- Complete scalar domain controlling values and two spacetime derivatives. -/
abbrev CanonicalPhysicalScalarC2JetCore :=
  canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod

theorem canonicalPhysicalScalarC2JetCore_isClosed :
    IsClosed
      (CanonicalPhysicalScalarC2JetCore period hPeriod :
        Set (CanonicalPhysicalScalarC2JetAmbient period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def canonicalPhysicalScalarC2JetCoreCompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (smoothScalarFrameJet2ContinuousLinearMap period hPeriod))

/-- Exact smooth fields lifted into the closed uniform second-jet core. -/
def smoothToCanonicalPhysicalScalarC2JetCore :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarC2JetCore period hPeriod where
  toFun field :=
    ⟨smoothScalarFrameJet2ContinuousLinearMap period hPeriod field,
      (LinearMap.range
        (smoothScalarFrameJet2ContinuousLinearMap
          period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothScalarFrameJet2ContinuousLinearMap period hPeriod) field)⟩
  map_add' first second := Subtype.ext
    ((smoothScalarFrameJet2ContinuousLinearMap
      period hPeriod).map_add first second)
  map_smul' scalar field := Subtype.ext
    ((smoothScalarFrameJet2ContinuousLinearMap
      period hPeriod).map_smul scalar field)

/-- The completed second-jet lift retains the scalar value, hence is
faithful on genuine smooth fields. -/
theorem smoothToCanonicalPhysicalScalarC2JetCore_injective :
    Function.Injective
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) := by
  intro first second hEqual
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hAmbient := congrArg Subtype.val hEqual
  exact congrArg (fun jet => (jet point).1) hAmbient

theorem smoothToCanonicalPhysicalScalarC2JetCore_denseRange :
    DenseRange
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := smoothScalarFrameJet2ContinuousLinearMap period hPeriod
  have hRange :
      Subtype.val '' Set.range
          (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) =
        (LinearMap.range inclusion :
          Set (CanonicalPhysicalScalarC2JetAmbient period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨field, rfl⟩, rfl⟩
      exact ⟨field, rfl⟩
    · rintro ⟨field, rfl⟩
      exact ⟨smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod field, ⟨field, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion :
      Set (CanonicalPhysicalScalarC2JetAmbient period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod))
  rw [hRange]

/-- Ambient inclusion of the completed second-jet core. -/
def canonicalPhysicalScalarC2JetCoreToAmbient :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      CanonicalPhysicalScalarC2JetAmbient period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).subtypeL

/-! ## Exact second-order Leibniz algebra -/

/-- Algebraic multiplication of ordered scalar second jets. -/
def scalarFrameJet2Mul {Index : Type*}
    (first second : ScalarFrameJet2 Index) : ScalarFrameJet2 Index :=
  (first.1 * second.1,
    (fun i => first.1 * second.2.1 i + second.1 * first.2.1 i,
      fun outer inner =>
        first.1 * second.2.2 outer inner +
          first.2.1 outer * second.2.1 inner +
          second.2.1 outer * first.2.1 inner +
          second.1 * first.2.2 outer inner))

theorem frameDerivativeComponentField_mul
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real)
    (index : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame
        (smoothScalarFieldMul period hPeriod first second) index =
      smoothScalarFieldMul period hPeriod first
          (frameDerivativeComponentField period hPeriod frame second index) +
        smoothScalarFieldMul period hPeriod second
          (frameDerivativeComponentField period hPeriod frame first index) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact congrFun (congrFun
    (frameDerivative_mul period hPeriod frame first second) point) index

theorem frameSecondDerivative_mul
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    frameSecondDerivative period hPeriod frame
        (smoothScalarFieldMul period hPeriod first second) =
      fun point outer inner =>
        first point *
            frameSecondDerivative period hPeriod frame second point outer inner +
          frameDerivative period hPeriod Real frame first point outer *
            frameDerivative period hPeriod Real frame second point inner +
          frameDerivative period hPeriod Real frame second point outer *
            frameDerivative period hPeriod Real frame first point inner +
          second point *
            frameSecondDerivative period hPeriod frame first point outer inner := by
  funext point outer inner
  change frameDerivative period hPeriod Real frame
      (frameDerivativeComponentField period hPeriod frame
        (smoothScalarFieldMul period hPeriod first second) inner)
      point outer = _
  rw [frameDerivativeComponentField_mul,
    frameDerivative_add,
    frameDerivative_mul,
    frameDerivative_mul]
  simp only [Pi.add_apply, frameDerivativeComponentField,
    frameSecondDerivative]
  ring

/-- The genuine smooth second jet is multiplicative for the exact jet
Leibniz product. -/
theorem smoothScalarFrameJet2_mul
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    smoothScalarFrameJet2 period hPeriod frame
        (smoothScalarFieldMul period hPeriod first second) =
      fun point => scalarFrameJet2Mul
        (smoothScalarFrameJet2 period hPeriod frame first point)
        (smoothScalarFrameJet2 period hPeriod frame second point) := by
  funext point
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrArg Prod.snd
        (congrFun (smoothFirstJet_mul period hPeriod frame first second) point)
    · exact congrFun
        (frameSecondDerivative_mul period hPeriod frame first second) point

private theorem scalarFrameJet2Mul_add_left
    {Index : Type*} [Fintype Index]
    (first second third : ScalarFrameJet2 Index) :
    scalarFrameJet2Mul (first + second) third =
      scalarFrameJet2Mul first third + scalarFrameJet2Mul second third := by
  apply Prod.ext
  · simp [scalarFrameJet2Mul]
    ring
  · apply Prod.ext
    · funext i
      simp [scalarFrameJet2Mul]
      ring
    · funext i j
      simp [scalarFrameJet2Mul]
      ring

private theorem scalarFrameJet2Mul_smul_left
    {Index : Type*} [Fintype Index]
    (scalar : Real) (first second : ScalarFrameJet2 Index) :
    scalarFrameJet2Mul (scalar • first) second =
      scalar • scalarFrameJet2Mul first second := by
  apply Prod.ext
  · simp [scalarFrameJet2Mul, smul_eq_mul]
    ring
  · apply Prod.ext
    · funext i
      simp [scalarFrameJet2Mul, smul_eq_mul]
      ring
    · funext i j
      simp [scalarFrameJet2Mul, smul_eq_mul]
      ring

private theorem scalarFrameJet2Mul_add_right
    {Index : Type*} [Fintype Index]
    (first second third : ScalarFrameJet2 Index) :
    scalarFrameJet2Mul first (second + third) =
      scalarFrameJet2Mul first second + scalarFrameJet2Mul first third := by
  apply Prod.ext
  · simp [scalarFrameJet2Mul]
    ring
  · apply Prod.ext
    · funext i
      simp [scalarFrameJet2Mul]
      ring
    · funext i j
      simp [scalarFrameJet2Mul]
      ring

private theorem scalarFrameJet2Mul_smul_right
    {Index : Type*} [Fintype Index]
    (scalar : Real) (first second : ScalarFrameJet2 Index) :
    scalarFrameJet2Mul first (scalar • second) =
      scalar • scalarFrameJet2Mul first second := by
  apply Prod.ext
  · simp [scalarFrameJet2Mul, smul_eq_mul]
    ring
  · apply Prod.ext
    · funext i
      simp [scalarFrameJet2Mul, smul_eq_mul]
      ring
    · funext i j
      simp [scalarFrameJet2Mul, smul_eq_mul]
      ring

private theorem scalarFrameJet2_value_norm_le
    {Index : Type*} [Fintype Index]
    (jet : ScalarFrameJet2 Index) : ‖jet.1‖ ≤ ‖jet‖ :=
  norm_fst_le jet

private theorem scalarFrameJet2_first_norm_le
    {Index : Type*} [Fintype Index]
    (jet : ScalarFrameJet2 Index) (index : Index) :
    ‖jet.2.1 index‖ ≤ ‖jet‖ :=
  (norm_le_pi_norm jet.2.1 index).trans
    ((norm_fst_le jet.2).trans (norm_snd_le jet))

private theorem scalarFrameJet2_second_norm_le
    {Index : Type*} [Fintype Index]
    (jet : ScalarFrameJet2 Index) (outer inner : Index) :
    ‖jet.2.2 outer inner‖ ≤ ‖jet‖ :=
  (norm_le_pi_norm (jet.2.2 outer) inner).trans
    ((norm_le_pi_norm jet.2.2 outer).trans
      ((norm_snd_le jet.2).trans (norm_snd_le jet)))

/-- Uniform finite-dimensional estimate for the ordered second-jet product. -/
theorem scalarFrameJet2Mul_norm_le
    {Index : Type*} [Fintype Index]
    (first second : ScalarFrameJet2 Index) :
    ‖scalarFrameJet2Mul first second‖ ≤
      4 * ‖first‖ * ‖second‖ := by
  let bound := ‖first‖ * ‖second‖
  have hBound : 0 ≤ bound := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  suffices hFinal : ‖scalarFrameJet2Mul first second‖ ≤ 4 * bound by
    simpa only [bound, mul_assoc] using hFinal
  have hValue : ‖first.1 * second.1‖ ≤ bound := by
    rw [norm_mul]
    exact mul_le_mul
      (scalarFrameJet2_value_norm_le first)
      (scalarFrameJet2_value_norm_le second)
      (norm_nonneg _) (norm_nonneg _)
  have hFirst (index : Index) :
      ‖first.1 * second.2.1 index + second.1 * first.2.1 index‖ ≤
        2 * bound := by
    calc
      _ ≤ ‖first.1 * second.2.1 index‖ +
          ‖second.1 * first.2.1 index‖ := norm_add_le _ _
      _ = ‖first.1‖ * ‖second.2.1 index‖ +
          ‖second.1‖ * ‖first.2.1 index‖ := by rw [norm_mul, norm_mul]
      _ ≤ bound + bound := add_le_add
        (mul_le_mul
          (scalarFrameJet2_value_norm_le first)
          (scalarFrameJet2_first_norm_le second index)
          (norm_nonneg _) (norm_nonneg _))
        (calc
          ‖second.1‖ * ‖first.2.1 index‖ ≤ ‖second‖ * ‖first‖ :=
            mul_le_mul
              (scalarFrameJet2_value_norm_le second)
              (scalarFrameJet2_first_norm_le first index)
              (norm_nonneg _) (norm_nonneg _)
          _ = bound := by simp only [bound]; ring)
      _ = 2 * bound := by ring
  have hSecond (outer inner : Index) :
      ‖first.1 * second.2.2 outer inner +
          first.2.1 outer * second.2.1 inner +
          second.2.1 outer * first.2.1 inner +
          second.1 * first.2.2 outer inner‖ ≤ 4 * bound := by
    calc
      _ ≤ ‖first.1 * second.2.2 outer inner‖ +
            ‖first.2.1 outer * second.2.1 inner‖ +
            ‖second.2.1 outer * first.2.1 inner‖ +
            ‖second.1 * first.2.2 outer inner‖ := by
          grw [norm_add_le, norm_add_le, norm_add_le]
      _ = ‖first.1‖ * ‖second.2.2 outer inner‖ +
            ‖first.2.1 outer‖ * ‖second.2.1 inner‖ +
            ‖second.2.1 outer‖ * ‖first.2.1 inner‖ +
            ‖second.1‖ * ‖first.2.2 outer inner‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
      _ ≤ bound + bound + bound + bound := by
          apply add_le_add
          · apply add_le_add
            · apply add_le_add
              · exact mul_le_mul
                  (scalarFrameJet2_value_norm_le first)
                  (scalarFrameJet2_second_norm_le second outer inner)
                  (norm_nonneg _) (norm_nonneg _)
              · exact mul_le_mul
                  (scalarFrameJet2_first_norm_le first outer)
                  (scalarFrameJet2_first_norm_le second inner)
                  (norm_nonneg _) (norm_nonneg _)
            · calc
                ‖second.2.1 outer‖ * ‖first.2.1 inner‖ ≤
                    ‖second‖ * ‖first‖ :=
                  mul_le_mul
                    (scalarFrameJet2_first_norm_le second outer)
                    (scalarFrameJet2_first_norm_le first inner)
                    (norm_nonneg _) (norm_nonneg _)
                _ = bound := by simp only [bound]; ring
          · calc
              ‖second.1‖ * ‖first.2.2 outer inner‖ ≤
                  ‖second‖ * ‖first‖ :=
                mul_le_mul
                  (scalarFrameJet2_value_norm_le second)
                  (scalarFrameJet2_second_norm_le first outer inner)
                  (norm_nonneg _) (norm_nonneg _)
              _ = bound := by simp only [bound]; ring
      _ = 4 * bound := by ring
  simp only [scalarFrameJet2Mul, Prod.norm_def]
  apply max_le
  · exact hValue.trans (by nlinarith)
  · apply max_le
    · rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 4 * bound)]
      intro index
      exact (hFirst index).trans (by nlinarith)
    · rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 4 * bound)]
      intro outer
      rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 4 * bound)]
      intro inner
      exact hSecond outer inner

/-- Pointwise Leibniz multiplication of continuous second jets. -/
def continuousScalarFrameJet2Mul
    (first second : CanonicalPhysicalScalarC2JetAmbient period hPeriod) :
    CanonicalPhysicalScalarC2JetAmbient period hPeriod where
  toFun := fun point => scalarFrameJet2Mul (first point) (second point)
  continuous_toFun := by
    dsimp only [scalarFrameJet2Mul]
    fun_prop

theorem continuousScalarFrameJet2Mul_norm_le
    (first second : CanonicalPhysicalScalarC2JetAmbient period hPeriod) :
    ‖continuousScalarFrameJet2Mul period hPeriod first second‖ ≤
      4 * ‖first‖ * ‖second‖ := by
  apply (ContinuousMap.norm_le _ (by positivity :
    0 ≤ 4 * ‖first‖ * ‖second‖)).2
  intro point
  calc
    _ ≤ 4 * ‖first point‖ * ‖second point‖ :=
      scalarFrameJet2Mul_norm_le (first point) (second point)
    _ ≤ 4 * ‖first‖ * ‖second‖ := by
      gcongr
      · exact first.norm_coe_le_norm point
      · exact second.norm_coe_le_norm point

/-- Bounded bilinear multiplication on all continuous uniform second jets. -/
def continuousScalarFrameJet2MulBilinear :
    CanonicalPhysicalScalarC2JetAmbient period hPeriod →L[Real]
      CanonicalPhysicalScalarC2JetAmbient period hPeriod →L[Real]
        CanonicalPhysicalScalarC2JetAmbient period hPeriod :=
  (LinearMap.mk₂ Real
    (continuousScalarFrameJet2Mul period hPeriod)
    (by
      intro first second third
      apply ContinuousMap.ext
      intro point
      exact scalarFrameJet2Mul_add_left
        (first point) (second point) (third point))
    (by
      intro scalar first second
      apply ContinuousMap.ext
      intro point
      exact scalarFrameJet2Mul_smul_left scalar (first point) (second point))
    (by
      intro first second third
      apply ContinuousMap.ext
      intro point
      exact scalarFrameJet2Mul_add_right
        (first point) (second point) (third point))
    (by
      intro scalar first second
      apply ContinuousMap.ext
      intro point
      exact scalarFrameJet2Mul_smul_right scalar (first point) (second point)
    )).mkContinuous₂ 4
      (continuousScalarFrameJet2Mul_norm_le period hPeriod)

@[simp]
theorem continuousScalarFrameJet2MulBilinear_apply
    (first second : CanonicalPhysicalScalarC2JetAmbient period hPeriod) :
    continuousScalarFrameJet2MulBilinear period hPeriod first second =
      continuousScalarFrameJet2Mul period hPeriod first second :=
  rfl

private theorem continuousScalarFrameJet2Mul_mem_core
    (first second : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    continuousScalarFrameJet2Mul period hPeriod first.1 second.1 ∈
      canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod := by
  apply map_mem_closure₂
    (continuousScalarFrameJet2MulBilinear
      period hPeriod).continuous₂ first.2 second.2
  intro firstJet hFirst secondJet hSecond
  rcases hFirst with ⟨firstField, rfl⟩
  rcases hSecond with ⟨secondField, rfl⟩
  refine ⟨smoothScalarFieldMul period hPeriod firstField secondField, ?_⟩
  apply ContinuousMap.ext
  intro point
  exact congrFun
    (smoothScalarFrameJet2_mul period hPeriod
      (physicalFrame period hPeriod) firstField secondField) point

/-- The pointwise product already known to remain in the closed core. -/
def canonicalPhysicalScalarC2JetCoreProductValue
    (first second : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    CanonicalPhysicalScalarC2JetCore period hPeriod :=
  ⟨continuousScalarFrameJet2Mul period hPeriod first.1 second.1,
    continuousScalarFrameJet2Mul_mem_core period hPeriod first second⟩

private theorem canonicalPhysicalScalarC2JetCoreProductValue_norm_le
    (first second : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    ‖canonicalPhysicalScalarC2JetCoreProductValue
        period hPeriod first second‖ ≤
      4 * ‖first‖ * ‖second‖ := by
  change ‖continuousScalarFrameJet2Mul period hPeriod first.1 second.1‖ ≤
    4 * ‖first.1‖ * ‖second.1‖
  exact continuousScalarFrameJet2Mul_norm_le
    period hPeriod first.1 second.1

private theorem canonicalPhysicalScalarC2JetCoreProductValue_add_left
    (first second third : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProductValue period hPeriod
        (first + second) third =
      canonicalPhysicalScalarC2JetCoreProductValue period hPeriod first third +
        canonicalPhysicalScalarC2JetCoreProductValue period hPeriod second third := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  exact scalarFrameJet2Mul_add_left
    (first.1 point) (second.1 point) (third.1 point)

private theorem canonicalPhysicalScalarC2JetCoreProductValue_smul_left
    (scalar : Real)
    (first second : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProductValue period hPeriod
        (scalar • first) second =
      scalar • canonicalPhysicalScalarC2JetCoreProductValue
        period hPeriod first second := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  exact scalarFrameJet2Mul_smul_left
    scalar (first.1 point) (second.1 point)

private theorem canonicalPhysicalScalarC2JetCoreProductValue_add_right
    (first second third : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProductValue period hPeriod
        first (second + third) =
      canonicalPhysicalScalarC2JetCoreProductValue period hPeriod first second +
        canonicalPhysicalScalarC2JetCoreProductValue period hPeriod first third := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  exact scalarFrameJet2Mul_add_right
    (first.1 point) (second.1 point) (third.1 point)

private theorem canonicalPhysicalScalarC2JetCoreProductValue_smul_right
    (scalar : Real)
    (first second : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    canonicalPhysicalScalarC2JetCoreProductValue period hPeriod
        first (scalar • second) =
      scalar • canonicalPhysicalScalarC2JetCoreProductValue
        period hPeriod first second := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  exact scalarFrameJet2Mul_smul_right
    scalar (first.1 point) (second.1 point)

private def canonicalPhysicalScalarC2JetCoreProductLinearMap :
    CanonicalPhysicalScalarC2JetCore period hPeriod →ₗ[Real]
      CanonicalPhysicalScalarC2JetCore period hPeriod →ₗ[Real]
        CanonicalPhysicalScalarC2JetCore period hPeriod :=
  LinearMap.mk₂ Real
    (canonicalPhysicalScalarC2JetCoreProductValue period hPeriod)
    (canonicalPhysicalScalarC2JetCoreProductValue_add_left period hPeriod)
    (canonicalPhysicalScalarC2JetCoreProductValue_smul_left period hPeriod)
    (canonicalPhysicalScalarC2JetCoreProductValue_add_right period hPeriod)
    (canonicalPhysicalScalarC2JetCoreProductValue_smul_right period hPeriod)

/-- Multiplication restricted to the complete closed second-jet core. -/
def canonicalPhysicalScalarC2JetCoreProduct :
    CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
      CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
        CanonicalPhysicalScalarC2JetCore period hPeriod := by
  exact @LinearMap.mkContinuous₂ Real Real Real
    (CanonicalPhysicalScalarC2JetCore period hPeriod)
    (CanonicalPhysicalScalarC2JetCore period hPeriod)
    (CanonicalPhysicalScalarC2JetCore period hPeriod)
    _ _ _ _ _ _ _ _ _
    (RingHom.id Real) (RingHom.id Real) _
    (canonicalPhysicalScalarC2JetCoreProductLinearMap period hPeriod) 4
      (canonicalPhysicalScalarC2JetCoreProductValue_norm_le period hPeriod)

theorem canonicalPhysicalScalarC2JetCoreProduct_norm_le
    (first second : CanonicalPhysicalScalarC2JetCore period hPeriod) :
    ‖canonicalPhysicalScalarC2JetCoreProduct
        period hPeriod first second‖ ≤
      4 * ‖first‖ * ‖second‖ :=
  canonicalPhysicalScalarC2JetCoreProductValue_norm_le
    period hPeriod first second

@[simp]
theorem canonicalPhysicalScalarC2JetCoreProduct_smooth
    (first second : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod first)
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod second) =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothScalarFieldMul period hPeriod first second) := by
  simp only [canonicalPhysicalScalarC2JetCoreProduct,
    LinearMap.mkContinuous₂_apply]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  change scalarFrameJet2Mul
      (smoothScalarFrameJet2 period hPeriod
        (physicalFrame period hPeriod) first point)
      (smoothScalarFrameJet2 period hPeriod
        (physicalFrame period hPeriod) second point) =
    smoothScalarFrameJet2 period hPeriod
      (physicalFrame period hPeriod)
      (smoothScalarFieldMul period hPeriod first second) point
  exact (congrFun
    (smoothScalarFrameJet2_mul period hPeriod
      (physicalFrame period hPeriod) first second) point).symm

theorem canonicalPhysicalScalarC2JetCoreProduct_contDiff :
    ContDiff Real ∞
      (fun input : CanonicalPhysicalScalarC2JetCore period hPeriod ×
          CanonicalPhysicalScalarC2JetCore period hPeriod =>
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          input.1 input.2) :=
  by
    let product :
        CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
          CanonicalPhysicalScalarC2JetCore period hPeriod →L[Real]
            CanonicalPhysicalScalarC2JetCore period hPeriod :=
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    exact ((ContinuousLinearMap.isBoundedBilinearMap
      (𝕜 := Real)
      (E := CanonicalPhysicalScalarC2JetCore period hPeriod)
      (F := CanonicalPhysicalScalarC2JetCore period hPeriod)
      (G := CanonicalPhysicalScalarC2JetCore period hPeriod)
      product) :
      IsBoundedBilinearMap Real
        (fun input : CanonicalPhysicalScalarC2JetCore period hPeriod ×
            CanonicalPhysicalScalarC2JetCore period hPeriod =>
          product input.1 input.2)).contDiff

/-- Summary: an actual complete uniform second-jet core with dense exact
smooth fields and bounded `C∞` Leibniz multiplication. -/
theorem canonical_physical_scalar_c2_jet_core_gate :
    IsClosed
        (CanonicalPhysicalScalarC2JetCore period hPeriod :
          Set (CanonicalPhysicalScalarC2JetAmbient period hPeriod)) ∧
      DenseRange
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) ∧
      ContDiff Real ∞
        (fun input : CanonicalPhysicalScalarC2JetCore period hPeriod ×
            CanonicalPhysicalScalarC2JetCore period hPeriod =>
          canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            input.1 input.2) ∧
      (∀ first second : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
            (smoothToCanonicalPhysicalScalarC2JetCore
              period hPeriod first)
            (smoothToCanonicalPhysicalScalarC2JetCore
              period hPeriod second) =
          smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (smoothScalarFieldMul period hPeriod first second)) := by
  exact ⟨canonicalPhysicalScalarC2JetCore_isClosed period hPeriod,
    smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod,
    canonicalPhysicalScalarC2JetCoreProduct_contDiff period hPeriod,
    canonicalPhysicalScalarC2JetCoreProduct_smooth period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
end JanusFormal
