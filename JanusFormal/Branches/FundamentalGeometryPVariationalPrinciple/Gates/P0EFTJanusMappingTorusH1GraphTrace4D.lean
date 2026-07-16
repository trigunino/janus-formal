import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusL2PTFunctionalSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# First-order Sobolev graph completion and conditional throat trace

On the actual compact four-dimensional D8 quotient, a finite smooth spanning
family turns the manifold derivative into global directional derivatives.
Their joint `L2` graph has a genuine Banach completion.  A quantitative trace
bound on smooth fields then extends uniquely to a continuous trace on that
completion.  The bound (the missing analytic trace theorem) remains an explicit
hypothesis; no intrinsic manifold Sobolev library is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphTrace4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel (EffectiveQuotient period hPeriod)

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel (EffectiveThroat period hPeriod)

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- An explicit finite smooth tangent generating family on the real quotient.
Unlike a basis-valued global frame, such a family is compatible with a
nontrivial tangent bundle.  Its construction is the remaining geometric input
to identify the graph completion with an intrinsic first-order Sobolev space. -/
structure SmoothD8Frame where
  count : Nat
  vectorAt : ∀ point : EffectiveQuotient period hPeriod,
    Fin count → TangentSpace coverModelWithCorners point
  spansAt : ∀ point : EffectiveQuotient period hPeriod,
    Submodule.span Real (Set.range (vectorAt point)) = ⊤
  contMDiff_vector : ∀ index : Fin count,
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ω
      (fun point =>
        (⟨point, vectorAt point index⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod)))

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Genuine manifold directional derivatives along the spanning family. -/
def frameDerivative
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) : Fin frame.count → Fiber :=
  fun index =>
    NormedSpace.fromTangentSpace (field point)
      ((tangentMap coverModelWithCorners 𝓘(Real, Fiber) field.toFun
        (⟨point, frame.vectorAt point index⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod))).2)

theorem frameDerivative_eq_mfderiv
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) (index : Fin frame.count) :
    frameDerivative period hPeriod Fiber frame field point index =
      mvfderiv coverModelWithCorners field.toFun point
        (frame.vectorAt point index) :=
  rfl

theorem frameDerivative_contMDiff
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber) :
    ContMDiff coverModelWithCorners 𝓘(Real, Fin frame.count → Fiber) ω
      (frameDerivative period hPeriod Fiber frame field) := by
  rw [contMDiff_pi_space]
  intro index
  have hDerivative :=
    (contMDiff_snd_tangentBundle_modelSpace Fiber 𝓘(Real, Fiber)).comp
      ((field.contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
        (frame.contMDiff_vector index))
  convert hDerivative using 1
  rfl

theorem frameDerivative_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Fiber) :
    frameDerivative period hPeriod Fiber frame (first + second) =
      frameDerivative period hPeriod Fiber frame first +
        frameDerivative period hPeriod Fiber frame second := by
  funext point index
  simp only [Pi.add_apply]
  rw [frameDerivative_eq_mfderiv, frameDerivative_eq_mfderiv,
    frameDerivative_eq_mfderiv]
  change
    mvfderiv coverModelWithCorners (first.toFun + second.toFun) point
        (frame.vectorAt point index) = _
  rw [mvfderiv_add
    ((first.contMDiff_toFun.mdifferentiable (by simp)) point)
    ((second.contMDiff_toFun.mdifferentiable (by simp)) point)]
  rfl

theorem frameDerivative_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real) (field : SmoothQuotientField period hPeriod Fiber) :
    frameDerivative period hPeriod Fiber frame (scalar • field) =
      scalar • frameDerivative period hPeriod Fiber frame field := by
  funext point index
  simp only [Pi.smul_apply]
  rw [frameDerivative_eq_mfderiv, frameDerivative_eq_mfderiv]
  change
    mvfderiv coverModelWithCorners (scalar • field.toFun) point
        (frame.vectorAt point index) = _
  unfold mvfderiv
  rw [const_smul_mfderiv
    ((field.contMDiff_toFun.mdifferentiable (by simp)) point) scalar]
  rfl

/-- The value and all spanning first derivatives, on the same global field. -/
def smoothFirstJet
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    Fiber × (Fin frame.count → Fiber) :=
  (field point, frameDerivative period hPeriod Fiber frame field point)

theorem smoothFirstJet_contMDiff
    (frame : SmoothD8Frame period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber) :
    ContMDiff coverModelWithCorners
      𝓘(Real, Fiber × (Fin frame.count → Fiber)) ω
      (smoothFirstJet period hPeriod Fiber frame field) :=
  field.contMDiff_toFun.prodMk_space
    (frameDerivative_contMDiff period hPeriod Fiber frame field)

theorem smoothFirstJet_memLp
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    MemLp (smoothFirstJet period hPeriod Fiber frame field) (2 : ENNReal) mu := by
  have hContinuous : Continuous
      (smoothFirstJet period hPeriod Fiber frame field) :=
    (smoothFirstJet_contMDiff period hPeriod Fiber frame field).continuous
  exact Continuous.memLp_of_hasCompactSupport hContinuous
    (HasCompactSupport.of_compactSpace
      (smoothFirstJet period hPeriod Fiber frame field))

/-- Smooth first jets as elements of the completed ambient `L2` space. -/
def smoothFirstJetToL2
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu :=
  (smoothFirstJet_memLp period hPeriod Fiber frame mu field).toLp
    (smoothFirstJet period hPeriod Fiber frame field)

theorem smoothFirstJet_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Fiber) :
    smoothFirstJet period hPeriod Fiber frame (first + second) =
      smoothFirstJet period hPeriod Fiber frame first +
        smoothFirstJet period hPeriod Fiber frame second := by
  funext point
  apply Prod.ext
  · rfl
  · exact congrFun (frameDerivative_add period hPeriod Fiber frame first second) point

theorem smoothFirstJet_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real) (field : SmoothQuotientField period hPeriod Fiber) :
    smoothFirstJet period hPeriod Fiber frame (scalar • field) =
      scalar • smoothFirstJet period hPeriod Fiber frame field := by
  funext point
  apply Prod.ext
  · rfl
  · exact congrFun (frameDerivative_smul period hPeriod Fiber frame scalar field) point

/-- The smooth first-jet graph map is exactly linear. -/
def smoothFirstJetL2LinearMap
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    SmoothQuotientField period hPeriod Fiber →ₗ[Real]
      Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu where
  toFun := smoothFirstJetToL2 period hPeriod Fiber frame mu
  map_add' first second := by
    apply Lp.ext
    have hSum :
        (smoothFirstJetToL2 period hPeriod Fiber frame mu (first + second) :
          EffectiveQuotient period hPeriod →
            Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
        smoothFirstJet period hPeriod Fiber frame (first + second) := by
      simpa only [smoothFirstJetToL2] using
        (smoothFirstJet_memLp period hPeriod Fiber frame mu
          (first + second)).coeFn_toLp
    have hFirst :
        (smoothFirstJetToL2 period hPeriod Fiber frame mu first :
          EffectiveQuotient period hPeriod →
            Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
        smoothFirstJet period hPeriod Fiber frame first := by
      simpa only [smoothFirstJetToL2] using
        (smoothFirstJet_memLp period hPeriod Fiber frame mu first).coeFn_toLp
    have hSecond :
        (smoothFirstJetToL2 period hPeriod Fiber frame mu second :
          EffectiveQuotient period hPeriod →
            Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
        smoothFirstJet period hPeriod Fiber frame second := by
      simpa only [smoothFirstJetToL2] using
        (smoothFirstJet_memLp period hPeriod Fiber frame mu second).coeFn_toLp
    filter_upwards
      [hSum, hFirst, hSecond,
       Lp.coeFn_add
         (smoothFirstJetToL2 period hPeriod Fiber frame mu first)
         (smoothFirstJetToL2 period hPeriod Fiber frame mu second)]
      with point hSum hFirst hSecond hAdd
    rw [hSum, hAdd]
    simp only [Pi.add_apply]
    rw [hFirst, hSecond,
      congrFun (smoothFirstJet_add period hPeriod Fiber frame first second) point]
    rfl
  map_smul' scalar field := by
    change smoothFirstJetToL2 period hPeriod Fiber frame mu (scalar • field) =
      scalar • smoothFirstJetToL2 period hPeriod Fiber frame mu field
    apply Lp.ext
    have hScaled :
        (smoothFirstJetToL2 period hPeriod Fiber frame mu (scalar • field) :
          EffectiveQuotient period hPeriod →
            Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
        smoothFirstJet period hPeriod Fiber frame (scalar • field) := by
      simpa only [smoothFirstJetToL2] using
        (smoothFirstJet_memLp period hPeriod Fiber frame mu
          (scalar • field)).coeFn_toLp
    have hField :
        (smoothFirstJetToL2 period hPeriod Fiber frame mu field :
          EffectiveQuotient period hPeriod →
            Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
        smoothFirstJet period hPeriod Fiber frame field := by
      simpa only [smoothFirstJetToL2] using
        (smoothFirstJet_memLp period hPeriod Fiber frame mu field).coeFn_toLp
    filter_upwards
      [hScaled, hField,
       Lp.coeFn_smul scalar
         (smoothFirstJetToL2 period hPeriod Fiber frame mu field)]
      with point hScaled hField hSmul
    rw [hScaled, hSmul]
    simp only [Pi.smul_apply]
    rw [hField,
      congrFun (smoothFirstJet_smul period hPeriod Fiber frame scalar field) point]
    rfl

/-- Closed first-jet graph: the `H¹` graph completion of smooth fields. -/
def h1GraphSubmodule
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    Submodule Real
      (Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu) :=
  (LinearMap.range
    (smoothFirstJetL2LinearMap period hPeriod Fiber frame mu)).topologicalClosure

/-- The genuine Banach graph completion on the compact D8 quotient. -/
abbrev H1GraphSpace
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  h1GraphSubmodule period hPeriod Fiber frame mu

/-- Canonical inclusion of smooth fields into their first-jet completion. -/
def smoothToH1GraphLinearMap
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    SmoothQuotientField period hPeriod Fiber →ₗ[Real]
      H1GraphSpace period hPeriod Fiber frame mu where
  toFun field :=
    ⟨smoothFirstJetL2LinearMap period hPeriod Fiber frame mu field,
      (LinearMap.range
        (smoothFirstJetL2LinearMap period hPeriod Fiber frame mu)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothFirstJetL2LinearMap period hPeriod Fiber frame mu) field)⟩
  map_add' first second := Subtype.ext
    ((smoothFirstJetL2LinearMap period hPeriod Fiber frame mu).map_add first second)
  map_smul' scalar field := Subtype.ext
    ((smoothFirstJetL2LinearMap period hPeriod Fiber frame mu).map_smul scalar field)

theorem smoothToH1Graph_denseRange
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    DenseRange (smoothToH1GraphLinearMap period hPeriod Fiber frame mu) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let jet := smoothFirstJetL2LinearMap period hPeriod Fiber frame mu
  have hRange :
      Subtype.val '' Set.range
          (smoothToH1GraphLinearMap period hPeriod Fiber frame mu) =
        (LinearMap.range jet : Set
          (Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨field, rfl⟩, rfl⟩
      exact ⟨field, rfl⟩
    · rintro ⟨field, rfl⟩
      exact ⟨smoothToH1GraphLinearMap period hPeriod Fiber frame mu field,
        ⟨field, rfl⟩, rfl⟩
  change closure (LinearMap.range jet : Set
      (Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToH1GraphLinearMap period hPeriod Fiber frame mu))
  rw [hRange]

/-- Forgetting the derivative coordinates gives the canonical continuous
embedding of the graph completion into spacetime `L2`. -/
def h1GraphToL2
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    H1GraphSpace period hPeriod Fiber frame mu →L[Real]
      Lp Fiber (2 : ENNReal) mu :=
  ((ContinuousLinearMap.fst Real Fiber (Fin frame.count → Fiber)).compLpL
      (2 : ENNReal) mu).comp
    (h1GraphSubmodule period hPeriod Fiber frame mu).subtypeL

theorem h1GraphToL2_agrees_on_smooth
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    h1GraphToL2 period hPeriod Fiber frame mu
        (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) =
      smoothFieldToL2 period hPeriod Fiber mu field := by
  apply Lp.ext
  have hProjection :=
    (ContinuousLinearMap.fst Real Fiber
      (Fin frame.count → Fiber)).coeFn_compLpL
      (p := (2 : ENNReal)) (μ := mu)
      (smoothFirstJetToL2 period hPeriod Fiber frame mu field)
  have hJet :
      (smoothFirstJetToL2 period hPeriod Fiber frame mu field :
        EffectiveQuotient period hPeriod →
          Fiber × (Fin frame.count → Fiber)) =ᵐ[mu]
      smoothFirstJet period hPeriod Fiber frame field := by
    simpa only [smoothFirstJetToL2] using
      (smoothFirstJet_memLp period hPeriod Fiber frame mu field).coeFn_toLp
  filter_upwards
    [hProjection, hJet,
      smoothFieldToL2_ae period hPeriod Fiber mu field]
    with point hProjection hJet hValue
  change
    (h1GraphToL2 period hPeriod Fiber frame mu
      (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) :
        EffectiveQuotient period hPeriod → Fiber) point = _
  rw [hValue]
  simpa [h1GraphToL2, smoothToH1GraphLinearMap,
    smoothFirstJetL2LinearMap, smoothFirstJet, hJet] using hProjection

/-- A full-support spacetime measure makes the smooth inclusion into the graph
completion injective. -/
theorem smoothToH1Graph_injective
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure] :
    Function.Injective
      (smoothToH1GraphLinearMap period hPeriod Fiber frame mu) := by
  intro first second hEqual
  apply smoothFieldToL2_injective period hPeriod Fiber mu
  rw [← h1GraphToL2_agrees_on_smooth period hPeriod Fiber frame mu first,
    ← h1GraphToL2_agrees_on_smooth period hPeriod Fiber frame mu second,
    hEqual]

variable [CompleteSpace Fiber]

/-- Completeness is inherited from the closed subspace of the ambient `L2`. -/
@[implicit_reducible]
def h1GraphCompleteSpace
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    CompleteSpace (H1GraphSpace period hPeriod Fiber frame mu) := by
  letI : CompleteSpace
      (Lp (Fiber × (Fin frame.count → Fiber)) (2 : ENNReal) mu) := inferInstance
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range (smoothFirstJetL2LinearMap period hPeriod Fiber frame mu))

omit [CompleteSpace Fiber] in
/-- Smooth throat fields are square integrable for every finite Borel measure. -/
theorem smoothThroatField_memLp
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : SmoothThroatField period hPeriod Fiber) :
    MemLp field.toFun (2 : ENNReal) nu :=
  field.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace field.toFun)

/-- Smooth restriction followed by the actual throat `L2` inclusion. -/
def smoothTraceToL2
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    Lp Fiber (2 : ENNReal) nu :=
  (smoothThroatField_memLp period hPeriod Fiber nu
    (throatTrace period hPeriod Fiber field)).toLp
      (throatTrace period hPeriod Fiber field).toFun

/-- The smooth throat trace is linear at the `L2` level. -/
def smoothTraceL2LinearMap
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu] :
    SmoothQuotientField period hPeriod Fiber →ₗ[Real]
      Lp Fiber (2 : ENNReal) nu where
  toFun := smoothTraceToL2 period hPeriod Fiber nu
  map_add' first second := by
    apply Lp.ext
    have hSum :
        (smoothTraceToL2 period hPeriod Fiber nu (first + second) :
          EffectiveThroat period hPeriod → Fiber) =ᵐ[nu]
        (throatTrace period hPeriod Fiber (first + second)).toFun := by
      simpa only [smoothTraceToL2] using
        (smoothThroatField_memLp period hPeriod Fiber nu
          (throatTrace period hPeriod Fiber (first + second))).coeFn_toLp
    have hFirst :
        (smoothTraceToL2 period hPeriod Fiber nu first :
          EffectiveThroat period hPeriod → Fiber) =ᵐ[nu]
        (throatTrace period hPeriod Fiber first).toFun := by
      simpa only [smoothTraceToL2] using
        (smoothThroatField_memLp period hPeriod Fiber nu
          (throatTrace period hPeriod Fiber first)).coeFn_toLp
    have hSecond :
        (smoothTraceToL2 period hPeriod Fiber nu second :
          EffectiveThroat period hPeriod → Fiber) =ᵐ[nu]
        (throatTrace period hPeriod Fiber second).toFun := by
      simpa only [smoothTraceToL2] using
        (smoothThroatField_memLp period hPeriod Fiber nu
          (throatTrace period hPeriod Fiber second)).coeFn_toLp
    filter_upwards
      [hSum, hFirst, hSecond,
       Lp.coeFn_add
         (smoothTraceToL2 period hPeriod Fiber nu first)
         (smoothTraceToL2 period hPeriod Fiber nu second)]
      with point hSum hFirst hSecond hAdd
    rw [hSum, hAdd]
    simp only [Pi.add_apply]
    rw [hFirst, hSecond]
    rfl
  map_smul' scalar field := by
    change smoothTraceToL2 period hPeriod Fiber nu (scalar • field) =
      scalar • smoothTraceToL2 period hPeriod Fiber nu field
    apply Lp.ext
    have hScaled :
        (smoothTraceToL2 period hPeriod Fiber nu (scalar • field) :
          EffectiveThroat period hPeriod → Fiber) =ᵐ[nu]
        (throatTrace period hPeriod Fiber (scalar • field)).toFun := by
      simpa only [smoothTraceToL2] using
        (smoothThroatField_memLp period hPeriod Fiber nu
          (throatTrace period hPeriod Fiber (scalar • field))).coeFn_toLp
    have hField :
        (smoothTraceToL2 period hPeriod Fiber nu field :
          EffectiveThroat period hPeriod → Fiber) =ᵐ[nu]
        (throatTrace period hPeriod Fiber field).toFun := by
      simpa only [smoothTraceToL2] using
        (smoothThroatField_memLp period hPeriod Fiber nu
          (throatTrace period hPeriod Fiber field)).coeFn_toLp
    filter_upwards
      [hScaled, hField,
       Lp.coeFn_smul scalar
         (smoothTraceToL2 period hPeriod Fiber nu field)]
      with point hScaled hField hSmul
    rw [hScaled, hSmul]
    simp only [Pi.smul_apply]
    rw [hField]
    rfl

/-- The exact analytic input missing from Mathlib: the smooth trace is bounded
by the first-jet graph norm. -/
structure HasH1TraceBound
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu] where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : SmoothQuotientField period hPeriod Fiber,
    ‖smoothTraceL2LinearMap period hPeriod Fiber nu field‖ ≤
      constant * ‖smoothToH1GraphLinearMap period hPeriod Fiber frame mu field‖

/-- The bounded smooth trace extends canonically to the completed `H¹` graph
space. -/
def h1Trace
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (_traceBound : HasH1TraceBound period hPeriod Fiber frame mu nu) :
    H1GraphSpace period hPeriod Fiber frame mu →L[Real]
      Lp Fiber (2 : ENNReal) nu :=
  (smoothTraceL2LinearMap period hPeriod Fiber nu).extendOfNorm
    (smoothToH1GraphLinearMap period hPeriod Fiber frame mu)

theorem h1Trace_agrees_on_smooth
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (traceBound : HasH1TraceBound period hPeriod Fiber frame mu nu)
    (field : SmoothQuotientField period hPeriod Fiber) :
    h1Trace period hPeriod Fiber frame mu nu traceBound
        (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) =
      smoothTraceL2LinearMap period hPeriod Fiber nu field :=
  LinearMap.extendOfNorm_eq
    (smoothToH1Graph_denseRange period hPeriod Fiber frame mu)
    ⟨traceBound.constant, traceBound.bound⟩ field

theorem h1Trace_norm_le
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (traceBound : HasH1TraceBound period hPeriod Fiber frame mu nu)
    (field : H1GraphSpace period hPeriod Fiber frame mu) :
    ‖h1Trace period hPeriod Fiber frame mu nu traceBound field‖ ≤
      traceBound.constant * ‖field‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    (smoothToH1Graph_denseRange period hPeriod Fiber frame mu)
    traceBound.constant traceBound.bound field

theorem h1Trace_unique
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (traceBound : HasH1TraceBound period hPeriod Fiber frame mu nu)
    (candidate : H1GraphSpace period hPeriod Fiber frame mu →L[Real]
      Lp Fiber (2 : ENNReal) nu)
    (hCandidate : ∀ field : SmoothQuotientField period hPeriod Fiber,
      candidate (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) =
        smoothTraceL2LinearMap period hPeriod Fiber nu field) :
    h1Trace period hPeriod Fiber frame mu nu traceBound = candidate := by
  apply LinearMap.extendOfNorm_unique
    (smoothToH1Graph_denseRange period hPeriod Fiber frame mu)
    traceBound.constant traceBound.bound
  apply LinearMap.ext
  intro field
  exact hCandidate field

end

end P0EFTJanusMappingTorusH1GraphTrace4D
end JanusFormal
