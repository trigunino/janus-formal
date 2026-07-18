import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D

/-!
# Conditional comparison of the static scalar energy completion with graph H¹

The scalar energy completion and the existing first-jet graph completion do
not have the same declared smooth core: the former contains only fields with
zero holonomic time derivative, while the latter contains every smooth scalar
field and uses an arbitrary finite smooth tangent frame.

This gate therefore does not identify either space with a new Sobolev space.
It takes the closure of the actual static smooth image inside the existing H¹
graph space and proves that a continuous bridge from the energy completion
exists exactly when the corresponding smooth norm estimate is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1GraphBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The already constructed first-jet graph space, specialized to the scalar
measure carried by the positive static data. -/
abbrev StaticScalarH1Graph
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :=
  let _ : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  H1GraphSpace period hPeriod Real frame data.formData.measure

/-- The full smooth scalar core map into graph H¹, with the measure instance
carried explicitly by the static data. -/
def allScalarSmoothToH1GraphLinearMap
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      StaticScalarH1Graph period hPeriod data frame := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  exact smoothToH1GraphLinearMap period hPeriod Real frame data.formData.measure

/-- The algebraic inclusion of the static smooth core into the genuine H¹
first-jet graph space.  No continuity is asserted here. -/
def staticScalarSmoothToH1GraphLinearMap
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    StaticGlobalScalarTest period hPeriod data →ₗ[Real]
      StaticScalarH1Graph period hPeriod data frame := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  exact
    { toFun := fun field =>
        smoothToH1GraphLinearMap period hPeriod Real frame
          data.formData.measure field.toField
      map_add' := fun first second =>
        (smoothToH1GraphLinearMap period hPeriod Real frame
          data.formData.measure).map_add first.toField second.toField
      map_smul' := fun scalar field =>
        (smoothToH1GraphLinearMap period hPeriod Real frame
          data.formData.measure).map_smul scalar field.toField }

/-- Closure of the actual static smooth core inside the existing graph H¹.
This is a closed subspace, not a replacement definition of Sobolev H¹. -/
def staticScalarH1GraphSubmodule
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    Submodule Real (StaticScalarH1Graph period hPeriod data frame) :=
  (LinearMap.range
    (staticScalarSmoothToH1GraphLinearMap period hPeriod data frame)).topologicalClosure

/-- The static closure within the pre-existing graph H¹ space. -/
abbrev StaticScalarH1GraphClosure
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :=
  staticScalarH1GraphSubmodule period hPeriod data frame

/-- Canonical map of the static smooth core into its graph closure. -/
def staticScalarSmoothToH1GraphClosureLinearMap
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    StaticGlobalScalarTest period hPeriod data →ₗ[Real]
      StaticScalarH1GraphClosure period hPeriod data frame where
  toFun field :=
    ⟨staticScalarSmoothToH1GraphLinearMap period hPeriod data frame field,
      (LinearMap.range
        (staticScalarSmoothToH1GraphLinearMap period hPeriod data frame)).le_topologicalClosure
        (LinearMap.mem_range_self
          (staticScalarSmoothToH1GraphLinearMap period hPeriod data frame) field)⟩
  map_add' first second := Subtype.ext
    ((staticScalarSmoothToH1GraphLinearMap period hPeriod data frame).map_add
      first second)
  map_smul' scalar field := Subtype.ext
    ((staticScalarSmoothToH1GraphLinearMap period hPeriod data frame).map_smul
      scalar field)

/-- The static smooth image is dense in its graph closure by construction. -/
theorem staticScalarSmoothToH1GraphClosure_denseRange
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    DenseRange
      (staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := staticScalarSmoothToH1GraphLinearMap period hPeriod data frame
  have hRange :
      Subtype.val '' Set.range
          (staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame) =
        (LinearMap.range inclusion : Set
          (StaticScalarH1Graph period hPeriod data frame)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨field, rfl⟩, rfl⟩
      exact ⟨field, rfl⟩
    · rintro ⟨field, rfl⟩
      exact
        ⟨staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame field,
          ⟨field, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion : Set
      (StaticScalarH1Graph period hPeriod data frame)) ⊆
    closure (Subtype.val '' Set.range
      (staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame))
  rw [hRange]

/-- Completeness inherited from the two nested closed subspaces. -/
@[implicit_reducible]
def staticScalarH1GraphClosureCompleteSpace
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    CompleteSpace (StaticScalarH1GraphClosure period hPeriod data frame) := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  letI : CompleteSpace (StaticScalarH1Graph period hPeriod data frame) :=
    h1GraphCompleteSpace period hPeriod Real frame data.formData.measure
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (staticScalarSmoothToH1GraphLinearMap period hPeriod data frame))

/-- Exact analytic obligation for the energy-to-graph bridge.  It compares
the two norms on their common static smooth core. -/
def StaticScalarEnergyToH1GraphBound
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) : Prop :=
  ∃ constant : Real, ∀ field : StaticGlobalScalarTest period hPeriod data,
    ‖staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame field‖ ≤
      constant * ‖staticScalarEnergyEmbedding period hPeriod data field‖

/-- A continuous bridge exists precisely when the smooth comparison estimate
has been proved. -/
def StaticScalarEnergyH1GraphBridgeExists
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) : Prop :=
  ∃ bridge : StaticScalarEnergyH1 period hPeriod data →L[Real]
      StaticScalarH1GraphClosure period hPeriod data frame,
    ∀ field : StaticGlobalScalarTest period hPeriod data,
      bridge (staticScalarEnergyEmbedding period hPeriod data field) =
        staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame field

/-- Conditional extension of the common static smooth core. -/
def staticScalarEnergyToH1GraphClosure
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (_hBound : StaticScalarEnergyToH1GraphBound period hPeriod data frame) :
    StaticScalarEnergyH1 period hPeriod data →L[Real]
      StaticScalarH1GraphClosure period hPeriod data frame := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  letI : CompleteSpace (StaticScalarH1Graph period hPeriod data frame) :=
    h1GraphCompleteSpace period hPeriod Real frame data.formData.measure
  letI : CompleteSpace (StaticScalarH1GraphClosure period hPeriod data frame) :=
    staticScalarH1GraphClosureCompleteSpace period hPeriod data frame
  exact
    (staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame).extendOfNorm
      (staticScalarEnergyEmbedding period hPeriod data).toLinearMap

theorem staticScalarEnergyToH1GraphClosure_agrees_on_smooth
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hBound : StaticScalarEnergyToH1GraphBound period hPeriod data frame)
    (field : StaticGlobalScalarTest period hPeriod data) :
    staticScalarEnergyToH1GraphClosure period hPeriod data frame hBound
        (staticScalarEnergyEmbedding period hPeriod data field) =
      staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame field := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  letI : CompleteSpace (StaticScalarH1Graph period hPeriod data frame) :=
    h1GraphCompleteSpace period hPeriod Real frame data.formData.measure
  letI : CompleteSpace (StaticScalarH1GraphClosure period hPeriod data frame) :=
    staticScalarH1GraphClosureCompleteSpace period hPeriod data frame
  apply LinearMap.extendOfNorm_eq
  · exact staticScalarEnergyEmbedding_denseRange period hPeriod data
  · exact hBound

theorem staticScalarEnergyH1GraphBridgeExists_iff
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    StaticScalarEnergyH1GraphBridgeExists period hPeriod data frame ↔
      StaticScalarEnergyToH1GraphBound period hPeriod data frame := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  letI : NormedSpace Real (StaticScalarH1Graph period hPeriod data frame) :=
    Submodule.normedSpace _
  letI : NormedSpace Real
      (StaticScalarH1GraphClosure period hPeriod data frame) :=
    Submodule.normedSpace _
  constructor
  · rintro ⟨bridge, hBridge⟩
    refine ⟨‖bridge‖, ?_⟩
    intro field
    rw [← hBridge field]
    exact @ContinuousLinearMap.le_opNorm
      Real Real
      (StaticScalarEnergyH1 period hPeriod data)
      (StaticScalarH1GraphClosure period hPeriod data frame)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (Submodule.normedSpace _) (RingHom.id Real) inferInstance bridge _
  · intro hBound
    exact
      ⟨staticScalarEnergyToH1GraphClosure period hPeriod data frame hBound,
        staticScalarEnergyToH1GraphClosure_agrees_on_smooth period hPeriod data frame
          hBound⟩

/-- The static graph closure is the entire pre-existing graph H¹ exactly if
static smooth fields are dense there.  This is the separate density obligation
needed before any identification with the full graph space. -/
theorem staticScalarH1GraphSubmodule_eq_top_iff
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    staticScalarH1GraphSubmodule period hPeriod data frame = ⊤ ↔
      DenseRange
        (staticScalarSmoothToH1GraphLinearMap period hPeriod data frame) := by
  change
    (LinearMap.range
      (staticScalarSmoothToH1GraphLinearMap period hPeriod data frame)).topologicalClosure =
        ⊤ ↔ _
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  rfl

/-- The full graph H¹ is generated densely by all smooth scalar fields.  In
contrast, every element of the energy smooth core carries the time-static
constraint.  Equality of the static closure with the full graph therefore
requires an additional static-density theorem, not present in the definitions. -/
theorem declared_smooth_core_constraints
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    (∀ field : StaticGlobalScalarTest period hPeriod data, ∀ point,
      holonomicCovectorComponent period hPeriod field.toField point 0 = 0) ∧
    DenseRange
      (allScalarSmoothToH1GraphLinearMap period hPeriod data frame) := by
  constructor
  · exact fun field point => field.time_static point
  · letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
    exact smoothToH1Graph_denseRange period hPeriod Real frame data.formData.measure

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1GraphBridge4D
end JanusFormal
