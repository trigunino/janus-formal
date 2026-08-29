import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

/-!
# Faithful C² core for general metric variations

The existing finite smooth spanning family reads every genuine smooth
symmetric two-tensor into a finite matrix of scalar fields.  Lifting each
entry to the canonical scalar C² core is injective.  The closure of this true
smooth range is therefore a complete C² metric-variation domain; it does not
replace the Lorentz metrics by a special ansatz or assume a global frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricC2VariationCore4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

theorem generalMetricFrameCoefficient_add
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) :
    generalMetricFrameCoefficient period hPeriod frame (first + second)
        row column =
      generalMetricFrameCoefficient period hPeriod frame first row column +
        generalMetricFrameCoefficient period hPeriod frame second row column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

theorem generalMetricFrameCoefficient_smul
    (frame : SmoothD8Frame period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) :
    generalMetricFrameCoefficient period hPeriod frame (scalar • tensor)
        row column =
      scalar • generalMetricFrameCoefficient
        period hPeriod frame tensor row column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

theorem generalMetricFrameCoefficient_sub
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) :
    generalMetricFrameCoefficient period hPeriod frame (first - second)
        row column =
      generalMetricFrameCoefficient period hPeriod frame first row column -
        generalMetricFrameCoefficient period hPeriod frame second row column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- Exact finite C² coefficient matrix of a genuine smooth metric
variation. -/
def smoothGeneralMetricTensorToC2Matrix
    (frame : SmoothD8Frame period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      C2FiniteMatrix period hPeriod frame.count where
  toFun tensor row column :=
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (generalMetricFrameCoefficient
        period hPeriod frame tensor row column)
  map_add' first second := by
    funext row column
    rw [generalMetricFrameCoefficient_add,
      map_add]
    rfl
  map_smul' scalar tensor := by
    funext row column
    rw [generalMetricFrameCoefficient_smul,
      map_smul]
    rfl

@[simp]
theorem smoothGeneralMetricTensorToC2Matrix_apply
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) :
    smoothGeneralMetricTensorToC2Matrix period hPeriod frame tensor row column =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (generalMetricFrameCoefficient
          period hPeriod frame tensor row column) :=
  rfl

theorem smoothGeneralMetricTensorToC2Matrix_injective
    (frame : SmoothD8Frame period hPeriod) :
    Function.Injective
      (smoothGeneralMetricTensorToC2Matrix period hPeriod frame) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  apply generalMetricFrameEnergy_pointwiseSeparates period hPeriod frame
  intro point
  unfold generalMetricFrameEnergy
  apply Finset.sum_eq_zero
  intro row _
  apply Finset.sum_eq_zero
  intro column _
  have hEntry :
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (generalMetricFrameCoefficient
            period hPeriod frame first row column) =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (generalMetricFrameCoefficient
            period hPeriod frame second row column) :=
    congrFun (congrFun hEqual row) column
  have hCoefficient :=
    smoothToCanonicalPhysicalScalarC2JetCore_injective
      period hPeriod hEntry
  have hPoint := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point)
    hCoefficient
  have hReading :
      first.tensor point (frame.vectorAt point row)
          (frame.vectorAt point column) =
        second.tensor point (frame.vectorAt point row)
          (frame.vectorAt point column) := by
    simpa only [generalMetricFrameCoefficient_apply] using hPoint
  have hSubCoefficient :
      generalMetricFrameCoefficient period hPeriod frame (first - second)
          row column point = 0 := by
    rw [generalMetricFrameCoefficient_sub]
    change first.tensor point (frame.vectorAt point row)
        (frame.vectorAt point column) -
      second.tensor point (frame.vectorAt point row)
        (frame.vectorAt point column) = 0
    rw [hReading]
    ring
  change (generalMetricFrameCoefficient
      period hPeriod frame (first - second) row column point) ^ 2 = 0
  rw [hSubCoefficient]
  norm_num

/-- Closed true-smooth range defining the general metric C² tangent core. -/
def generalMetricC2VariationCoreSubmodule
    (frame : SmoothD8Frame period hPeriod) :
    Submodule Real (C2FiniteMatrix period hPeriod frame.count) :=
  (LinearMap.range
    (smoothGeneralMetricTensorToC2Matrix
      period hPeriod frame)).topologicalClosure

/-- Complete C² domain of general metric variations. -/
abbrev GeneralMetricC2VariationCore
    (frame : SmoothD8Frame period hPeriod) :=
  generalMetricC2VariationCoreSubmodule period hPeriod frame

theorem generalMetricC2VariationCore_isClosed
    (frame : SmoothD8Frame period hPeriod) :
    IsClosed
      (GeneralMetricC2VariationCore period hPeriod frame :
        Set (C2FiniteMatrix period hPeriod frame.count)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def generalMetricC2VariationCoreCompleteSpace
    (frame : SmoothD8Frame period hPeriod) :
    CompleteSpace (GeneralMetricC2VariationCore period hPeriod frame) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (smoothGeneralMetricTensorToC2Matrix period hPeriod frame))

/-- Dense faithful inclusion of genuine smooth symmetric variations. -/
def smoothToGeneralMetricC2VariationCore
    (frame : SmoothD8Frame period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GeneralMetricC2VariationCore period hPeriod frame where
  toFun tensor :=
    ⟨smoothGeneralMetricTensorToC2Matrix period hPeriod frame tensor,
      (LinearMap.range
        (smoothGeneralMetricTensorToC2Matrix
          period hPeriod frame)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothGeneralMetricTensorToC2Matrix period hPeriod frame) tensor)⟩
  map_add' first second := Subtype.ext
    ((smoothGeneralMetricTensorToC2Matrix
      period hPeriod frame).map_add first second)
  map_smul' scalar tensor := Subtype.ext
    ((smoothGeneralMetricTensorToC2Matrix
      period hPeriod frame).map_smul scalar tensor)

theorem smoothToGeneralMetricC2VariationCore_denseRange
    (frame : SmoothD8Frame period hPeriod) :
    DenseRange
      (smoothToGeneralMetricC2VariationCore period hPeriod frame) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion :=
    smoothGeneralMetricTensorToC2Matrix period hPeriod frame
  have hRange :
      Subtype.val '' Set.range
          (smoothToGeneralMetricC2VariationCore period hPeriod frame) =
        (LinearMap.range inclusion :
          Set (C2FiniteMatrix period hPeriod frame.count)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨tensor, rfl⟩, rfl⟩
      exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact ⟨smoothToGeneralMetricC2VariationCore
          period hPeriod frame tensor, ⟨tensor, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion :
      Set (C2FiniteMatrix period hPeriod frame.count)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToGeneralMetricC2VariationCore period hPeriod frame))
  rw [hRange]

theorem smoothToGeneralMetricC2VariationCore_injective
    (frame : SmoothD8Frame period hPeriod) :
    Function.Injective
      (smoothToGeneralMetricC2VariationCore period hPeriod frame) := by
  intro first second hEqual
  apply smoothGeneralMetricTensorToC2Matrix_injective
    period hPeriod frame
  exact congrArg Subtype.val hEqual

/-- Continuous inclusion into the ambient finite C² coefficient matrix. -/
def generalMetricC2VariationCoreToMatrix
    (frame : SmoothD8Frame period hPeriod) :
    GeneralMetricC2VariationCore period hPeriod frame →L[Real]
      C2FiniteMatrix period hPeriod frame.count :=
  (generalMetricC2VariationCoreSubmodule period hPeriod frame).subtypeL

/-- Summary gate for the genuine general-metric C² variation domain. -/
theorem general_metric_c2_variation_core_gate
    (frame : SmoothD8Frame period hPeriod) :
    Function.Injective
        (smoothToGeneralMetricC2VariationCore period hPeriod frame) ∧
      DenseRange
        (smoothToGeneralMetricC2VariationCore period hPeriod frame) ∧
      IsClosed
        (GeneralMetricC2VariationCore period hPeriod frame :
          Set (C2FiniteMatrix period hPeriod frame.count)) := by
  exact ⟨smoothToGeneralMetricC2VariationCore_injective
      period hPeriod frame,
    smoothToGeneralMetricC2VariationCore_denseRange period hPeriod frame,
    generalMetricC2VariationCore_isClosed period hPeriod frame⟩

end

end P0EFTJanusProgramPGeneralMetricC2VariationCore4D
end JanusFormal
