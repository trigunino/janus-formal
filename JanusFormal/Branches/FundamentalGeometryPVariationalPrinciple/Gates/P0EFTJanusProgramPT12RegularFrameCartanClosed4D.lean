import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Single-valued closed L² realization of the actual metric Cartan operator in regular-frame coefficients. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)

open Set
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

abbrev CartanGhostL2 := PiLp 2 fun _ : Fin 4 => CanonicalPhysicalBulkL2 period hPeriod
abbrev CartanTensorL2 := PiLp 2 fun _ : Fin 4 × Fin 4 => CanonicalPhysicalBulkL2 period hPeriod

def regularFrameGhostL2 : (Fin 4 → SmoothScalarField period hPeriod) →ₗ[Real]
    CartanGhostL2 period hPeriod where
  toFun coefficients := WithLp.toLp 2 fun direction => smoothToCanonicalPhysicalBulkL2 period hPeriod
    (coefficients direction)
  map_add' first second := by
    apply PiLp.ext
    intro direction
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_add _ _
  map_smul' scalar field := by
    apply PiLp.ext
    intro direction
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_smul scalar _

theorem regularFrameGhostL2_denseRange : DenseRange (regularFrameGhostL2 period hPeriod) := by
  let coordinateEquiv := PiLp.continuousLinearEquiv 2 Real
    (fun _ : Fin 4 => CanonicalPhysicalBulkL2 period hPeriod)
  have hPi : DenseRange (Pi.map fun _ : Fin 4 => smoothToCanonicalPhysicalBulkL2 period hPeriod) :=
    DenseRange.piMap fun _ => smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod
  exact coordinateEquiv.symm.surjective.denseRange.comp hPi coordinateEquiv.symm.continuous

def regularFrameCartanRow (first second : Fin 4) :
    (Fin 4 → SmoothScalarField period hPeriod) →ₗ[Real] SmoothScalarField period hPeriod :=
  ∑ direction : Fin 4,
    (regularFrameCartanColumn period hPeriod reference tensor first second direction).comp
      (LinearMap.proj direction)

def regularFrameCartanL2 : (Fin 4 → SmoothScalarField period hPeriod) →ₗ[Real]
    CartanTensorL2 period hPeriod where
  toFun coefficients := WithLp.toLp 2 fun row => smoothToCanonicalPhysicalBulkL2 period hPeriod
    (regularFrameCartanRow period hPeriod reference tensor row.1 row.2 coefficients)
  map_add' first second := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (regularFrameCartanRow period hPeriod reference tensor row.1 row.2)).map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (regularFrameCartanRow period hPeriod reference tensor row.1 row.2)).map_smul scalar field

theorem regularFrameCartanL2_actual
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) (first second : Fin 4) :
    regularFrameCartanL2 period hPeriod reference tensor coefficients (first, second) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (regularFrameSymmetricTensorCoefficient period hPeriod reference
          (smoothMetricCartanAction period hPeriod
            (regularFrameGhostFromCoefficients period hPeriod reference coefficients) tensor) first second) := by
  change smoothToCanonicalPhysicalBulkL2 period hPeriod
    (regularFrameCartanRow period hPeriod reference tensor first second coefficients) = _
  simp only [regularFrameCartanRow, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  exact congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
    (regularFrameCartan_eq_sum_columns period hPeriod reference tensor coefficients first second).symm

def regularFrameCartanGraph : Submodule Real
    (CartanGhostL2 period hPeriod × CartanTensorL2 period hPeriod) :=
  ((regularFrameGhostL2 period hPeriod).prod
    (regularFrameCartanL2 period hPeriod reference tensor)).range.topologicalClosure

theorem regularFrameCartanGraph_pairing
    (graph : regularFrameCartanGraph period hPeriod reference tensor)
    (first second : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (graph.val.2 (first, second)) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      ∑ direction : Fin 4, inner Real (graph.val.1 direction)
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (regularFrameCartanColumnAdjoint period hPeriod reference tensor first second direction test)) := by
  have hClosed : IsClosed {pair : CartanGhostL2 period hPeriod × CartanTensorL2 period hPeriod |
      inner Real (pair.2 (first, second)) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
        ∑ direction : Fin 4, inner Real (pair.1 direction)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod
            (regularFrameCartanColumnAdjoint period hPeriod reference tensor first second direction test))} := by
    apply isClosed_eq <;> fun_prop
  apply closure_minimal (s := (((regularFrameGhostL2 period hPeriod).prod
    (regularFrameCartanL2 period hPeriod reference tensor)).range : Set _)) ?_ hClosed graph.property
  rintro _ ⟨coefficients, rfl⟩
  change inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (regularFrameCartanRow period hPeriod reference tensor first second coefficients)) _ = _
  simp only [regularFrameCartanRow, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro direction _
  exact regularFrameCartanColumn_pairing period hPeriod reference tensor first second direction _ test

theorem regularFrameCartanGraph_input_injective :
    Function.Injective (fun graph : regularFrameCartanGraph period hPeriod reference tensor => graph.val.1) := by
  intro x y hInput
  apply Subtype.ext
  refine Prod.ext hInput ?_
  apply PiLp.ext
  rintro ⟨first, second⟩
  apply sub_eq_zero.mp
  apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  rw [inner_sub_left, regularFrameCartanGraph_pairing, regularFrameCartanGraph_pairing]
  apply sub_eq_zero.mpr
  exact congrArg (fun input : CartanGhostL2 period hPeriod =>
    ∑ direction : Fin 4, inner Real (input direction)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (regularFrameCartanColumnAdjoint period hPeriod reference tensor first second direction test))) hInput

/-- Minimal closed rectangular Cartan operator in the fixed regular-frame L² coefficients. -/
def regularFrameCartanMinimal : CartanGhostL2 period hPeriod →ₗ.[Real] CartanTensorL2 period hPeriod :=
  (regularFrameCartanGraph period hPeriod reference tensor).toLinearPMap

theorem regularFrameCartanMinimal_graph :
    (regularFrameCartanMinimal period hPeriod reference tensor).graph =
      regularFrameCartanGraph period hPeriod reference tensor := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun graph => graph.val.2)
    (regularFrameCartanGraph_input_injective period hPeriod reference tensor
      (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem regularFrameCartanMinimal_isClosed :
    (regularFrameCartanMinimal period hPeriod reference tensor).IsClosed := by
  rw [LinearPMap.IsClosed, regularFrameCartanMinimal_graph]
  exact ((regularFrameGhostL2 period hPeriod).prod
    (regularFrameCartanL2 period hPeriod reference tensor)).range.isClosed_topologicalClosure

theorem regularFrameCartanMinimal_smooth_mem (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameGhostL2 period hPeriod coefficients ∈
      (regularFrameCartanMinimal period hPeriod reference tensor).domain :=
  ⟨(regularFrameGhostL2 period hPeriod coefficients,
    regularFrameCartanL2 period hPeriod reference tensor coefficients),
    Submodule.le_topologicalClosure _ ⟨coefficients, rfl⟩, rfl⟩

theorem regularFrameCartanMinimal_smooth_apply (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    regularFrameCartanMinimal period hPeriod reference tensor
      ⟨regularFrameGhostL2 period hPeriod coefficients,
        regularFrameCartanMinimal_smooth_mem period hPeriod reference tensor coefficients⟩ =
      regularFrameCartanL2 period hPeriod reference tensor coefficients := by
  have hGraph := (regularFrameCartanMinimal period hPeriod reference tensor).mem_graph
    ⟨regularFrameGhostL2 period hPeriod coefficients,
      regularFrameCartanMinimal_smooth_mem period hPeriod reference tensor coefficients⟩
  rw [regularFrameCartanMinimal_graph] at hGraph
  exact congrArg (fun graph => graph.val.2)
    (regularFrameCartanGraph_input_injective period hPeriod reference tensor
      (a₁ := ⟨_, hGraph⟩)
      (a₂ := ⟨(regularFrameGhostL2 period hPeriod coefficients,
        regularFrameCartanL2 period hPeriod reference tensor coefficients),
        Submodule.le_topologicalClosure _ ⟨coefficients, rfl⟩⟩) rfl)

theorem regularFrameCartanMinimal_denseDomain :
    Dense ((regularFrameCartanMinimal period hPeriod reference tensor).domain :
      Set (CartanGhostL2 period hPeriod)) :=
  (regularFrameGhostL2_denseRange period hPeriod).mono
    (by rintro _ ⟨coefficients, rfl⟩; exact regularFrameCartanMinimal_smooth_mem period hPeriod reference tensor coefficients)

end
end JanusFormal.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
