import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessianLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTLLWorldvolumeHessianLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusThroatLinearOperationsZero4D

/-!
# Simultaneous weak LL Hessian and Jacobi operator

The actual simultaneous LL curves already vary the auxiliary metric, the LL
measure coefficient, and the LL flux.  This gate bundles their proved mixed
Hessian into a weak Jacobi operator, and identifies it with the actual second
directional derivative already present in the full LL variational API.

The generating frame has no curve-valued variation in the current API.
Accordingly, this gate stops at the exact three-slot operator with the frame
held fixed.  It does not claim a frame Hessian, a diagonal gauge generator, or
any on-shell/off-shell identity `J ∘ R = 0`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessianLinearity4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianLinearity4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTLLMeasureFieldTwoParameter4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusThroatLinearOperationsZero4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exactly the three LL slots carried by the existing simultaneous curve. -/
abbrev LLFullWeakTangent :=
  SmoothThroatField period hPeriod LLMetricFiber ×
    (SmoothThroatField period hPeriod Real ×
      SmoothThroatField period hPeriod LLFieldFiber)

abbrev LLFullWeakDual :=
  LLFullWeakTangent period hPeriod →ₗ[Real] Real

def llFullWeakVariation
    (direction : LLFullWeakTangent period hPeriod) :
    LLVariation period hPeriod where
  measureDirection := direction.2.1
  fieldDirection := direction.2.2

/-- Faithful embedding into the already proved full-LL variational packet;
all non-LL directions are set to zero. -/
def llFullWeakDirectionPacket
    (direction : LLFullWeakTangent period hPeriod) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := zeroSmoothDiagonalMetricVariation period hPeriod
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := direction.2.2 }
  robin := 0
  llAuxMetric := direction.1
  llMeasure := direction.2.1

/-- The genuine simultaneous affine curve of all currently typed LL slots. -/
def llFullWeakCurve
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod) (t : Real) :
    IndependentFields period hPeriod :=
  { fields with
    llAuxMetric := fields.llAuxMetric + t • direction.1
    llMeasure := fields.llMeasure + t • direction.2.1
    llField := fields.llField + t • direction.2.2 }

theorem llFullWeakCurve_eq_actual
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod) (t : Real) :
    llFullWeakCurve period hPeriod fields direction t =
      fullLLFieldCurve period hPeriod fields
        (llFullWeakDirectionPacket period hPeriod direction) t :=
  rfl

/-- Sum of the two already proved actual mixed Hessians. -/
def llFullWeakHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTDifferentialLLKineticMixedHessian period hPeriod frame
      fields.llAuxMetric fields.llField
      first.1 second.1 first.2.2 second.2.2 mu +
    globalPTLLWorldvolumeHessian period hPeriod fields
      (llFullWeakVariation period hPeriod first)
      (llFullWeakVariation period hPeriod second) mu

theorem llFullWeakHessian_eq_actual
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFullWeakHessian period hPeriod frame fields first second mu =
      fullLLHessian period hPeriod frame fields
        (llFullWeakDirectionPacket period hPeriod first)
        (llFullWeakDirectionPacket period hPeriod second) mu :=
  rfl

def llFullWeakEulerAlong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  fullLLEulerAlong period hPeriod frame fields
    (llFullWeakDirectionPacket period hPeriod first)
    (llFullWeakDirectionPacket period hPeriod second) mu t

/-- The bundled form is the actual second directional derivative already
proved for the simultaneous LL curve. -/
theorem llFullWeakEuler_second_direction_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (llFullWeakEulerAlong period hPeriod frame fields first second mu)
      (llFullWeakHessian period hPeriod frame fields first second mu) 0 := by
  rw [llFullWeakHessian_eq_actual]
  exact fullLLEuler_second_direction_hasDerivAt period hPeriod frame fields
    (llFullWeakDirectionPacket period hPeriod first)
    (llFullWeakDirectionPacket period hPeriod second) mu

theorem llFullWeakHessian_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFullWeakHessian period hPeriod frame fields first second mu =
      llFullWeakHessian period hPeriod frame fields second first mu := by
  unfold llFullWeakHessian
  rw [globalPTDifferentialLLKineticMixedHessian_symmetric,
    globalPTLLWorldvolumeHessian_symmetric]

private theorem globalPTMixedHessian_smul_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (scalar : Real)
    (a b : SmoothThroatField period hPeriod LLMetricFiber)
    (u v : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field
        (scalar • a) b (scalar • u) v mu =
      scalar * globalPTDifferentialLLKineticMixedHessian period hPeriod
        frame aux field a b u v mu := by
  unfold globalPTDifferentialLLKineticMixedHessian
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with point
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
  rw [differentialLLKineticMixedHessianDensity_smul_first]
  have ha :
      differentialLLAuxMetricDirectionPT period hPeriod (scalar • a) =
        scalar • differentialLLAuxMetricDirectionPT period hPeriod a := by
    ext current
    rfl
  have hu :
      differentialLLFluxDirectionPT period hPeriod (scalar • u) =
        scalar • differentialLLFluxDirectionPT period hPeriod u := by
    ext current
    rfl
  rw [ha, hu, differentialLLKineticMixedHessianDensity_smul_first]
  ring

private theorem globalPTWorldvolumeHessian_smul_first
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (scalar : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTLLWorldvolumeHessian period hPeriod fields
        (llFullWeakVariation period hPeriod (scalar • first))
        (llFullWeakVariation period hPeriod second) mu =
      scalar * globalPTLLWorldvolumeHessian period hPeriod fields
        (llFullWeakVariation period hPeriod first)
        (llFullWeakVariation period hPeriod second) mu := by
  have hScaled :
      llFullWeakVariation period hPeriod (scalar • first) =
        { measureDirection := scalar • first.2.1
          fieldDirection := scalar • first.2.2 } := rfl
  rw [hScaled]
  unfold globalPTLLWorldvolumeHessian
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with point
  unfold ptLLWorldvolumeHessianDensity ptAverage
    llWorldvolumeHessianDensity llFullWeakVariation
  have hMeasure :
      (scalar • first.2.1).toFun =
        fun current => scalar * first.2.1 current := rfl
  have hField :
      (scalar • first.2.2).toFun =
        fun current => scalar • first.2.2 current := rfl
  simp_rw [hMeasure, hField]
  change (1 / 2 : Real) * (_ + _) = scalar * ((1 / 2 : Real) * (_ + _))
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

theorem llFullWeakHessian_add_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second test : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llFullWeakHessian period hPeriod frame fields
        (first + second) test mu =
      llFullWeakHessian period hPeriod frame fields first test mu +
        llFullWeakHessian period hPeriod frame fields second test mu := by
  unfold llFullWeakHessian
  change
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        fields.llAuxMetric fields.llField
        (first.1 + second.1) test.1
        (first.2.2 + second.2.2) test.2.2 mu +
      globalPTLLWorldvolumeHessian period hPeriod fields
        (addVariation period hPeriod
          (llFullWeakVariation period hPeriod first)
          (llFullWeakVariation period hPeriod second))
        (llFullWeakVariation period hPeriod test) mu = _
  rw [globalPTMixedHessian_add_first,
    globalPTLLWorldvolumeHessian_add_first]
  ring

theorem llFullWeakHessian_smul_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real)
    (first test : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFullWeakHessian period hPeriod frame fields
        (scalar • first) test mu =
      scalar * llFullWeakHessian period hPeriod frame fields first test mu := by
  unfold llFullWeakHessian
  change
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame
        fields.llAuxMetric fields.llField
        (scalar • first.1) test.1
        (scalar • first.2.2) test.2.2 mu +
      globalPTLLWorldvolumeHessian period hPeriod fields
        (llFullWeakVariation period hPeriod (scalar • first))
        (llFullWeakVariation period hPeriod test) mu = _
  rw [globalPTMixedHessian_smul_first,
    globalPTWorldvolumeHessian_smul_first]
  ring

theorem llFullWeakHessian_add_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second test : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llFullWeakHessian period hPeriod frame fields test
        (first + second) mu =
      llFullWeakHessian period hPeriod frame fields test first mu +
        llFullWeakHessian period hPeriod frame fields test second mu := by
  rw [llFullWeakHessian_symmetric period hPeriod frame fields test
      (first + second) mu,
    llFullWeakHessian_add_left,
    llFullWeakHessian_symmetric period hPeriod frame fields first test mu,
    llFullWeakHessian_symmetric period hPeriod frame fields second test mu]

theorem llFullWeakHessian_smul_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real)
    (first test : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFullWeakHessian period hPeriod frame fields test
        (scalar • first) mu =
      scalar * llFullWeakHessian period hPeriod frame fields test first mu := by
  rw [llFullWeakHessian_symmetric period hPeriod frame fields test
      (scalar • first) mu,
    llFullWeakHessian_smul_left,
    llFullWeakHessian_symmetric period hPeriod frame fields first test mu]

/-- Weak Jacobi operator for all three currently typed simultaneous LL slots. -/
def llFullWeakJacobiOperator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    LLFullWeakTangent period hPeriod →ₗ[Real]
      LLFullWeakDual period hPeriod where
  toFun first :=
    { toFun := fun second =>
        llFullWeakHessian period hPeriod frame fields first second mu
      map_add' := fun second third =>
        llFullWeakHessian_add_right
          period hPeriod frame fields second third first mu
      map_smul' := fun scalar second =>
        llFullWeakHessian_smul_right
          period hPeriod frame fields scalar second first mu }
  map_add' first second := by
    apply LinearMap.ext
    intro test
    exact llFullWeakHessian_add_left
      period hPeriod frame fields first second test mu
  map_smul' scalar first := by
    apply LinearMap.ext
    intro test
    exact llFullWeakHessian_smul_left
      period hPeriod frame fields scalar first test mu

@[simp]
theorem llFullWeakJacobiOperator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : LLFullWeakTangent period hPeriod) :
    llFullWeakJacobiOperator period hPeriod frame fields mu first second =
      llFullWeakHessian period hPeriod frame fields first second mu :=
  rfl

end

end P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D
end JanusFormal
