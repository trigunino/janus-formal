import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalFieldsCenterReduction4D

/-! # Finite diffeomorphism BRST Euler map at zero nonminimal fields -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2DiffeomorphismBRSTCenterEuler4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2CartanFirstJet4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
open P0EFTJanusFiniteFrameC2DiffeomorphismFP4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Linear De Donder--Nakanishi--Lautrup density at fixed metric and tensor. -/
def finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (field : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    C0Scalar period hPeriod :=
  finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric metric *
    ∑ index : Fin frame.count,
      finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric index (metric, tensor) *
        finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame field index

/-- Integrated linear De Donder residual paired with the auxiliary field. -/
def finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (field : FiniteFrameDiffeomorphismC2Core period hPeriod frame) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity period hPeriod frame baseMetric
      metric tensor field)

/-- Exact polynomial identity along the auxiliary-field line. -/
theorem finiteFrameC2DiffeomorphismBRSTDensity_nakanishiLautrup_line
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (field : FiniteFrameDiffeomorphismC2Core period hPeriod frame) (t : Real) :
    finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame baseMetric
        (metric, (tensor, (t • field, 0))) =
      t ^ 2 • finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame baseMetric
          (metric, (tensor, (field, 0))) +
        (t - t ^ 2) •
          finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity period hPeriod frame
            baseMetric metric tensor field := by
  apply ContinuousMap.ext
  intro point
  simp [finiteFrameC2DiffeomorphismBRSTDensity,
    finiteFrameC2DiffeomorphismBRSTOperatorFeatures,
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply,
    finiteFrameDiffeomorphismBRSTC0Polynomial,
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity,
    Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  ring

/-- Integrated form of the exact auxiliary-field polynomial identity. -/
theorem finiteFrameC2DiffeomorphismBRSTAction_nakanishiLautrup_line
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (field : FiniteFrameDiffeomorphismC2Core period hPeriod frame) (t : Real) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
        (metric, (tensor, (t • field, 0))) =
      t ^ 2 * finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
          (metric, (tensor, (field, 0))) +
        (t - t ^ 2) *
          finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame
            baseMetric metric tensor field := by
  unfold finiteFrameC2DiffeomorphismBRSTAction
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction
  rw [finiteFrameC2DiffeomorphismBRSTDensity_nakanishiLautrup_line period hPeriod]
  simp

private theorem hasDerivAt_action_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {action : E → Real} {base : E} {derivative : E →L[Real] Real}
    (hAction : HasFDerivAt action derivative base) (direction : E) :
    HasDerivAt (fun t : Real => action (base + t • direction))
      (derivative direction) 0 := by
  have hLine : HasDerivAt (fun t : Real => base + t • direction) direction 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (x := (0 : Real)) (c := base)).fun_add
        ((hasDerivAt_id' (0 : Real)).smul_const direction)
  simpa only [Function.comp_def] using
    hAction.comp_hasDerivAt_of_eq 0 hLine (by simp only [zero_smul, add_zero])

/-- At zero nonminimal fields, the auxiliary-field Euler component is exactly
the integrated De Donder pairing. -/
theorem finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply_nakanishiLautrup
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (hMetric : metric ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (field : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric
        (metric, (tensor, 0)) (0, (0, (field, 0))) =
      finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame baseMetric
        metric tensor field := by
  let Input := FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame baseMetric
  let base : Input := (metric, (tensor, 0))
  let direction : Input := (0, (0, (field, 0)))
  let action := finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
  let derivative := finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric base
  let residual := finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame
    baseMetric metric tensor field
  have hAction : HasFDerivAt action derivative base := by
    exact finiteFrameC2DiffeomorphismBRSTAction_hasFDerivAt period hPeriod frame baseMetric
      base ⟨hMetric, Set.mem_univ _⟩
  have hLine := hasDerivAt_action_affine_line hAction direction
  have hLineForm :
      (fun t : Real => action (base + t • direction)) =
        (fun t : Real => t ^ 2 * action (metric, (tensor, (field, 0))) +
          (t - t ^ 2) * residual) := by
    funext t
    have hInput : base + t • direction = (metric, (tensor, (t • field, 0))) := by
      apply Prod.ext
      · change metric + t • (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) = metric
        simp
      · apply Prod.ext
        · change tensor + t • (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) = tensor
          simp
        · apply Prod.ext
          · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) + t • field = t • field
            simp
          · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame ×
              FiniteFrameDiffeomorphismC2Core period hPeriod frame) + t • 0 = 0
            simp
    rw [hInput]
    simpa [action, residual] using
      finiteFrameC2DiffeomorphismBRSTAction_nakanishiLautrup_line period hPeriod
        frame baseMetric metric tensor field t
  rw [hLineForm] at hLine
  have hId : HasDerivAt (fun t : Real => t) 1 0 := hasDerivAt_id 0
  have hPolynomial : HasDerivAt
      (fun t : Real => t ^ 2 * action (metric, (tensor, (field, 0))) +
        (t - t ^ 2) * residual) residual 0 := by
    have hRaw := ((hId.pow 2).mul_const (action (metric, (tensor, (field, 0))))).add
      ((hId.sub (hId.pow 2)).mul_const residual)
    exact hRaw.congr_deriv (by norm_num)
  have hDerivative := hLine.unique hPolynomial
  exact hDerivative

/-- With `B` and antighost zero, the action vanishes for every ghost. -/
theorem finiteFrameC2DiffeomorphismBRSTAction_zero_B_antighost
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (ghost : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
        (metric, (tensor, (0, (0, ghost)))) = 0 := by
  simp [finiteFrameC2DiffeomorphismBRSTAction,
    finiteFrameC2DiffeomorphismBRSTDensity,
    finiteFrameC2DiffeomorphismBRSTOperatorFeatures,
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply,
    finiteFrameDiffeomorphismBRSTC0Polynomial]

/-- With `B` and ghost zero, the action vanishes for every antighost. -/
theorem finiteFrameC2DiffeomorphismBRSTAction_zero_B_ghost
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (antighost : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
        (metric, (tensor, (0, (antighost, 0)))) = 0 := by
  simp [finiteFrameC2DiffeomorphismBRSTAction,
    finiteFrameC2DiffeomorphismBRSTDensity,
    finiteFrameC2DiffeomorphismBRSTOperatorFeatures,
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply,
    finiteFrameDiffeomorphismBRSTC0Polynomial,
    finiteFrameC2DiffeomorphismFP,
    finiteFrameC2DiffeomorphismFPCoefficient,
    finiteFrameC2CartanFirstJet,
    finiteFrameC2CartanComponentExpression,
    finiteFrameC2CartanComponentFirstDerivative,
    finiteFrameC2DeDonderFirstJetCoefficient]

/-- The antighost Euler component vanishes at zero nonminimal fields. -/
theorem finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply_antighost
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (hMetric : metric ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (antighost : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric
        (metric, (tensor, 0)) (0, (0, (0, (antighost, 0)))) = 0 := by
  let Input := FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame baseMetric
  let base : Input := (metric, (tensor, 0))
  let direction : Input := (0, (0, (0, (antighost, 0))))
  let action := finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
  let derivative := finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric base
  have hAction : HasFDerivAt action derivative base := by
    exact finiteFrameC2DiffeomorphismBRSTAction_hasFDerivAt period hPeriod frame baseMetric
      base ⟨hMetric, Set.mem_univ _⟩
  have hLine := hasDerivAt_action_affine_line hAction direction
  have hFunctions :
      (fun t : Real => action (base + t • direction)) =
        (fun _ : Real => (0 : Real)) := by
    funext t
    have hInput : base + t • direction =
        (metric, (tensor, (0, (t • antighost, 0)))) := by
      apply Prod.ext
      · change metric + t • (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) = metric
        simp
      · apply Prod.ext
        · change tensor + t • (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) = tensor
          simp
        · apply Prod.ext
          · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) + t • 0 = 0
            simp
          · apply Prod.ext
            · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) +
                  t • antighost = t • antighost
              simp
            · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) + t • 0 = 0
              simp
    rw [hInput]
    exact finiteFrameC2DiffeomorphismBRSTAction_zero_B_ghost period hPeriod frame
      baseMetric metric tensor (t • antighost)
  rw [hFunctions] at hLine
  exact hLine.unique (hasDerivAt_const (x := (0 : Real)) (c := (0 : Real)))

/-- The ghost Euler component vanishes at zero nonminimal fields. -/
theorem finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply_ghost
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (hMetric : metric ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (ghost : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric
        (metric, (tensor, 0)) (0, (0, (0, (0, ghost)))) = 0 := by
  let Input := FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame baseMetric
  let base : Input := (metric, (tensor, 0))
  let direction : Input := (0, (0, (0, (0, ghost))))
  let action := finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
  let derivative := finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric base
  have hAction : HasFDerivAt action derivative base := by
    exact finiteFrameC2DiffeomorphismBRSTAction_hasFDerivAt period hPeriod frame baseMetric
      base ⟨hMetric, Set.mem_univ _⟩
  have hLine := hasDerivAt_action_affine_line hAction direction
  have hFunctions :
      (fun t : Real => action (base + t • direction)) =
        (fun _ : Real => (0 : Real)) := by
    funext t
    have hInput : base + t • direction =
        (metric, (tensor, (0, (0, t • ghost)))) := by
      apply Prod.ext
      · change metric + t • (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) = metric
        simp
      · apply Prod.ext
        · change tensor + t • (0 : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) = tensor
          simp
        · apply Prod.ext
          · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) + t • 0 = 0
            simp
          · apply Prod.ext
            · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) + t • 0 = 0
              simp
            · change (0 : FiniteFrameDiffeomorphismC2Core period hPeriod frame) +
                  t • ghost = t • ghost
              simp
    rw [hInput]
    exact finiteFrameC2DiffeomorphismBRSTAction_zero_B_antighost period hPeriod frame
      baseMetric metric tensor (t • ghost)
  rw [hFunctions] at hLine
  exact hLine.unique (hasDerivAt_const (x := (0 : Real)) (c := (0 : Real)))

/-- At zero nonminimal fields, the full nonminimal Euler restriction is the
single De Donder pairing with its auxiliary-field component. -/
theorem finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (hMetric : metric ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (fields : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric
        (metric, (tensor, 0)) (0, (0, fields)) =
      finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame baseMetric
        metric tensor fields.1 := by
  let derivative := finiteFrameC2DiffeomorphismBRSTEuler period hPeriod frame baseMetric
    (metric, (tensor, 0))
  have hSplit :
      ((0, (0, fields)) : FiniteFrameC2DiffeomorphismBRSTCore period hPeriod frame baseMetric) =
        (0, (0, (fields.1, 0))) +
          (0, (0, (0, (fields.2.1, 0)))) +
          (0, (0, (0, (0, fields.2.2)))) := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · apply Prod.ext
        · simp
        · apply Prod.ext <;> simp
  change derivative (0, (0, fields)) = _
  rw [hSplit, map_add, map_add,
    finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply_nakanishiLautrup
      period hPeriod frame baseMetric metric tensor hMetric fields.1,
    finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply_antighost
      period hPeriod frame baseMetric metric tensor hMetric fields.2.1,
    finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply_ghost
      period hPeriod frame baseMetric metric tensor hMetric fields.2.2]
  simp

end
end P0EFTJanusFiniteFrameC2DiffeomorphismBRSTCenterEuler4D
end JanusFormal
