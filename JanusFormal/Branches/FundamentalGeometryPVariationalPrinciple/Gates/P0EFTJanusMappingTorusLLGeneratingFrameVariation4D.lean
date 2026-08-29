import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D

/-!
# Typed LL generating-frame variations

The finite LL frame is a spanning family of smooth throat vector fields.
Its linear tangent is therefore a family of smooth vector fields with the
same finite index type.  An actual frame curve additionally carries a frame
at every parameter value and its velocity is checked fiberwise.

An exponential rescaling gives a nonconstant, globally defined curve of
actual generating frames and realizes the radial tangent exactly.  Along this
realized sector, the first variation and symmetric mixed radial frame Hessian
are proved from the true PT action.  The diagonal Lie action on the frame,
auxiliary metric, measure coefficient, and LL flux is also bundled below.

The existing LL action curve still accepts only the last three slots.  The
generic four-slot Hessian operator supplied here is consequently named
`frameFrozen`: it is the exact pullback of the proved three-slot Hessian and
is not presented as a generic frame Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLLGeneratingFrameVariation4D

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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusTruePTDifferentialLLSimultaneousVariation4D

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

local instance effectiveThroatTangentNormedAddCommGroup
    (point : EffectiveThroat period hPeriod) :
    NormedAddCommGroup
      (TangentSpace throatCoverModelWithCorners point) :=
  inferInstanceAs (NormedAddCommGroup ThroatCoverCoordinates)

local instance effectiveThroatTangentNormedSpace
    (point : EffectiveThroat period hPeriod) :
    NormedSpace Real (TangentSpace throatCoverModelWithCorners point) :=
  inferInstanceAs (NormedSpace Real ThroatCoverCoordinates)

/-- Linear tangent space of a fixed finite generating frame. -/
abbrev LLFrameTangent
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  Fin frame.count → CInfinityThroatGhost period hPeriod

/-- The vector fields underlying a generating frame, viewed in its tangent
space. -/
def llFrameBaseTangent
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    LLFrameTangent period hPeriod frame :=
  fun index =>
    { toFun := fun point => frame.vectorAt point index
      contMDiff_toFun := frame.contMDiff_vector index }

@[simp]
theorem llFrameBaseTangent_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (index : Fin frame.count) (point : EffectiveThroat period hPeriod) :
    llFrameBaseTangent period hPeriod frame index point =
      frame.vectorAt point index :=
  rfl

/-- The affine curve in the linear space of smooth frame sections.  It is
always a faithful tangent curve; spanning is deliberately not asserted. -/
def llFrameSectionAffineCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : LLFrameTangent period hPeriod frame) (t : Real) :
    LLFrameTangent period hPeriod frame :=
  llFrameBaseTangent period hPeriod frame + t • direction

@[simp]
theorem llFrameSectionAffineCurve_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : LLFrameTangent period hPeriod frame) :
    llFrameSectionAffineCurve period hPeriod frame direction 0 =
      llFrameBaseTangent period hPeriod frame := by
  simp [llFrameSectionAffineCurve]

theorem llFrameSectionAffineCurve_sub_base
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : LLFrameTangent period hPeriod frame) (t : Real) :
    llFrameSectionAffineCurve period hPeriod frame direction t -
        llFrameBaseTangent period hPeriod frame =
      t • direction := by
  simp [llFrameSectionAffineCurve]

/-- A curve whose every value is an actual generating frame with the original
finite index count. -/
structure LLGeneratingFrameCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod) where
  toFrame : Real → SmoothThroatGeneratingFrame period hPeriod
  count_eq : ∀ t, (toFrame t).count = frame.count
  at_zero_vector : ∀ (point : EffectiveThroat period hPeriod)
      (index : Fin frame.count),
    (toFrame 0).vectorAt point (Fin.cast (count_eq 0).symm index) =
      frame.vectorAt point index

/-- A frame curve's vectors transported to the fixed index type. -/
def LLGeneratingFrameCurve.vectorAt
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    (curve : LLGeneratingFrameCurve period hPeriod frame)
    (t : Real) (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count) :
    TangentSpace throatCoverModelWithCorners point :=
  (curve.toFrame t).vectorAt point
    (Fin.cast (curve.count_eq t).symm index)

@[simp]
theorem LLGeneratingFrameCurve.vectorAt_zero
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    (curve : LLGeneratingFrameCurve period hPeriod frame)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count) :
    curve.vectorAt period hPeriod 0 point index =
      frame.vectorAt point index :=
  curve.at_zero_vector point index

/-- Exact fiberwise velocity predicate for a curve of actual frames. -/
def LLGeneratingFrameCurve.HasVelocity
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    (curve : LLGeneratingFrameCurve period hPeriod frame)
    (direction : LLFrameTangent period hPeriod frame) : Prop :=
  ∀ (point : EffectiveThroat period hPeriod) (index : Fin frame.count),
    HasDerivAt
      (fun t => curve.vectorAt period hPeriod t point index)
      (direction index point) 0

/-- Nonzero scalar rescaling preserves the spanning property. -/
def llScaleGeneratingFrame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0) :
    SmoothThroatGeneratingFrame period hPeriod where
  count := frame.count
  vectorAt point index := scale • frame.vectorAt point index
  spansAt point := by
    apply top_unique
    rw [← frame.spansAt point]
    apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    have hScaled :
        scale • frame.vectorAt point index ∈
          Submodule.span Real
            (Set.range
              (fun current : Fin frame.count =>
                scale • frame.vectorAt point current)) :=
      Submodule.subset_span ⟨index, rfl⟩
    have hRecovered := (Submodule.span Real
      (Set.range
        (fun current : Fin frame.count =>
          scale • frame.vectorAt point current))).smul_mem
            scale⁻¹ hScaled
    simpa [hScale] using hRecovered
  contMDiff_vector index := by
    exact (scale • llFrameBaseTangent period hPeriod frame index).contMDiff

@[simp]
theorem llScaleGeneratingFrame_count
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0) :
    (llScaleGeneratingFrame period hPeriod frame scale hScale).count =
      frame.count :=
  rfl

@[simp]
theorem llScaleGeneratingFrame_vectorAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (point : EffectiveThroat period hPeriod) (index : Fin frame.count) :
    (llScaleGeneratingFrame period hPeriod frame scale hScale).vectorAt
        point index =
      scale • frame.vectorAt point index :=
  rfl

/-- Actual global frame curve generated by exponential rescaling. -/
def llFrameExponentialCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rate : Real) :
    LLGeneratingFrameCurve period hPeriod frame where
  toFrame t :=
    llScaleGeneratingFrame period hPeriod frame
      (Real.exp (rate * t)) (Real.exp_ne_zero _)
  count_eq _ := rfl
  at_zero_vector point index := by
    simp [llScaleGeneratingFrame]

/-- Velocity realized by the exponential frame curve. -/
def llFrameRadialDirection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rate : Real) :
    LLFrameTangent period hPeriod frame :=
  rate • llFrameBaseTangent period hPeriod frame

theorem llFrameExponentialCurve_hasVelocity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rate : Real) :
    (llFrameExponentialCurve period hPeriod frame rate).HasVelocity
      period hPeriod (llFrameRadialDirection period hPeriod frame rate) := by
  intro point index
  have hScalar :
      HasDerivAt (fun t : Real => Real.exp (rate * t)) rate 0 := by
    have hInner : HasDerivAt (fun t : Real => rate * t) rate 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul rate
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (rate * 0)).comp 0 hInner
  simpa [LLGeneratingFrameCurve.vectorAt, llFrameExponentialCurve,
    llScaleGeneratingFrame, llFrameRadialDirection,
    llFrameBaseTangent] using
      hScalar.smul_const (frame.vectorAt point index)

theorem throatFrameDerivative_scale
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) (index : Fin frame.count) :
    throatFrameDerivative period hPeriod LLFieldFiber
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        field point index =
      scale • throatFrameDerivative period hPeriod LLFieldFiber
        frame field point index := by
  rw [throatFrameDerivative_eq_mvfderiv,
    throatFrameDerivative_eq_mvfderiv]
  exact map_smul
    (mvfderiv throatCoverModelWithCorners field.toFun point)
    scale (frame.vectorAt point index)

theorem throatDerivativeEnergy_scale
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativeEnergy period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        field point =
      scale ^ 2 *
        throatDerivativeEnergy period hPeriod frame field point := by
  unfold throatDerivativeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [throatFrameDerivative_scale]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem differentialLLKineticDensity_scale
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLKineticDensity period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        aux field point =
      scale ^ 2 *
        differentialLLKineticDensity period hPeriod frame aux field point := by
  unfold differentialLLKineticDensity
  rw [throatDerivativeEnergy_scale]
  ring

theorem ptSymmetricDifferentialLLKineticDensity_scale
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticDensity period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        aux field point =
      scale ^ 2 *
        ptSymmetricDifferentialLLKineticDensity
          period hPeriod frame aux field point := by
  unfold ptSymmetricDifferentialLLKineticDensity
  rw [differentialLLKineticDensity_scale,
    differentialLLKineticDensity_scale]
  ring

theorem globalPTDifferentialLLKineticAction_scale
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTDifferentialLLKineticAction period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        aux field mu =
      scale ^ 2 *
        globalPTDifferentialLLKineticAction
          period hPeriod frame aux field mu := by
  unfold globalPTDifferentialLLKineticAction
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with point
  exact ptSymmetricDifferentialLLKineticDensity_scale
    period hPeriod frame scale hScale aux field point

/-- Exact action formula along the actual exponential frame curve. -/
theorem truePTAction_frameExponential_eq
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (rate t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLAction period hPeriod
        ((llFrameExponentialCurve period hPeriod frame rate).toFrame t)
        fields mu =
      Real.exp (rate * t) ^ 2 *
          globalPTDifferentialLLKineticAction period hPeriod frame
            fields.llAuxMetric fields.llField mu +
        globalPTLLWorldvolumeAction period hPeriod fields mu := by
  rw [← globalPTFullDifferentialLLAction_eq_true]
  unfold globalPTFullDifferentialLLAction llFrameExponentialCurve
  rw [globalPTDifferentialLLKineticAction_scale]

/-- Genuine first frame derivative of the true PT action in every radial
frame direction. -/
theorem truePTAction_frameExponential_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (rate : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun t : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod
          ((llFrameExponentialCurve period hPeriod frame rate).toFrame t)
          fields mu)
      (2 * rate *
        globalPTDifferentialLLKineticAction period hPeriod frame
          fields.llAuxMetric fields.llField mu) 0 := by
  have hExp :
      HasDerivAt (fun t : Real => Real.exp (rate * t)) rate 0 := by
    have hInner : HasDerivAt (fun t : Real => rate * t) rate 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul rate
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (rate * 0)).comp 0 hInner
  rw [show
    (fun t : Real =>
      globalPTSymmetricDifferentialLLAction period hPeriod
        ((llFrameExponentialCurve period hPeriod frame rate).toFrame t)
        fields mu) =
      fun t : Real =>
        Real.exp (rate * t) ^ 2 *
            globalPTDifferentialLLKineticAction period hPeriod frame
              fields.llAuxMetric fields.llField mu +
          globalPTLLWorldvolumeAction period hPeriod fields mu by
    funext t
    exact truePTAction_frameExponential_eq
      period hPeriod frame fields rate t mu]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (((hExp.pow 2).mul_const
      (globalPTDifferentialLLKineticAction period hPeriod frame
        fields.llAuxMetric fields.llField mu)).const_add
      (globalPTLLWorldvolumeAction period hPeriod fields mu))

/-- First radial frame variation transported along a second radial frame
curve. -/
def llFrameRadialEulerAlong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (firstRate secondRate : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  2 * firstRate * Real.exp (secondRate * t) ^ 2 *
    globalPTDifferentialLLKineticAction period hPeriod frame
      fields.llAuxMetric fields.llField mu

theorem truePTAction_nestedFrameExponential_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (firstRate secondRate t : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun s : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod
          ((llFrameExponentialCurve period hPeriod
            ((llFrameExponentialCurve
              period hPeriod frame secondRate).toFrame t) firstRate).toFrame s)
          fields mu)
      (llFrameRadialEulerAlong period hPeriod frame fields
        firstRate secondRate mu t) 0 := by
  have h := truePTAction_frameExponential_hasDerivAt
    period hPeriod
      ((llFrameExponentialCurve period hPeriod frame secondRate).toFrame t)
      fields firstRate mu
  rw [show
    globalPTDifferentialLLKineticAction period hPeriod
        ((llFrameExponentialCurve period hPeriod frame secondRate).toFrame t)
        fields.llAuxMetric fields.llField mu =
      Real.exp (secondRate * t) ^ 2 *
        globalPTDifferentialLLKineticAction period hPeriod frame
          fields.llAuxMetric fields.llField mu by
    exact globalPTDifferentialLLKineticAction_scale
      period hPeriod frame (Real.exp (secondRate * t))
        (Real.exp_ne_zero _) fields.llAuxMetric fields.llField mu] at h
  simpa [llFrameRadialEulerAlong, mul_assoc] using h

/-- Actual mixed Hessian in the globally realized radial frame sector. -/
def llFrameRadialHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (firstRate secondRate : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  4 * firstRate * secondRate *
    globalPTDifferentialLLKineticAction period hPeriod frame
      fields.llAuxMetric fields.llField mu

theorem llFrameRadialEulerAlong_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (firstRate secondRate : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    HasDerivAt
      (llFrameRadialEulerAlong period hPeriod frame fields
        firstRate secondRate mu)
      (llFrameRadialHessian period hPeriod frame fields
        firstRate secondRate mu) 0 := by
  have hExp :
      HasDerivAt (fun t : Real => Real.exp (secondRate * t))
        secondRate 0 := by
    have hInner :
        HasDerivAt (fun t : Real => secondRate * t) secondRate 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul secondRate
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (secondRate * 0)).comp 0 hInner
  let kinetic :=
    globalPTDifferentialLLKineticAction period hPeriod frame
      fields.llAuxMetric fields.llField mu
  have hDerivative :=
    ((hExp.pow 2).mul_const kinetic).mul_const (2 * firstRate)
  have hFunction :
      llFrameRadialEulerAlong period hPeriod frame fields
          firstRate secondRate mu =
        fun t => Real.exp (secondRate * t) ^ 2 * kinetic *
          (2 * firstRate) := by
    funext t
    unfold llFrameRadialEulerAlong
    dsimp only [kinetic]
    ring
  have hValue :
      llFrameRadialHessian period hPeriod frame fields
          firstRate secondRate mu =
        (2 * secondRate) * kinetic * (2 * firstRate) := by
    unfold llFrameRadialHessian
    dsimp only [kinetic]
    ring
  rw [hFunction, hValue]
  simpa only [Pi.pow_apply, mul_zero, Real.exp_zero, Nat.reduceSub, pow_one,
    Nat.cast_ofNat, one_mul, mul_one] using hDerivative

theorem llFrameRadialHessian_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (firstRate secondRate : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameRadialHessian period hPeriod frame fields
        firstRate secondRate mu =
      llFrameRadialHessian period hPeriod frame fields
        secondRate firstRate mu := by
  unfold llFrameRadialHessian
  ring

/-- Constant smooth throat scalar used to expose real linearity of the vector
field bracket. -/
def llConstantThroatScalar (value : Real) :
    CInfinityThroatScalarField period hPeriod :=
  ⟨fun _ => value, contMDiff_const⟩

@[simp]
theorem throatScalarLieDerivative_constant
    (ghost : CInfinityThroatGhost period hPeriod) (value : Real) :
    throatScalarLieDerivative period hPeriod ghost
        (llConstantThroatScalar period hPeriod value) = 0 := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv throatCoverModelWithCorners
      (fun _ : EffectiveThroat period hPeriod => value)
      point (ghost point) = 0
  rw [mvfderiv_const]
  rfl

@[simp]
theorem throatScalarSmulGhost_constant
    (value : Real) (ghost : CInfinityThroatGhost period hPeriod) :
    throatScalarSmulGhost period hPeriod
        (llConstantThroatScalar period hPeriod value) ghost =
      value • ghost := by
  apply ContMDiffSection.ext
  intro point
  rfl

theorem throatGhostLieBracket_const_smul_right
    (ghost direction : CInfinityThroatGhost period hPeriod)
    (value : Real) :
    throatGhostLieBracket period hPeriod ghost (value • direction) =
      value • throatGhostLieBracket period hPeriod ghost direction := by
  rw [← throatScalarSmulGhost_constant period hPeriod value direction,
    throatGhostLieBracket_scalarSmul_right,
    throatScalarLieDerivative_constant]
  apply ContMDiffSection.ext
  intro point
  simp [throatScalarSmulGhost, llConstantThroatScalar]

/-- Lie derivative of every vector in a frame tangent. -/
def llFrameLieDerivative
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod)
    (direction : LLFrameTangent period hPeriod frame) :
    LLFrameTangent period hPeriod frame :=
  fun index =>
    throatGhostLieBracket period hPeriod ghost (direction index)

theorem llFrameLieDerivative_add
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod)
    (first second : LLFrameTangent period hPeriod frame) :
    llFrameLieDerivative period hPeriod frame ghost (first + second) =
      llFrameLieDerivative period hPeriod frame ghost first +
        llFrameLieDerivative period hPeriod frame ghost second := by
  funext index
  exact throatGhostLieBracket_add_right period hPeriod
    ghost (first index) (second index)

theorem llFrameLieDerivative_smul
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod)
    (value : Real) (direction : LLFrameTangent period hPeriod frame) :
    llFrameLieDerivative period hPeriod frame ghost (value • direction) =
      value • llFrameLieDerivative period hPeriod frame ghost direction := by
  funext index
  exact throatGhostLieBracket_const_smul_right period hPeriod
    ghost (direction index) value

/-- Natural linear Lie action on the frame tangent. -/
def llFrameLieDerivativeLinear
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod) :
    LLFrameTangent period hPeriod frame →ₗ[Real]
      LLFrameTangent period hPeriod frame where
  toFun := llFrameLieDerivative period hPeriod frame ghost
  map_add' := llFrameLieDerivative_add period hPeriod frame ghost
  map_smul' := llFrameLieDerivative_smul period hPeriod frame ghost

universe u

/-- Componentwise scalar Lie derivative of a Euclidean throat field. -/
def llEuclideanLieDerivative
    {Index : Type u} [Fintype Index]
    (ghost : CInfinityThroatGhost period hPeriod)
    (field :
      SmoothThroatField period hPeriod (EuclideanSpace Real Index)) :
    SmoothThroatField period hPeriod (EuclideanSpace Real Index) where
  toFun point :=
    (EuclideanSpace.equiv Index Real).symm
      (fun index =>
        throatScalarLieDerivative period hPeriod ghost
          (smoothThroatEuclideanCoordinate period hPeriod field index) point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv Index Real).symm.toContinuousLinearMap.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact
      (throatScalarLieDerivative period hPeriod ghost
        (smoothThroatEuclideanCoordinate period hPeriod field index)).contMDiff

theorem llEuclideanLieDerivative_add
    {Index : Type u} [Fintype Index]
    (ghost : CInfinityThroatGhost period hPeriod)
    (first second :
      SmoothThroatField period hPeriod (EuclideanSpace Real Index)) :
    llEuclideanLieDerivative period hPeriod ghost (first + second) =
      llEuclideanLieDerivative period hPeriod ghost first +
        llEuclideanLieDerivative period hPeriod ghost second := by
  apply SmoothThroatField.ext period hPeriod (EuclideanSpace Real Index)
  intro point
  apply (EuclideanSpace.equiv Index Real).injective
  funext index
  have hCoordinate :
      smoothThroatEuclideanCoordinate period hPeriod
          (first + second) index =
        smoothThroatEuclideanCoordinate period hPeriod first index +
          smoothThroatEuclideanCoordinate period hPeriod second index := by
    apply ContMDiffMap.ext
    intro current
    rfl
  change throatScalarLieDerivative period hPeriod ghost
      (smoothThroatEuclideanCoordinate period hPeriod
        (first + second) index) point = _
  rw [hCoordinate, throatScalarLieDerivative_addScalar]
  rfl

theorem llEuclideanLieDerivative_smul
    {Index : Type u} [Fintype Index]
    (ghost : CInfinityThroatGhost period hPeriod)
    (value : Real)
    (field :
      SmoothThroatField period hPeriod (EuclideanSpace Real Index)) :
    llEuclideanLieDerivative period hPeriod ghost (value • field) =
      value • llEuclideanLieDerivative period hPeriod ghost field := by
  apply SmoothThroatField.ext period hPeriod (EuclideanSpace Real Index)
  intro point
  apply (EuclideanSpace.equiv Index Real).injective
  funext index
  have hCoordinate :
      smoothThroatEuclideanCoordinate period hPeriod
          (value • field) index =
        value • smoothThroatEuclideanCoordinate
          period hPeriod field index := by
    apply ContMDiffMap.ext
    intro current
    rfl
  change throatScalarLieDerivative period hPeriod ghost
      (smoothThroatEuclideanCoordinate period hPeriod
        (value • field) index) point = _
  rw [hCoordinate, throatScalarLieDerivative_smulScalar]
  rfl

def llEuclideanLieDerivativeLinear
    {Index : Type u} [Fintype Index]
    (ghost : CInfinityThroatGhost period hPeriod) :
    SmoothThroatField period hPeriod (EuclideanSpace Real Index) →ₗ[Real]
      SmoothThroatField period hPeriod (EuclideanSpace Real Index) where
  toFun := llEuclideanLieDerivative period hPeriod ghost
  map_add' := llEuclideanLieDerivative_add period hPeriod ghost
  map_smul' := llEuclideanLieDerivative_smul period hPeriod ghost

/-- Scalar Lie derivative in the analytic LL measure-coefficient slot. -/
def llRealLieDerivative
    (ghost : CInfinityThroatGhost period hPeriod)
    (field : SmoothThroatField period hPeriod Real) :
    SmoothThroatField period hPeriod Real where
  toFun point :=
    throatScalarLieDerivative period hPeriod ghost
      (analyticThroatScalarToCInfinity period hPeriod field) point
  contMDiff_toFun :=
    (throatScalarLieDerivative period hPeriod ghost
      (analyticThroatScalarToCInfinity period hPeriod field)).contMDiff

theorem llRealLieDerivative_add
    (ghost : CInfinityThroatGhost period hPeriod)
    (first second : SmoothThroatField period hPeriod Real) :
    llRealLieDerivative period hPeriod ghost (first + second) =
      llRealLieDerivative period hPeriod ghost first +
        llRealLieDerivative period hPeriod ghost second := by
  apply SmoothThroatField.ext period hPeriod Real
  intro point
  have hAnalytic :
      analyticThroatScalarToCInfinity period hPeriod (first + second) =
        analyticThroatScalarToCInfinity period hPeriod first +
          analyticThroatScalarToCInfinity period hPeriod second := by
    apply ContMDiffMap.ext
    intro current
    rfl
  change throatScalarLieDerivative period hPeriod ghost
      (analyticThroatScalarToCInfinity period hPeriod
        (first + second)) point = _
  rw [hAnalytic, throatScalarLieDerivative_addScalar]
  rfl

theorem llRealLieDerivative_smul
    (ghost : CInfinityThroatGhost period hPeriod)
    (value : Real) (field : SmoothThroatField period hPeriod Real) :
    llRealLieDerivative period hPeriod ghost (value • field) =
      value • llRealLieDerivative period hPeriod ghost field := by
  apply SmoothThroatField.ext period hPeriod Real
  intro point
  have hAnalytic :
      analyticThroatScalarToCInfinity period hPeriod (value • field) =
        value • analyticThroatScalarToCInfinity period hPeriod field := by
    apply ContMDiffMap.ext
    intro current
    rfl
  change throatScalarLieDerivative period hPeriod ghost
      (analyticThroatScalarToCInfinity period hPeriod
        (value • field)) point = _
  rw [hAnalytic, throatScalarLieDerivative_smulScalar]
  rfl

def llRealLieDerivativeLinear
    (ghost : CInfinityThroatGhost period hPeriod) :
    SmoothThroatField period hPeriod Real →ₗ[Real]
      SmoothThroatField period hPeriod Real where
  toFun := llRealLieDerivative period hPeriod ghost
  map_add' := llRealLieDerivative_add period hPeriod ghost
  map_smul' := llRealLieDerivative_smul period hPeriod ghost

/-- All four LL tangent slots: frame, auxiliary metric, measure coefficient,
and flux. -/
abbrev LLFourSlotTangent
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  LLFrameTangent period hPeriod frame ×
    LLFullWeakTangent period hPeriod

abbrev LLFourSlotDual
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  LLFourSlotTangent period hPeriod frame →ₗ[Real] Real

/-- The natural diagonal Lie action on all four LL tangent slots. -/
def llFourSlotDiagonalLieGenerator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod) :
    LLFourSlotTangent period hPeriod frame →ₗ[Real]
      LLFourSlotTangent period hPeriod frame :=
  (llFrameLieDerivativeLinear period hPeriod frame ghost).prodMap
    ((llEuclideanLieDerivativeLinear period hPeriod ghost).prodMap
      ((llRealLieDerivativeLinear period hPeriod ghost).prodMap
        (llEuclideanLieDerivativeLinear period hPeriod ghost)))

/-- The background frame and the three actual LL fields as one four-slot
linear packet. -/
def llFourSlotBackground
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) :
    LLFourSlotTangent period hPeriod frame :=
  (llFrameBaseTangent period hPeriod frame,
    (fields.llAuxMetric, (fields.llMeasure, fields.llField)))

/-- Infinitesimal diagonal gauge direction at a concrete LL background. -/
def llFourSlotDiagonalGaugeDirection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod) :
    LLFourSlotTangent period hPeriod frame :=
  llFourSlotDiagonalLieGenerator period hPeriod frame ghost
    (llFourSlotBackground period hPeriod frame fields)

@[simp]
theorem llFourSlotDiagonalGaugeDirection_frame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod) :
    (llFourSlotDiagonalGaugeDirection
      period hPeriod frame fields ghost).1 =
      llFrameLieDerivative period hPeriod frame ghost
        (llFrameBaseTangent period hPeriod frame) :=
  rfl

/-- Three concrete diagonal generators supplied by the actual throat rotation
ghosts. -/
def llFourSlotRotationGaugeDirection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) (axis : Fin 3) :
    LLFourSlotTangent period hPeriod frame :=
  llFourSlotDiagonalGaugeDirection period hPeriod frame fields
    (throatSpatialRotationGhost period hPeriod axis)

/-- Forgetting the frame slot is the exact map into the previously proved
three-slot variational API. -/
def llFourSlotForgetFrame
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    LLFourSlotTangent period hPeriod frame →ₗ[Real]
      LLFullWeakTangent period hPeriod :=
  LinearMap.snd Real
    (LLFrameTangent period hPeriod frame)
    (LLFullWeakTangent period hPeriod)

/-- The proved Hessian pulled back along `llFourSlotForgetFrame`.  This is
precisely the frame-frozen reduction, not a frame-varying Hessian. -/
def llFrameFrozenFourSlotHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFourSlotTangent period hPeriod frame)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  llFullWeakHessian period hPeriod frame fields first.2 second.2 mu

theorem llFrameFrozenFourSlotHessian_add_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second test : LLFourSlotTangent period hPeriod frame)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llFrameFrozenFourSlotHessian period hPeriod frame fields
        (first + second) test mu =
      llFrameFrozenFourSlotHessian period hPeriod frame fields first test mu +
        llFrameFrozenFourSlotHessian
          period hPeriod frame fields second test mu :=
  llFullWeakHessian_add_left period hPeriod frame fields
    first.2 second.2 test.2 mu

theorem llFrameFrozenFourSlotHessian_smul_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (value : Real)
    (first test : LLFourSlotTangent period hPeriod frame)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameFrozenFourSlotHessian period hPeriod frame fields
        (value • first) test mu =
      value * llFrameFrozenFourSlotHessian
        period hPeriod frame fields first test mu :=
  llFullWeakHessian_smul_left period hPeriod frame fields
    value first.2 test.2 mu

theorem llFrameFrozenFourSlotHessian_add_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second test : LLFourSlotTangent period hPeriod frame)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llFrameFrozenFourSlotHessian period hPeriod frame fields test
        (first + second) mu =
      llFrameFrozenFourSlotHessian period hPeriod frame fields test first mu +
        llFrameFrozenFourSlotHessian
          period hPeriod frame fields test second mu :=
  llFullWeakHessian_add_right period hPeriod frame fields
    first.2 second.2 test.2 mu

theorem llFrameFrozenFourSlotHessian_smul_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (value : Real)
    (first test : LLFourSlotTangent period hPeriod frame)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameFrozenFourSlotHessian period hPeriod frame fields test
        (value • first) mu =
      value * llFrameFrozenFourSlotHessian
        period hPeriod frame fields test first mu :=
  llFullWeakHessian_smul_right period hPeriod frame fields
    value first.2 test.2 mu

/-- Bundled frame-frozen four-slot Jacobi operator. -/
def llFrameFrozenFourSlotJacobiOperator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    LLFourSlotTangent period hPeriod frame →ₗ[Real]
      LLFourSlotDual period hPeriod frame where
  toFun first :=
    { toFun := fun second =>
        llFrameFrozenFourSlotHessian
          period hPeriod frame fields first second mu
      map_add' := fun second third =>
        llFrameFrozenFourSlotHessian_add_right
          period hPeriod frame fields second third first mu
      map_smul' := fun value second =>
        llFrameFrozenFourSlotHessian_smul_right
          period hPeriod frame fields value second first mu }
  map_add' first second := by
    apply LinearMap.ext
    intro test
    exact llFrameFrozenFourSlotHessian_add_left
      period hPeriod frame fields first second test mu
  map_smul' value first := by
    apply LinearMap.ext
    intro test
    exact llFrameFrozenFourSlotHessian_smul_left
      period hPeriod frame fields value first test mu

@[simp]
theorem llFrameFrozenFourSlotJacobiOperator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : LLFourSlotTangent period hPeriod frame) :
    llFrameFrozenFourSlotJacobiOperator period hPeriod frame fields mu
        first second =
      llFullWeakHessian period hPeriod frame fields first.2 second.2 mu :=
  rfl

/-- Exact typed obstruction: the current Hessian API annihilates every pure
frame tangent because it never varies the frame argument. -/
theorem llFrameFrozenFourSlotJacobiOperator_pureFrame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (direction : LLFrameTangent period hPeriod frame) :
    llFrameFrozenFourSlotJacobiOperator period hPeriod frame fields mu
        (direction, 0) = 0 := by
  apply LinearMap.ext
  intro test
  change llFullWeakHessian period hPeriod frame fields 0 test.2 mu = 0
  simpa using llFullWeakHessian_smul_left
    period hPeriod frame fields 0
      (0 : LLFullWeakTangent period hPeriod) test.2 mu

/-- On a diagonal gauge direction, the known operator sees exactly the old
three-slot Lie direction and drops the now typed frame component. -/
theorem llFrameFrozenFourSlotJacobiOperator_diagonal_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (ghost : CInfinityThroatGhost period hPeriod)
    (test : LLFourSlotTangent period hPeriod frame) :
    llFrameFrozenFourSlotJacobiOperator period hPeriod frame fields mu
        (llFourSlotDiagonalGaugeDirection
          period hPeriod frame fields ghost) test =
      llFullWeakHessian period hPeriod frame fields
        (llEuclideanLieDerivative period hPeriod ghost fields.llAuxMetric,
          (llRealLieDerivative period hPeriod ghost fields.llMeasure,
            llEuclideanLieDerivative period hPeriod ghost fields.llField))
        test.2 mu :=
  rfl

end

end P0EFTJanusMappingTorusLLGeneratingFrameVariation4D
end JanusFormal
