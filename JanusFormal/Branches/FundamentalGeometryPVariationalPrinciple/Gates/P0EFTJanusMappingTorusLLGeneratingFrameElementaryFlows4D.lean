import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLGeneratingFrameVariation4D

/-!
# Elementary globally admissible LL frame flows

The radial frame curve is enlarged in two independent ways:

* every generator may be exponentially rescaled at its own rate;
* one generator may be sheared by a smooth multiple of another.

Both constructions remain generating frames for every real parameter and
their velocities are proved in the fixed linear tangent space.  Thus the
admissible frame sector is no longer restricted to one radial direction.
The realization of an arbitrary raw frame tangent still requires a smooth
coefficient/right-inverse theorem for the finite generating family.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLLGeneratingFrameElementaryFlows4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusLLGeneratingFrameVariation4D

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

local instance effectiveThroatTangentNormedAddCommGroup
    (point : EffectiveThroat period hPeriod) :
    NormedAddCommGroup
      (TangentSpace throatCoverModelWithCorners point) :=
  inferInstanceAs (NormedAddCommGroup ThroatCoverCoordinates)

local instance effectiveThroatTangentNormedSpace
    (point : EffectiveThroat period hPeriod) :
    NormedSpace Real (TangentSpace throatCoverModelWithCorners point) :=
  inferInstanceAs (NormedSpace Real ThroatCoverCoordinates)

/-- Independent nonzero rescaling of every member of a generating family. -/
def llAnisotropicScaleGeneratingFrame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rates : Fin frame.count → Real) (t : Real) :
    SmoothThroatGeneratingFrame period hPeriod where
  count := frame.count
  vectorAt point index :=
    Real.exp (rates index * t) • frame.vectorAt point index
  spansAt point := by
    apply top_unique
    rw [← frame.spansAt point]
    apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    have hScaled :
        Real.exp (rates index * t) • frame.vectorAt point index ∈
          Submodule.span Real
            (Set.range (fun current : Fin frame.count =>
              Real.exp (rates current * t) •
                frame.vectorAt point current)) :=
      Submodule.subset_span ⟨index, rfl⟩
    have hRecovered := (Submodule.span Real
      (Set.range (fun current : Fin frame.count =>
        Real.exp (rates current * t) •
          frame.vectorAt point current))).smul_mem
            (Real.exp (rates index * t))⁻¹ hScaled
    simpa [Real.exp_ne_zero] using hRecovered
  contMDiff_vector index := by
    exact
      (Real.exp (rates index * t) •
        llFrameBaseTangent period hPeriod frame index).contMDiff

@[simp]
theorem llAnisotropicScaleGeneratingFrame_vectorAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rates : Fin frame.count → Real) (t : Real)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count) :
    (llAnisotropicScaleGeneratingFrame
      period hPeriod frame rates t).vectorAt point index =
      Real.exp (rates index * t) • frame.vectorAt point index :=
  rfl

/-- Globally defined anisotropic exponential curve of actual frames. -/
def llFrameAnisotropicExponentialCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rates : Fin frame.count → Real) :
    LLGeneratingFrameCurve period hPeriod frame where
  toFrame t :=
    llAnisotropicScaleGeneratingFrame period hPeriod frame rates t
  count_eq _ := rfl
  at_zero_vector point index := by
    simp [llAnisotropicScaleGeneratingFrame]

/-- Tangent realized by independent exponential rates. -/
def llFrameAnisotropicDirection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rates : Fin frame.count → Real) :
    LLFrameTangent period hPeriod frame :=
  fun index => rates index • llFrameBaseTangent period hPeriod frame index

theorem llFrameAnisotropicExponentialCurve_hasVelocity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (rates : Fin frame.count → Real) :
    (llFrameAnisotropicExponentialCurve period hPeriod frame rates).HasVelocity
      period hPeriod
      (llFrameAnisotropicDirection period hPeriod frame rates) := by
  intro point index
  have hScalar :
      HasDerivAt (fun t : Real => Real.exp (rates index * t))
        (rates index) 0 := by
    have hInner :
        HasDerivAt (fun t : Real => rates index * t) (rates index) 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul (rates index)
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (rates index * 0)).comp 0 hInner
  simpa [LLGeneratingFrameCurve.vectorAt,
    llFrameAnisotropicExponentialCurve,
    llAnisotropicScaleGeneratingFrame,
    llFrameAnisotropicDirection, llFrameBaseTangent] using
      hScalar.smul_const (frame.vectorAt point index)

/-- Smooth elementary direction adding a scalar multiple of `target` to
`source`. -/
def llFrameShearDirection
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count)
    (coefficient : CInfinityThroatScalarField period hPeriod) :
    LLFrameTangent period hPeriod frame :=
  fun index =>
    if index = source then
      throatScalarSmulGhost period hPeriod coefficient
        (llFrameBaseTangent period hPeriod frame target)
    else 0

@[simp]
theorem llFrameShearDirection_source
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count)
    (coefficient : CInfinityThroatScalarField period hPeriod) :
    llFrameShearDirection period hPeriod frame source target coefficient source =
      throatScalarSmulGhost period hPeriod coefficient
        (llFrameBaseTangent period hPeriod frame target) := by
  simp [llFrameShearDirection]

@[simp]
theorem llFrameShearDirection_apply_source
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count)
    (coefficient : CInfinityThroatScalarField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    llFrameShearDirection period hPeriod frame source target coefficient
        source point =
      coefficient point • frame.vectorAt point target := by
  simp [llFrameShearDirection, throatScalarSmulGhost, llFrameBaseTangent]

theorem llFrameShearDirection_apply_of_ne
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target index : Fin frame.count)
    (coefficient : CInfinityThroatScalarField period hPeriod)
    (hIndex : index ≠ source)
    (point : EffectiveThroat period hPeriod) :
    llFrameShearDirection period hPeriod frame source target coefficient
        index point = 0 := by
  simp [llFrameShearDirection, hIndex]

/-- A transvection of one generator by another preserves the generated
submodule for every parameter. -/
def llShearGeneratingFrame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count) (hDistinct : target ≠ source)
    (coefficient : CInfinityThroatScalarField period hPeriod) (t : Real) :
    SmoothThroatGeneratingFrame period hPeriod where
  count := frame.count
  vectorAt point index :=
    frame.vectorAt point index +
      t • llFrameShearDirection period hPeriod frame source target
        coefficient index point
  spansAt point := by
    let shearSet : Set
        (TangentSpace throatCoverModelWithCorners point) :=
      Set.range (fun index : Fin frame.count =>
        frame.vectorAt point index +
          t • llFrameShearDirection period hPeriod frame source target
            coefficient index point)
    apply top_unique
    rw [← frame.spansAt point]
    apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    by_cases hIndex : index = source
    · subst index
      have hSource :
          frame.vectorAt point source +
              t • llFrameShearDirection period hPeriod frame source target
                coefficient source point ∈
            Submodule.span Real shearSet :=
        Submodule.subset_span ⟨source, rfl⟩
      have hTarget :
          frame.vectorAt point target ∈ Submodule.span Real shearSet := by
        have hMember : frame.vectorAt point target +
              t • llFrameShearDirection period hPeriod frame source target
                coefficient target point ∈
            Submodule.span Real shearSet :=
          Submodule.subset_span ⟨target, rfl⟩
        simpa [llFrameShearDirection_apply_of_ne,
          hDistinct] using hMember
      have hCombination :=
        (Submodule.span Real shearSet).sub_mem hSource
          ((Submodule.span Real shearSet).smul_mem
            (t * coefficient point) hTarget)
      simpa [llFrameShearDirection_apply_source, throatScalarSmulGhost,
        llFrameBaseTangent, smul_smul] using hCombination
    · have hMember : frame.vectorAt point index +
            t • llFrameShearDirection period hPeriod frame source target
              coefficient index point ∈
          Submodule.span Real shearSet :=
        Submodule.subset_span ⟨index, rfl⟩
      simpa [llFrameShearDirection_apply_of_ne, hIndex] using hMember
  contMDiff_vector index := by
    exact
      (llFrameBaseTangent period hPeriod frame index +
        t • llFrameShearDirection period hPeriod frame source target
          coefficient index).contMDiff

@[simp]
theorem llShearGeneratingFrame_vectorAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count) (hDistinct : target ≠ source)
    (coefficient : CInfinityThroatScalarField period hPeriod) (t : Real)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count) :
    (llShearGeneratingFrame period hPeriod frame source target hDistinct
      coefficient t).vectorAt point index =
      frame.vectorAt point index +
        t • llFrameShearDirection period hPeriod frame source target
          coefficient index point :=
  rfl

/-- Global affine shear curve of actual generating frames. -/
def llFrameShearCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count) (hDistinct : target ≠ source)
    (coefficient : CInfinityThroatScalarField period hPeriod) :
    LLGeneratingFrameCurve period hPeriod frame where
  toFrame t :=
    llShearGeneratingFrame period hPeriod frame source target hDistinct
      coefficient t
  count_eq _ := rfl
  at_zero_vector point index := by
    simp [llShearGeneratingFrame]

theorem llFrameShearCurve_hasVelocity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (source target : Fin frame.count) (hDistinct : target ≠ source)
    (coefficient : CInfinityThroatScalarField period hPeriod) :
    (llFrameShearCurve period hPeriod frame source target hDistinct
      coefficient).HasVelocity period hPeriod
        (llFrameShearDirection period hPeriod frame source target
          coefficient) := by
  intro point index
  have hDerivative :=
    ((hasDerivAt_id (0 : Real)).smul_const
      (llFrameShearDirection period hPeriod frame source target
        coefficient index point)).const_add (frame.vectorAt point index)
  simpa [LLGeneratingFrameCurve.vectorAt, llFrameShearCurve,
    llShearGeneratingFrame] using
      hDerivative.congr_deriv (one_smul Real _)

end

end P0EFTJanusMappingTorusLLGeneratingFrameElementaryFlows4D
end JanusFormal
