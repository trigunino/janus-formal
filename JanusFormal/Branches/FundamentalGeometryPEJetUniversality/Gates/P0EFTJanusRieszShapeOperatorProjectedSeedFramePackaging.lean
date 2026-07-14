import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenCanonicalTransition

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition

universe u v w x y

variable {Base : Type w} {Model : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Model]

variable {κ : Type x} [Fintype κ]

structure OrthonormalFrameSynthesisOn (domain : Set Base) where
  coordinateBasis : Basis κ ℝ Model
  coordinateBasis_orthonormal : Orthonormal ℝ coordinateBasis
  vector : κ → Base → Ambient
  vector_orthonormal :
    ∀ base, base ∈ domain → Orthonormal ℝ (fun k => vector k base)
  synthesis : Base → Model →L[ℝ] Ambient
  synthesis_basis :
    ∀ base k, synthesis base (coordinateBasis k) = vector k base
  synthesis_contDiffOn : ContDiffOn ℝ ∞ synthesis domain
  fallback : Model →ₗᵢ[ℝ] Ambient

def synthesizedIsometryValue
    {domain : Set Base}
    (data : OrthonormalFrameSynthesisOn
      (Base := Base) (Model := Model) (Ambient := Ambient)
      (κ := κ) domain)
    (base : Base) : Model →ₗᵢ[ℝ] Ambient := by
  classical
  by_cases hValid : base ∈ domain
  · have hImage : Orthonormal ℝ
        ((data.synthesis base).toLinearMap ∘ data.coordinateBasis) := by
      simpa [Function.comp_def, data.synthesis_basis] using
        data.vector_orthonormal base hValid
    exact (data.synthesis base).toLinearMap.isometryOfOrthonormal
      data.coordinateBasis_orthonormal hImage
  · exact data.fallback

theorem synthesizedIsometryValue_toContinuousLinearMap
    {domain : Set Base}
    (data : OrthonormalFrameSynthesisOn
      (Base := Base) (Model := Model) (Ambient := Ambient)
      (κ := κ) domain)
    (base : Base) (hValid : base ∈ domain) :
    (synthesizedIsometryValue data base).toContinuousLinearMap =
      data.synthesis base := by
  apply ContinuousLinearMap.ext
  intro vector
  change synthesizedIsometryValue data base vector = data.synthesis base vector
  rw [synthesizedIsometryValue]
  simp only [hValid, ↓reduceDIte]
  rfl

def OrthonormalFrameSynthesisOn.toSmoothIsometricFrameFamilyOn
    {domain : Set Base}
    (data : OrthonormalFrameSynthesisOn
      (Base := Base) (Model := Model) (Ambient := Ambient)
      (κ := κ) domain) :
    SmoothIsometricFrameFamilyOn Base Model Ambient domain where
  frame := synthesizedIsometryValue data
  forward_contDiffOn := by
    apply data.synthesis_contDiffOn.congr
    intro base hValid
    exact synthesizedIsometryValue_toContinuousLinearMap data base hValid

theorem OrthonormalFrameSynthesisOn.frame_basis
    {domain : Set Base}
    (data : OrthonormalFrameSynthesisOn
      (Base := Base) (Model := Model) (Ambient := Ambient)
      (κ := κ) domain)
    (base : Base) (hValid : base ∈ domain) (k : κ) :
    data.toSmoothIsometricFrameFamilyOn.frame base
        (data.coordinateBasis k) =
      data.vector k base := by
  change synthesizedIsometryValue data base (data.coordinateBasis k) =
    data.vector k base
  rw [synthesizedIsometryValue]
  simp only [hValid, ↓reduceDIte]
  exact data.synthesis_basis base k

def projectedSeedSynthesisLinearMap
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) : Model →ₗ[ℝ] Ambient :=
  coordinateBasis.constr ℝ
    (fun k => projectedSeedNormalFrame tangentFrame charts chart k base)

def projectedSeedSynthesisCLM
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) : Model →L[ℝ] Ambient :=
  (projectedSeedSynthesisLinearMap coordinateBasis tangentFrame charts chart base).toContinuousLinearMap

@[simp]
theorem projectedSeedSynthesisCLM_basis
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) (k : κ) :
    projectedSeedSynthesisCLM coordinateBasis tangentFrame charts chart base
        (coordinateBasis k) =
      projectedSeedNormalFrame tangentFrame charts chart k base := by
  unfold projectedSeedSynthesisCLM projectedSeedSynthesisLinearMap
  exact coordinateBasis.constr_basis ℝ _ k

def projectedSeedSmoothIsometricFrameFamilyOn
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (fallback : Model →ₗᵢ[ℝ] Ambient)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart)
    (hSynthesisSmooth :
      ContDiffOn ℝ ∞
        (projectedSeedSynthesisCLM coordinateBasis tangentFrame charts chart)
        {base | projectedSeedChartValid tangentFrame charts chart base}) :
    SmoothIsometricFrameFamilyOn Base Model Ambient
      {base | projectedSeedChartValid tangentFrame charts chart base} :=
  OrthonormalFrameSynthesisOn.toSmoothIsometricFrameFamilyOn
    ({ coordinateBasis := coordinateBasis
       coordinateBasis_orthonormal := hCoordinateOrthonormal
       vector := fun k => projectedSeedNormalFrame tangentFrame charts chart k
       vector_orthonormal := by
         intro base hValid
         exact projectedSeedNormalFrame_orthonormal
           tangentFrame charts chart base hValid
       synthesis := projectedSeedSynthesisCLM
         coordinateBasis tangentFrame charts chart
       synthesis_basis := projectedSeedSynthesisCLM_basis
         coordinateBasis tangentFrame charts chart
       synthesis_contDiffOn := hSynthesisSmooth
       fallback := fallback } :
      OrthonormalFrameSynthesisOn
        (Base := Base) (Model := Model) (Ambient := Ambient) (κ := κ)
        {base | projectedSeedChartValid tangentFrame charts chart base})

theorem projectedSeedSmoothIsometricFrameFamilyOn_range
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (fallback : Model →ₗᵢ[ℝ] Ambient)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart)
    (hSynthesisSmooth :
      ContDiffOn ℝ ∞
        (projectedSeedSynthesisCLM coordinateBasis tangentFrame charts chart)
        {base | projectedSeedChartValid tangentFrame charts chart base})
    (base : Base)
    (hValid : projectedSeedChartValid tangentFrame charts chart base) :
    normalFrameRange
        ((projectedSeedSmoothIsometricFrameFamilyOn coordinateBasis
          hCoordinateOrthonormal fallback tangentFrame charts chart
          hSynthesisSmooth).frame base) =
      Submodule.span ℝ
        (Set.range
          (fun k => projectedSeedNormalFrame tangentFrame charts chart k base)) := by
  unfold normalFrameRange
  have hFrame :
      ((projectedSeedSmoothIsometricFrameFamilyOn coordinateBasis
        hCoordinateOrthonormal fallback tangentFrame charts chart
        hSynthesisSmooth).frame base).toLinearMap =
        projectedSeedSynthesisLinearMap
          coordinateBasis tangentFrame charts chart base := by
    apply LinearMap.ext
    intro vector
    unfold projectedSeedSmoothIsometricFrameFamilyOn
    change synthesizedIsometryValue
      ({ coordinateBasis := coordinateBasis
         coordinateBasis_orthonormal := hCoordinateOrthonormal
         vector := fun k => projectedSeedNormalFrame tangentFrame charts chart k
         vector_orthonormal := by
           intro point hPoint
           exact projectedSeedNormalFrame_orthonormal
             tangentFrame charts chart point hPoint
         synthesis := projectedSeedSynthesisCLM
           coordinateBasis tangentFrame charts chart
         synthesis_basis := projectedSeedSynthesisCLM_basis
           coordinateBasis tangentFrame charts chart
         synthesis_contDiffOn := hSynthesisSmooth
         fallback := fallback } :
        OrthonormalFrameSynthesisOn
          (Base := Base) (Model := Model) (Ambient := Ambient) (κ := κ)
          {point | projectedSeedChartValid tangentFrame charts chart point})
      base vector = projectedSeedSynthesisCLM coordinateBasis tangentFrame charts chart base vector
    have hCLM := synthesizedIsometryValue_toContinuousLinearMap
      ({ coordinateBasis := coordinateBasis
         coordinateBasis_orthonormal := hCoordinateOrthonormal
         vector := fun k => projectedSeedNormalFrame tangentFrame charts chart k
         vector_orthonormal := by
           intro point hPoint
           exact projectedSeedNormalFrame_orthonormal
             tangentFrame charts chart point hPoint
         synthesis := projectedSeedSynthesisCLM
           coordinateBasis tangentFrame charts chart
         synthesis_basis := projectedSeedSynthesisCLM_basis
           coordinateBasis tangentFrame charts chart
         synthesis_contDiffOn := hSynthesisSmooth
         fallback := fallback } :
        OrthonormalFrameSynthesisOn
          (Base := Base) (Model := Model) (Ambient := Ambient) (κ := κ)
          {point | projectedSeedChartValid tangentFrame charts chart point})
      base hValid
    exact congrArg (fun operator : Model →L[ℝ] Ambient => operator vector) hCLM
  rw [hFrame]
  exact coordinateBasis.constr_range ℝ

structure ProjectedSeedFramePackagingStatus where
  coordinateModelBasisChosen : Prop
  coordinateBasisOrthonormal : Prop
  finiteSynthesisOperatorConstructed : Prop
  synthesisOperatorContDiffOnProved : Prop
  pointwiseIsometryPackaged : Prop
  frameRangeIdentified : Prop
  connectedToOpenCanonicalTransitions : Prop

def projectedSeedFramePackagingClosed
    (s : ProjectedSeedFramePackagingStatus) : Prop :=
  s.coordinateModelBasisChosen ∧
  s.coordinateBasisOrthonormal ∧
  s.finiteSynthesisOperatorConstructed ∧
  s.synthesisOperatorContDiffOnProved ∧
  s.pointwiseIsometryPackaged ∧
  s.frameRangeIdentified ∧
  s.connectedToOpenCanonicalTransitions

theorem missing_synthesis_smoothness_blocks_frame_packaging
    (s : ProjectedSeedFramePackagingStatus)
    (hMissing : Not s.synthesisOperatorContDiffOnProved) :
    Not (projectedSeedFramePackagingClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
end JanusFormal
