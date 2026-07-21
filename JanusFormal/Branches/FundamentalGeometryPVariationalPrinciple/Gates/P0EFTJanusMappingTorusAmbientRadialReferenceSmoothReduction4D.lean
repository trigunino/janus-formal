import Mathlib.Analysis.Calculus.ContDiff.Operations
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientRadialReferencePointwiseReduction4D

/-!
# Smooth radial reference reduction of the ambient atlas

The true radial frame is the derivative of the genuine ambient immersion in
each real cover chart.  Its coordinate family and inverse family are smooth;
the resulting orthonormal reduction has the canonical locally constant `O(4)`
overlap selected by the actual winding.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D
open P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D
open P0EFTJanusMappingTorusAmbientAtlasRadialReferenceTransition4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D
open P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientRadialReferencePointwiseReduction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientCoordinates := ModelProd EuclideanR4 Real
private local instance ambientNormedAddCommGroup :
    NormedAddCommGroup AmbientCoordinates := inferInstance
private local instance ambientNormedSpace :
    NormedSpace Real AmbientCoordinates := inferInstance
private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod
private local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private def localAmbientMap (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientCoordinates :=
  coverAmbientMap period hPeriod ((chartAt CoverModel anchor).symm coordinate)

private def radialFrameFormula (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  stableRadialReferenceEquiv
    ((mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
        (localAmbientMap period hPeriod anchor) input.1 input.2).1 +
      (mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
        (localAmbientMap period hPeriod anchor) input.1 input.2).2 •
        (localAmbientMap period hPeriod anchor input.1).1)

private theorem radialFrameFormula_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞ (radialFrameFormula period hPeriod anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  have hQuotient : input.1 ∈
      (ambientQuotientLocalChart period hPeriod anchor).target := hInput.1
  have hCoverTarget : input.1 ∈ (chartAt CoverModel anchor).target := by
    simp only [ambientQuotientLocalChart, mfld_simps] at hQuotient
    exact hQuotient.1
  have hChartAt : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      (chartAt CoverModel anchor).symm input.1 :=
    contMDiffOn_chart_symm.contMDiffAt
      ((chartAt CoverModel anchor).open_target.mem_nhds hCoverTarget)
  have hMapAt : ContMDiffAt coverModelWithCorners
      𝓘(Real, AmbientCoordinates) ∞
      (localAmbientMap period hPeriod anchor) input.1 :=
    (coverAmbientMap_contMDiff period hPeriod
      ((chartAt CoverModel anchor).symm input.1)).comp input.1 hChartAt
  have hDerivativeAt := hMapAt.mfderiv_const (m := ∞) (by simp)
  have hDerivativeProduct : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates →L[Real] AmbientCoordinates) ∞
      (fun pair => inTangentCoordinates coverModelWithCorners
        𝓘(Real, AmbientCoordinates) id (localAmbientMap period hPeriod anchor)
        (mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
          (localAmbientMap period hPeriod anchor)) input.1 pair.1) input :=
    hDerivativeAt.comp input contMDiffAt_fst
  have hSnd : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates) ∞
      (fun pair : CoverModel × CoverCoordinates => pair.2) input :=
    (((contMDiff_fst.comp contMDiff_snd).prodMk_space
      (contMDiff_snd.comp contMDiff_snd)) |>.contMDiffAt)
  have hApplied := hDerivativeProduct.clm_apply hSnd
  have hMapProduct : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, AmbientCoordinates) ∞
      (fun pair => localAmbientMap period hPeriod anchor pair.1) input :=
    hMapAt.comp input contMDiffAt_fst
  have hAppliedFst := ContDiff.comp_contMDiffAt
    (ContinuousLinearMap.fst Real EuclideanR4 Real).contDiff hApplied
  have hAppliedSnd := ContDiff.comp_contMDiffAt
    (ContinuousLinearMap.snd Real EuclideanR4 Real).contDiff hApplied
  have hMapFst := ContDiff.comp_contMDiffAt
    (ContinuousLinearMap.fst Real EuclideanR4 Real).contDiff hMapProduct
  have hRadial := hAppliedFst.add (hAppliedSnd.smul hMapFst)
  have hFinal := stableRadialReferenceEquiv.contDiff.contMDiff.contMDiffAt.comp
    input hRadial
  have hFirst := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    (hFinal.contMDiffWithinAt (s := chartTangentDomain period hPeriod anchor))
  have hSecond := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    (hFinal.contMDiffWithinAt (s := chartTangentDomain period hPeriod anchor))
  convert hFirst.prodMk hSecond using 1
  funext current
  simp only [radialFrameFormula, localAmbientMap,
    inTangentCoordinates_model_space, Function.comp_def, Pi.add_apply]
  exact (Prod.eta _).symm

private theorem radialFrameFormula_eq
    (anchor : AmbientCover period hPeriod) (input : CoverModel × CoverCoordinates)
    (hInput : input ∈ chartTangentDomain period hPeriod anchor) :
    radialFrameFormula period hPeriod anchor input =
      ambientRadialReferenceAtlasFrame period hPeriod anchor input.1 input.2 := by
  have hQuotient : input.1 ∈
      (ambientQuotientLocalChart period hPeriod anchor).target := hInput.1
  have hCoverTarget : input.1 ∈ (chartAt CoverModel anchor).target := by
    have h := hQuotient
    simp only [ambientQuotientLocalChart, mfld_simps] at h
    exact h.1
  have hChart : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (chartAt CoverModel anchor).symm input.1 :=
    ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
      ((chartAt CoverModel anchor).open_target.mem_nhds hCoverTarget)).mdifferentiableAt
      (by simp)
  have hAmbient : MDifferentiableAt coverModelWithCorners
      𝓘(Real, AmbientCoordinates) (coverAmbientMap period hPeriod)
      ((chartAt CoverModel anchor).symm input.1) :=
    (coverAmbientMap_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply input.1 hAmbient hChart input.2
  simp only [Function.comp_def] at hChain
  change mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
      (localAmbientMap period hPeriod anchor) input.1 input.2 = _ at hChain
  simp only [ambientRadialReferenceAtlasFrame, dif_pos hQuotient]
  change radialFrameFormula period hPeriod anchor input =
    stableRadialReferenceEquiv
      (genuineStableRadialTangentEquiv period hPeriod
        ((chartAt CoverModel anchor).symm input.1)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (chartAt CoverModel anchor).symm input.1 input.2))
  rw [genuineStableRadialTangentEquiv_apply]
  unfold radialFrameFormula
  rw [hChain]
  rfl

private def radialOperator (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientCoordinates →L[Real] EuclideanR4 :=
  (ContinuousLinearMap.fst Real EuclideanR4 Real) +
    (ContinuousLinearMap.snd Real EuclideanR4 Real).smulRight
      (localAmbientMap period hPeriod anchor coordinate).1

private def radialFrameCLMFormula (anchor : AmbientCover period hPeriod)
    (base coordinate : CoverModel) : CoverCoordinates →L[Real] CoverCoordinates :=
  stableRadialReferenceEquiv.toContinuousLinearMap.comp
    ((radialOperator period hPeriod anchor coordinate).comp
      (inTangentCoordinates coverModelWithCorners 𝓘(Real, AmbientCoordinates)
        id (localAmbientMap period hPeriod anchor)
        (mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
          (localAmbientMap period hPeriod anchor)) base coordinate))

private theorem radialFrameCLMFormula_apply
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (vector : CoverCoordinates) :
    radialFrameCLMFormula period hPeriod anchor coordinate coordinate vector =
      radialFrameFormula period hPeriod anchor (coordinate, vector) := by
  unfold radialFrameCLMFormula radialOperator radialFrameFormula
  simp only [inTangentCoordinates_model_space, ContinuousLinearMap.comp_apply]
  change stableRadialReferenceEquiv
      (((mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
        (localAmbientMap period hPeriod anchor) coordinate vector).1) +
       (mfderiv coverModelWithCorners 𝓘(Real, AmbientCoordinates)
        (localAmbientMap period hPeriod anchor) coordinate vector).2 •
          (localAmbientMap period hPeriod anchor coordinate).1) = _
  rfl

private theorem radialFrameCLMFormula_contMDiffAt
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    ContMDiffAt coverModelWithCorners
      𝓘(Real, CoverCoordinates →L[Real] CoverCoordinates) ∞
      (radialFrameCLMFormula period hPeriod anchor coordinate) coordinate := by
  have hCoverTarget : coordinate ∈ (chartAt CoverModel anchor).target := by
    have h := hCoordinate
    simp only [ambientQuotientLocalChart, mfld_simps] at h
    exact h.1
  have hChartAt : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      (chartAt CoverModel anchor).symm coordinate :=
    contMDiffOn_chart_symm.contMDiffAt
      ((chartAt CoverModel anchor).open_target.mem_nhds hCoverTarget)
  have hMapAt : ContMDiffAt coverModelWithCorners
      𝓘(Real, AmbientCoordinates) ∞
      (localAmbientMap period hPeriod anchor) coordinate :=
    (coverAmbientMap_contMDiff period hPeriod
      ((chartAt CoverModel anchor).symm coordinate)).comp coordinate hChartAt
  have hDerivativeAt := hMapAt.mfderiv_const (m := ∞) (by simp)
  have hMapFst := ContDiff.comp_contMDiffAt
    (ContinuousLinearMap.fst Real EuclideanR4 Real).contDiff hMapAt
  have hOperatorContDiff : ContDiff Real ∞
      (fun point : EuclideanR4 =>
        (ContinuousLinearMap.fst Real EuclideanR4 Real) +
          (ContinuousLinearMap.snd Real EuclideanR4 Real).smulRight point) :=
    contDiff_const.add (contDiff_const.smulRight contDiff_id)
  have hOperator := hOperatorContDiff.comp_contMDiffAt hMapFst
  have hRadialDerivative := hOperator.clm_comp hDerivativeAt
  have hStable : ContMDiffAt coverModelWithCorners
      𝓘(Real, EuclideanR4 →L[Real] CoverCoordinates) ∞
      (fun _ : CoverModel => stableRadialReferenceEquiv.toContinuousLinearMap)
      coordinate := contMDiffAt_const
  have hFrame := hStable.clm_comp hRadialDerivative
  convert hFrame using 1
  funext current
  rfl

private theorem radialFrameCLMFormula_eq_atlasFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    radialFrameCLMFormula period hPeriod anchor coordinate coordinate =
      (ambientRadialReferenceAtlasFrame period hPeriod anchor coordinate :
        CoverCoordinates →L[Real] CoverCoordinates) := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [radialFrameCLMFormula_apply]
  exact radialFrameFormula_eq period hPeriod anchor (coordinate, vector)
    ⟨hCoordinate, Set.mem_univ vector⟩

private theorem radialFrameCLMFormula_base_independent
    (anchor : AmbientCover period hPeriod) (first second : CoverModel) :
    radialFrameCLMFormula period hPeriod anchor first second =
      radialFrameCLMFormula period hPeriod anchor second second := by
  simp [radialFrameCLMFormula, inTangentCoordinates_model_space]

private theorem radialInverseFrameApplication_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (fun input =>
        (ambientRadialReferenceAtlasFrame period hPeriod anchor input.1).symm
          input.2)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  have hCoordinate : input.1 ∈
      (ambientQuotientLocalChart period hPeriod anchor).target := hInput.1
  have hForward := radialFrameCLMFormula_contMDiffAt period hPeriod anchor
    input.1 hCoordinate
  let frame := ambientRadialReferenceAtlasFrame period hPeriod anchor input.1
  have hFrameEq : radialFrameCLMFormula period hPeriod anchor input.1 input.1 =
      (frame : CoverCoordinates →L[Real] CoverCoordinates) :=
    radialFrameCLMFormula_eq_atlasFrame period hPeriod anchor input.1 hCoordinate
  have hInverseAt : ContDiffAt Real ∞ ContinuousLinearMap.inverse
      (radialFrameCLMFormula period hPeriod anchor input.1 input.1) := by
    rw [hFrameEq]
    exact contDiffAt_map_inverse frame
  have hInverse := hInverseAt.comp_contMDiffAt hForward
  have hSnd : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates) ∞
      (fun pair : CoverModel × CoverCoordinates => pair.2) input :=
    (((contMDiff_fst.comp contMDiff_snd).prodMk_space
      (contMDiff_snd.comp contMDiff_snd)) |>.contMDiffAt)
  have hInverseProduct : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates →L[Real] CoverCoordinates) ∞
      (fun pair => ContinuousLinearMap.inverse
        (radialFrameCLMFormula period hPeriod anchor input.1 pair.1)) input :=
    hInverse.comp input contMDiffAt_fst
  have hApplied := hInverseProduct.clm_apply hSnd
  have hAppliedWithin := hApplied.contMDiffWithinAt
    (s := chartTangentDomain period hPeriod anchor)
  have hActualSelf : ContMDiffWithinAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates) ∞
      (fun current =>
        (ambientRadialReferenceAtlasFrame period hPeriod anchor current.1).symm
          current.2)
      (chartTangentDomain period hPeriod anchor) input := by
    refine hAppliedWithin.congr ?_ ?_
    · intro current hCurrent
      have hCurrentCoordinate : current.1 ∈
          (ambientQuotientLocalChart period hPeriod anchor).target := hCurrent.1
      have hEq := radialFrameCLMFormula_eq_atlasFrame period hPeriod anchor
        current.1 hCurrentCoordinate
      rw [radialFrameCLMFormula_base_independent period hPeriod]
      rw [hEq]
      rw [ContinuousLinearMap.inverse_equiv]
      rfl
    ·
      rw [hFrameEq]
      rw [ContinuousLinearMap.inverse_equiv]
      rfl
  have hFirst := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hActualSelf
  have hSecond := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hActualSelf
  convert hFirst.prodMk hSecond using 1
  funext current
  simp only [Function.comp_def]
  exact (Prod.eta _).symm

private theorem radialForwardFrameApplication_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (fun input => ambientRadialReferenceAtlasFrame period hPeriod anchor
        input.1 input.2)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  refine (radialFrameFormula_contMDiffOn period hPeriod anchor input hInput).congr
    ?_ ?_
  · intro current hCurrent
    exact (radialFrameFormula_eq period hPeriod anchor current hCurrent).symm
  · exact (radialFrameFormula_eq period hPeriod anchor input hInput).symm

private def radialFormFormula (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : Real :=
  ‖(radialFrameFormula period hPeriod anchor input).1‖ ^ 2 +
    (radialFrameFormula period hPeriod anchor input).2 ^ 2

private theorem radialFormFormula_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Real) ∞
      (radialFormFormula period hPeriod anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  have hForward := radialFrameFormula_contMDiffOn period hPeriod anchor input hInput
  have hFirst : ContMDiffWithinAt
      (coverModelWithCorners.prod coverModelWithCorners) (𝓡 3) ∞
      (fun current => (radialFrameFormula period hPeriod anchor current).1)
      (chartTangentDomain period hPeriod anchor) input :=
    hForward.fst
  have hSecond : ContMDiffWithinAt
      (coverModelWithCorners.prod coverModelWithCorners) 𝓘(Real, Real) ∞
      (fun current => (radialFrameFormula period hPeriod anchor current).2)
      (chartTangentDomain period hPeriod anchor) input :=
    hForward.snd
  have hNorm := ContDiff.comp_contMDiffWithinAt
    (contDiff_norm_sq Real) hFirst
  have hSquare := hSecond.pow 2
  change ContMDiffWithinAt
    (coverModelWithCorners.prod coverModelWithCorners) 𝓘(Real, Real) ∞
    (fun current => ‖(radialFrameFormula period hPeriod anchor current).1‖ ^ 2 +
      (radialFrameFormula period hPeriod anchor current).2 ^ 2)
    (chartTangentDomain period hPeriod anchor) input
  exact hNorm.add hSquare

private theorem radialAtlasFormApplication_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Real) ∞
      (fun input => ambientRadialReferenceAtlasForm period hPeriod anchor
        input.1 input.2)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  refine (radialFormFormula_contMDiffOn period hPeriod anchor input hInput).congr
    ?_ ?_
  · intro current hCurrent
    change ambientCoverEuclideanQuadraticForm
      (ambientRadialReferenceAtlasFrame period hPeriod anchor current.1 current.2) =
      ‖(radialFrameFormula period hPeriod anchor current).1‖ ^ 2 +
        (radialFrameFormula period hPeriod anchor current).2 ^ 2
    rw [ambientCoverEuclideanQuadraticForm_apply,
      radialFrameFormula_eq period hPeriod anchor current hCurrent]
  · change ambientCoverEuclideanQuadraticForm
      (ambientRadialReferenceAtlasFrame period hPeriod anchor input.1 input.2) =
      ‖(radialFrameFormula period hPeriod anchor input).1‖ ^ 2 +
        (radialFrameFormula period hPeriod anchor input).2 ^ 2
    rw [ambientCoverEuclideanQuadraticForm_apply,
      radialFrameFormula_eq period hPeriod anchor input hInput]

private def canonicalRadialTransitionApplication
    (first second : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  (canonicalAmbientReferenceOrthogonalTransition period hPeriod first second
    input.1).toLinearEquiv input.2

private theorem canonicalRadialTransitionApplication_contMDiffOn
    (first second : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (canonicalRadialTransitionApplication period hPeriod first second)
      (transitionTangentDomain period hPeriod first second) := by
  intro input hInput
  have hCoordinate : input.1 ∈
      (ambientAtlasTransition period hPeriod first second).source := hInput.1
  let fixed :=
    (canonicalAmbientReferenceOrthogonalTransition period hPeriod first second
      input.1).toLinearEquiv.toContinuousLinearMap
  have hSnd : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates) ∞
      (fun pair : CoverModel × CoverCoordinates => pair.2) input :=
    (((contMDiff_fst.comp contMDiff_snd).prodMk_space
      (contMDiff_snd.comp contMDiff_snd)) |>.contMDiffAt)
  have hFixedSelf : ContMDiffAt
      (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, CoverCoordinates) ∞ (fun current => fixed current.2) input :=
    fixed.contDiff.contMDiff.contMDiffAt.comp input hSnd
  have hWinding := ambientTransitionWinding_eventuallyEq period hPeriod
    first second input.1 hCoordinate
  have hWindingProduct := hWinding.comp_tendsto continuousAt_fst
  have hApplication : Filter.EventuallyEq (nhds input)
      (canonicalRadialTransitionApplication period hPeriod first second)
      (fun current => fixed current.2) := by
    filter_upwards [hWindingProduct] with current hCurrent
    have hCurrent' : ambientTransitionWinding period hPeriod first second
        current.1 = ambientTransitionWinding period hPeriod first second input.1 := by
      simpa only [Function.comp_apply] using hCurrent
    unfold canonicalRadialTransitionApplication fixed
    unfold canonicalAmbientReferenceOrthogonalTransition
    rw [hCurrent']
    rfl
  have hCanonicalSelf := hFixedSelf.congr_of_eventuallyEq hApplication
  have hCanonicalWithin := hCanonicalSelf.contMDiffWithinAt
    (s := transitionTangentDomain period hPeriod first second)
  have hFirst := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hCanonicalWithin
  have hSecond := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hCanonicalWithin
  convert hFirst.prodMk hSecond using 1
  funext current
  exact (Prod.eta _).symm

private theorem radialReductionTransitionApplication_contMDiffOn
    (first second : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (reductionOrthogonalTransitionApplication period hPeriod
        (ambientRadialReferenceOrthonormalAtlasReduction period hPeriod)
        first second)
      (transitionTangentDomain period hPeriod first second) := by
  intro input hInput
  refine (canonicalRadialTransitionApplication_contMDiffOn period hPeriod
    first second input hInput).congr ?_ ?_
  · intro current hCurrent
    have hCoordinate : current.1 ∈
        (ambientAtlasTransition period hPeriod first second).source := hCurrent.1
    simp only [reductionOrthogonalTransitionApplication, hCoordinate, dite_true]
    exact DFunLike.congr_fun
      (ambientRadialReferenceOrthogonalTransition_eq_canonical period hPeriod
        first second current.1 hCoordinate) current.2
  · have hCoordinate : input.1 ∈
        (ambientAtlasTransition period hPeriod first second).source := hInput.1
    simp only [reductionOrthogonalTransitionApplication, hCoordinate, dite_true]
    exact DFunLike.congr_fun
      (ambientRadialReferenceOrthogonalTransition_eq_canonical period hPeriod
        first second input.1 hCoordinate) input.2

/-- The inverse genuine radial frame is jointly smooth on every real chart. -/
theorem ambientRadialReferenceInverseFrame_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (fun input =>
        (ambientRadialReferenceAtlasFrame period hPeriod anchor input.1).symm
          input.2)
      (chartTangentDomain period hPeriod anchor) :=
  radialInverseFrameApplication_contMDiffOn period hPeriod anchor

/-- Smooth radial orthonormal reduction with the genuine canonical overlaps. -/
def ambientRadialReferenceContMDiffOrthonormalAtlasReduction :
    AmbientContMDiffOrthonormalAtlasReduction period hPeriod where
  toPointwise := ambientRadialReferenceOrthonormalAtlasReduction period hPeriod
  form_contMDiffOn := by
    intro anchor
    convert radialAtlasFormApplication_contMDiffOn period hPeriod anchor using 1
    funext input
    rfl
  frame_contMDiffOn := by
    intro anchor
    convert radialInverseFrameApplication_contMDiffOn period hPeriod anchor using 1
    funext input
    rfl
  transition_contMDiffOn :=
    radialReductionTransitionApplication_contMDiffOn period hPeriod

/-- The smooth reduction retains the exact canonical winding transition. -/
theorem ambientRadialReferenceSmoothOrthogonalTransition_eq_canonical
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientRadialReferenceContMDiffOrthonormalAtlasReduction period hPeriod
      |>.toPointwise.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv =
      (canonicalAmbientReferenceOrthogonalTransition period hPeriod
        first second coordinate).toLinearEquiv :=
  ambientRadialReferenceOrthogonalTransition_eq_canonical period hPeriod
    first second coordinate hCoordinate

end
end P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D
end JanusFormal
