import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalHolonomicExactCoordinateVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalStereographicIntrinsicMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-! # Identification of the transported volume with the intrinsic holonomic metric

The product basis used for stereographic measure transport becomes the
time-first holonomic basis by a permutation. The concrete tensor pullback
therefore identifies the two metric determinants, including their density.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalHolonomicIntrinsicMetricVolume4D

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusCanonicalStereographicCoordinateTransport4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D
open P0EFTJanusCanonicalHolonomicStereographicInverse4D
open P0EFTJanusCanonicalHolonomicExactCoordinateVolume4D
open P0EFTJanusCanonicalStereographicIntrinsicMetric4D

private abbrev Coordinates := EuclideanSpace Real (Fin 3) × Real
private abbrev Vector4 := Fin 4 → Real
private abbrev ProductIndex := Fin 3 ⊕ Fin 1
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

private def productCoordinateBasis : Module.Basis ProductIndex Real Coordinates :=
  (EuclideanSpace.basisFun (Fin 3) Real).toBasis.prod (Module.Basis.singleton (Fin 1) Real)

private def productToHolonomicIndex : ProductIndex ≃ Fin 4 :=
  (Equiv.sumComm (Fin 3) (Fin 1)).trans finSumFinEquiv

private def stereographicProductBilin (point : Coordinates) :
    Coordinates →ₗ[Real] Coordinates →ₗ[Real] Real where
  toFun := fun first => {
    toFun := fun second =>
      (4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1, second.1⟫ - first.2 * second.2
    map_add' := by
      intro second third
      simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
      ring
    map_smul' := by
      intro scalar second
      change (4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1, scalar • second.1⟫ -
          first.2 * (scalar * second.2) =
        scalar * ((4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1, second.1⟫ - first.2 * second.2)
      rw [inner_smul_right]
      ring }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro third
    change (4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1 + second.1, third.1⟫ -
        (first.2 + second.2) * third.2 =
      ((4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1, third.1⟫ - first.2 * third.2) +
        ((4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪second.1, third.1⟫ - second.2 * third.2)
    rw [inner_add_left]
    ring
  map_smul' := by
    intro scalar first
    apply LinearMap.ext
    intro second
    change (4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪scalar • first.1, second.1⟫ -
        (scalar * first.2) * second.2 =
      scalar * ((4 / (‖point.1‖ ^ 2 + 4)) ^ 2 * ⟪first.1, second.1⟫ - first.2 * second.2)
    simp only [inner_smul_left, conj_trivial]
    ring

private theorem stereographicProductBilin_matrix (point : Coordinates) :
    LinearMap.toMatrix₂ productCoordinateBasis productCoordinateBasis
        (stereographicProductBilin point) = stereographicAmbientLorentzMatrix point := by
  classical
  ext first second
  simp only [LinearMap.toMatrix₂_apply]
  rcases first with first | first <;> rcases second with second | second
  · by_cases hEqual : first = second
    · subst second
      simp [stereographicProductBilin, productCoordinateBasis, Module.Basis.prod_apply,
        stereographicAmbientLorentzMatrix, EuclideanSpace.basisFun_apply]
    · simp [stereographicProductBilin, productCoordinateBasis, Module.Basis.prod_apply,
        stereographicAmbientLorentzMatrix, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_left, hEqual]
  · simp [stereographicProductBilin, productCoordinateBasis, Module.Basis.prod_apply,
      stereographicAmbientLorentzMatrix]
  · simp [stereographicProductBilin, productCoordinateBasis, Module.Basis.prod_apply,
      stereographicAmbientLorentzMatrix]
  · have hEqual : first = second := Subsingleton.elim _ _
    subst second
    simp [stereographicProductBilin, productCoordinateBasis, Module.Basis.prod_apply,
      stereographicAmbientLorentzMatrix]

/-- Every entry of the transported matrix is the literal Lorentz pairing
of the differentiated product basis vectors. -/
theorem stereographicTransitionLorentzMatrix_pairing
    (transition : Coordinates → Coordinates) (point : Coordinates)
    (first second : ProductIndex) :
    stereographicTransitionLorentzMatrix transition point first second =
      (4 / (‖(transition point).1‖ ^ 2 + 4)) ^ 2 *
        ⟪(fderiv Real transition point (productCoordinateBasis first)).1,
          (fderiv Real transition point (productCoordinateBasis second)).1⟫ -
        (fderiv Real transition point (productCoordinateBasis first)).2 *
          (fderiv Real transition point (productCoordinateBasis second)).2 := by
  let derivative := (fderiv Real transition point).toLinearMap
  have hMatrix := LinearMap.toMatrix₂_compl₁₂
    productCoordinateBasis productCoordinateBasis productCoordinateBasis productCoordinateBasis
    (stereographicProductBilin (transition point)) derivative derivative
  rw [stereographicProductBilin_matrix] at hMatrix
  have hEntry := congrArg (fun matrix => matrix first second) hMatrix
  simp only [LinearMap.toMatrix₂_apply, LinearMap.compl₁₂_apply] at hEntry
  exact hEntry.symm

private theorem productCoordinateBasis_holonomic (index : ProductIndex) :
    holonomicCoordinateEquiv (productCoordinateBasis index) =
      Pi.single (productToHolonomicIndex index) 1 := by
  classical
  funext component
  rcases index with index | index
  · fin_cases index <;> fin_cases component <;>
      norm_num [holonomicCoordinateEquiv_apply, holonomicVectorCoefficient,
        productCoordinateBasis, Module.Basis.prod_apply, productToHolonomicIndex,
        finSumFinEquiv, EuclideanSpace.basisFun_apply, Pi.single_apply] <;>
      first | rfl | decide
  · fin_cases index; fin_cases component <;>
      norm_num [holonomicCoordinateEquiv_apply, holonomicVectorCoefficient,
        productCoordinateBasis, Module.Basis.prod_apply, productToHolonomicIndex,
        finSumFinEquiv, EuclideanSpace.basisFun_apply, Pi.single_apply] <;>
      first | rfl | decide

private theorem reparametrizedTransition_fderiv_basis
    (transition : Vector4 → Coordinates) (current : Vector4)
    (hDerivative : DifferentiableAt Real transition current) (index : ProductIndex) :
    fderiv Real (transition ∘ holonomicCoordinateEquiv)
        (holonomicCoordinateEquiv.symm current) (productCoordinateBasis index) =
      fderiv Real transition current (Pi.single (productToHolonomicIndex index) 1) := by
  have hChain : HasFDerivAt (transition ∘ holonomicCoordinateEquiv)
      ((fderiv Real transition current).comp holonomicCoordinateEquiv.toContinuousLinearMap)
      (holonomicCoordinateEquiv.symm current) := by
    have hOuter : HasFDerivAt transition (fderiv Real transition current)
        (holonomicCoordinateEquiv (holonomicCoordinateEquiv.symm current)) := by
      simpa only [holonomicCoordinateEquiv.apply_symm_apply] using hDerivative.hasFDerivAt
    exact hOuter.comp (holonomicCoordinateEquiv.symm current) holonomicCoordinateEquiv.hasFDerivAt
  rw [hChain.fderiv, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv Real transition current) (productCoordinateBasis_holonomic index)

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The concrete transported matrix is the intrinsic holonomic matrix with
its time entry moved from first to last. -/
theorem holonomicInverseTransitionLorentzMatrix_eq_intrinsic_submatrix
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (current : Vector4)
    (hCurrent : current ∈ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) :
    let inverse := holonomicToStereographicLocalInverse
      period hPeriod patch coordinate shift pole point hPoint
    stereographicTransitionLorentzMatrix (inverse ∘ holonomicCoordinateEquiv)
        (holonomicCoordinateEquiv.symm current) =
      (localMetricMatrix period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch current).submatrix productToHolonomicIndex productToHolonomicIndex := by
  let inverse := holonomicToStereographicLocalInverse
    period hPeriod patch coordinate shift pole point hPoint
  have hDerivative : DifferentiableAt Real inverse current :=
    ((holonomicToStereographicLocalInverse_contDiffOn
      period hPeriod patch coordinate shift pole point hPoint).contDiffAt
      ((holonomicToStereographicDomain_isOpen
        period hPeriod patch coordinate shift pole point hPoint).mem_nhds hCurrent)).differentiableAt
      (by simp)
  have hModel : mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      inverse current = fderiv Real inverse current := by
    have hSelf : mfderiv (modelWithCornersSelf Real Vector4)
        (modelWithCornersSelf Real Coordinates) inverse current = fderiv Real inverse current := by
      rw [mfderiv_eq_fderiv]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hSelf
    exact hSelf
  ext first second
  change stereographicTransitionLorentzMatrix (inverse ∘ holonomicCoordinateEquiv)
      (holonomicCoordinateEquiv.symm current) first second =
    localMetricMatrix period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch current (productToHolonomicIndex first) (productToHolonomicIndex second)
  rw [stereographicTransitionLorentzMatrix_pairing,
    reparametrizedTransition_fderiv_basis inverse current hDerivative first,
    reparametrizedTransition_fderiv_basis inverse current hDerivative second]
  simp only [Function.comp_apply, holonomicCoordinateEquiv.apply_symm_apply]
  have hMetric := canonical_holonomic_stereographic_intrinsic_metric_gate
    period hPeriod patch coordinate shift pole point hPoint current hCurrent
    (productToHolonomicIndex first) (productToHolonomicIndex second)
  change localMetricMatrix period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch current (productToHolonomicIndex first) (productToHolonomicIndex second) =
    (4 / (‖(inverse current).1‖ ^ 2 + 4)) ^ 2 *
      ⟪(mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners inverse current
          (Pi.single (productToHolonomicIndex first) 1)).1,
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners inverse current
          (Pi.single (productToHolonomicIndex second) 1)).1⟫ -
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners inverse current
          (Pi.single (productToHolonomicIndex first) 1)).2 *
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners inverse current
          (Pi.single (productToHolonomicIndex second) 1)).2 at hMetric
  rw [hModel] at hMetric
  exact hMetric.symm

/-- The exact measured density of Gate575 is the intrinsic holonomic metric
density on the actual inverse overlap of Gate573. -/
theorem holonomicStereographicTransitionMetricDensity_eq_intrinsic
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (current : Vector4)
    (hCurrent : current ∈ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) :
    holonomicStereographicTransitionMetricDensity
        (holonomicToStereographicLocalInverse
          period hPeriod patch coordinate shift pole point hPoint) current =
      ENNReal.ofReal (Real.sqrt |(localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current).det|) := by
  rw [holonomicStereographicTransitionMetricDensity,
    holonomicInverseTransitionLorentzMatrix_eq_intrinsic_submatrix
      period hPeriod patch coordinate shift pole point hPoint current hCurrent,
    Matrix.det_submatrix_equiv_self]

/-- The canonical quotient measure has exactly the intrinsic metric density
on every measurable subset of the constructed holonomic neighborhood. -/
theorem holonomicCoordinateMap_image_intrinsic_volume
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole)
    (subset : Set Vector4) (hSubset : MeasurableSet subset)
    (hInDomain : subset ⊆ holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
      ∫⁻ current in subset, ENNReal.ofReal (localMetricVolumeFactor period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current) := by
  have hSmooth := holonomicToStereographicLocalInverse_contDiffOn
    period hPeriod patch coordinate shift pole point hPoint
  have hOpen := holonomicToStereographicDomain_isOpen
    period hPeriod patch coordinate shift pole point hPoint
  have hVolume := holonomicCoordinateMap_image_volume period hPeriod patch shift pole
    (holonomicToStereographicLocalInverse
      period hPeriod patch coordinate shift pole point hPoint) subset hSubset
    (fun current hCurrent =>
      (hSmooth.contDiffAt (hOpen.mem_nhds (hInDomain hCurrent))).differentiableAt (by simp))
    ((holonomicToStereographicLocalInverse_injOn
      period hPeriod patch coordinate shift pole point hPoint).mono hInDomain)
    (fun _ hCurrent => (hInDomain hCurrent).2.1)
    (fun current hCurrent => holonomicToStereographicLocalInverse_physical_agreement
      period hPeriod patch coordinate shift pole point hPoint current (hInDomain hCurrent))
  rw [hVolume]
  apply setLIntegral_congr_fun hSubset
  intro current hCurrent
  exact holonomicStereographicTransitionMetricDensity_eq_intrinsic
    period hPeriod patch coordinate shift pole point hPoint current (hInDomain hCurrent)

/-- The physical holonomic chart is injective on this exact volume neighborhood. -/
theorem holonomicCoordinateMap_injOn_inverse_domain
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (shift : Real) (pole : StandardSphere) (point : Coordinates)
    (hPoint : point ∈ stereographicHolonomicOverlapDomain
      period hPeriod patch coordinate shift pole) :
    InjOn patch.coordinateMap (holonomicToStereographicDomain
      period hPeriod patch coordinate shift pole point hPoint) := by
  intro first hFirst second hSecond hEqual
  apply holonomicToStereographicLocalInverse_injOn
    period hPeriod patch coordinate shift pole point hPoint hFirst hSecond
  apply shiftedStereographicPhysicalMapAmbient_injOn_strip
    period hPeriod shift pole hFirst.2.1 hSecond.2.1
  rw [holonomicToStereographicLocalInverse_physical_agreement
    period hPeriod patch coordinate shift pole point hPoint first hFirst,
    holonomicToStereographicLocalInverse_physical_agreement
    period hPeriod patch coordinate shift pole point hPoint second hSecond]
  exact hEqual

/-- Every coordinate of every holonomic chart has an open neighborhood with
the exact canonical metric-volume formula, with no measure-agreement hypothesis. -/
theorem canonical_holonomic_intrinsic_metric_volume_gate
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    ∃ domain : Set Vector4, coordinate ∈ domain ∧ IsOpen domain ∧ InjOn patch.coordinateMap domain ∧
      ∀ subset : Set Vector4, MeasurableSet subset → subset ⊆ domain →
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
          ∫⁻ current in subset, ENNReal.ofReal (localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current) := by
  obtain ⟨shift, pole, point, hPoint, hBase, _⟩ :=
    canonical_holonomic_stereographic_overlap_gate period hPeriod patch coordinate
  refine ⟨holonomicToStereographicDomain
    period hPeriod patch coordinate shift pole point hPoint, ?_,
    holonomicToStereographicDomain_isOpen
      period hPeriod patch coordinate shift pole point hPoint,
    holonomicCoordinateMap_injOn_inverse_domain
      period hPeriod patch coordinate shift pole point hPoint, ?_⟩
  · have hMem := holonomicToStereographicDomain_base_mem
      period hPeriod patch coordinate shift pole point hPoint
    rwa [hBase] at hMem
  · exact fun subset hSubset hInDomain => holonomicCoordinateMap_image_intrinsic_volume
      period hPeriod patch coordinate shift pole point hPoint subset hSubset hInDomain

end
end P0EFTJanusCanonicalHolonomicIntrinsicMetricVolume4D
end JanusFormal
