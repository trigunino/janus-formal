import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricPullback4D
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Regularity of the physical metric in the incidence chart

The physical collar metric of Gate 1056 is built from a smooth Lorentz
metric and the derivative frame of an inverse incidence chart.  On the
valid chart target its coefficients, determinant, metric density, and
metric-volume current are differentiable.  This discharges the regularity
hypothesis in physical metric-divergence naturality from ordinary `C¹`
regularity of the current, without a warped-metric compatibility datum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricRegularity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricPullback4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Ambient coordinates converted to the model coordinates form a smooth
linear equivalence. -/
def programPT06AmbientCoverCoordinateEquiv :
    ProgramPT06AmbientCoordinate4 ≃L[Real] CoverCoordinates :=
  programPT06AmbientHolonomicEquiv.trans holonomicCoordinateEquiv.symm

@[simp] theorem programPT06AmbientCoverCoordinateEquiv_apply
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientCoverCoordinateEquiv coordinate =
      programPT06AmbientCoverCoordinate coordinate :=
  rfl

theorem programPT06AmbientCoverCoordinate_contMDiff :
    ContMDiff (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real CoverCoordinates) ∞
      programPT06AmbientCoverCoordinate := by
  exact holonomicCoordinateEquiv.symm.contDiff.contMDiff.comp
    programPT06AmbientHolonomicEquiv.contDiff.contMDiff

/-- Smooth inverse of the ambient-to-cover coordinate equivalence. -/
def programPT06AmbientCoverCoordinateInverse
    (coordinate : CoverCoordinates) : ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientHolonomicEquiv.symm
    (holonomicCoordinateEquiv coordinate)

theorem programPT06AmbientCoverCoordinateInverse_contMDiff :
    ContMDiff (modelWithCornersSelf Real CoverCoordinates)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
      programPT06AmbientCoverCoordinateInverse := by
  exact programPT06AmbientHolonomicEquiv.symm.contDiff.contMDiff.comp
    holonomicCoordinateEquiv.contDiff.contMDiff

/-- The ambient-to-cover linear equivalence, bundled using the coordinate
topologies selected by this development. -/
private def programPT06AmbientCoverCoordinatePartialDiffeomorph :
    PartialDiffeomorph
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real CoverCoordinates)
      ProgramPT06AmbientCoordinate4 CoverCoordinates ∞ where
  toPartialEquiv := {
    toFun := programPT06AmbientCoverCoordinate
    invFun := programPT06AmbientCoverCoordinateInverse
    source := Set.univ
    target := Set.univ
    map_source' := fun _ _ => Set.mem_univ _
    map_target' := fun _ _ => Set.mem_univ _
    left_inv' := by
      intro coordinate _
      unfold programPT06AmbientCoverCoordinate
        programPT06AmbientCoverCoordinateInverse
      rw [holonomicCoordinateEquiv.apply_symm_apply,
        programPT06AmbientHolonomicEquiv.symm_apply_apply]
    right_inv' := by
      intro coordinate _
      unfold programPT06AmbientCoverCoordinate
        programPT06AmbientCoverCoordinateInverse
      rw [programPT06AmbientHolonomicEquiv.apply_symm_apply,
        holonomicCoordinateEquiv.symm_apply_apply] }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun :=
    programPT06AmbientCoverCoordinate_contMDiff.contMDiffOn
  contMDiffOn_invFun :=
    programPT06AmbientCoverCoordinateInverse_contMDiff.contMDiffOn

/-- Coordinates on which the total inverse-chart representative has its
actual chart meaning. -/
def programPT06EffectiveBulkChartCoordinateDomain
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    Set ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientCoverCoordinate ⁻¹'
    (extChartAt coverModelWithCorners anchor).target

theorem programPT06EffectiveBulkChartCoordinateDomain_isOpen
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    IsOpen (programPT06EffectiveBulkChartCoordinateDomain
      period hPeriod anchor) :=
  (isOpen_extChartAt_target anchor).preimage
    continuous_programPT06AmbientCoverCoordinate

theorem programPT06EffectiveBulkChartPoint_contMDiffOn
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    ContMDiffOn
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners ∞
      (programPT06EffectiveBulkChartPoint period hPeriod anchor)
      (programPT06EffectiveBulkChartCoordinateDomain
        period hPeriod anchor) := by
  exact (contMDiffOn_extChartAt_symm anchor).comp
    programPT06AmbientCoverCoordinate_contMDiff.contMDiffOn
    (fun _ hCoordinate => hCoordinate)

/-- Constant coordinate-basis tangent input over ambient coordinate space. -/
def programPT06AmbientCoordinateBasisTangentInput
    (index : Fin 4) (coordinate : ProgramPT06AmbientCoordinate4) :
    TangentBundle
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      ProgramPT06AmbientCoordinate4 :=
  ⟨coordinate, programPT06AmbientCoordinateBasis index⟩

theorem programPT06AmbientCoordinateBasisTangentInput_contMDiff
    (index : Fin 4) :
    ContMDiff
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4).tangent ∞
      (programPT06AmbientCoordinateBasisTangentInput index) := by
  change ContMDiff
    (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4).tangent ∞
    ((tangentBundleModelSpaceDiffeomorph
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (⊤ : ℕ∞)).symm ∘
      fun coordinate : ProgramPT06AmbientCoordinate4 =>
        (coordinate, programPT06AmbientCoordinateBasis index))
  have hPair : ContMDiff
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real
        (ProgramPT06AmbientCoordinate4 × ProgramPT06AmbientCoordinate4)) ∞
      (fun coordinate : ProgramPT06AmbientCoordinate4 =>
        (coordinate, programPT06AmbientCoordinateBasis index)) :=
    (contMDiff_id
      (I := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (n := ∞)).prodMk_space
      (contMDiff_const
        (I := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (I' := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (n := ∞) (c := programPT06AmbientCoordinateBasis index))
  rw [modelWithCornersSelf_prod] at hPair
  exact (tangentBundleModelSpaceDiffeomorph
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (⊤ : ℕ∞)).symm.contMDiff.comp hPair

/-- The inverse-chart derivative frame is smooth wherever the inverse chart
is valid. -/
theorem programPT06EffectiveBulkChartTangentFrame_contMDiffOn
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (index : Fin 4) :
    ContMDiffOn
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners.tangent ∞
      (fun coordinate =>
        (⟨programPT06EffectiveBulkChartPoint
            period hPeriod anchor coordinate,
          programPT06EffectiveBulkChartTangentFrame
            period hPeriod anchor coordinate index⟩ :
          TangentBundle coverModelWithCorners
            (ProgramPT06EffectiveBulk period hPeriod)))
      (programPT06EffectiveBulkChartCoordinateDomain
        period hPeriod anchor) := by
  let domain := programPT06EffectiveBulkChartCoordinateDomain
    period hPeriod anchor
  let pointMap := programPT06EffectiveBulkChartPoint period hPeriod anchor
  let tangentInput :=
    programPT06AmbientCoordinateBasisTangentInput index
  have hPoint : ContMDiffOn
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners ∞ pointMap domain :=
    programPT06EffectiveBulkChartPoint_contMDiffOn
      period hPeriod anchor
  have hOpen : IsOpen domain :=
    programPT06EffectiveBulkChartCoordinateDomain_isOpen
      period hPeriod anchor
  have hTangentMap :=
    hPoint.contMDiffOn_tangentMapWithin
      (m := ∞) (by simp) hOpen.uniqueMDiffOn
  have hInput : ContMDiff
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4).tangent ∞
      tangentInput :=
    programPT06AmbientCoordinateBasisTangentInput_contMDiff index
  have hInputMaps : MapsTo tangentInput domain
      (Bundle.TotalSpace.proj ⁻¹' domain) := by
    intro coordinate hCoordinate
    exact hCoordinate
  have hComposed := hTangentMap.comp hInput.contMDiffOn hInputMaps
  apply hComposed.congr
  intro coordinate hCoordinate
  change
    ⟨pointMap coordinate,
        programPT06EffectiveBulkChartTangentFrame
          period hPeriod anchor coordinate index⟩ =
      tangentMapWithin
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        coverModelWithCorners pointMap domain (tangentInput coordinate)
  unfold tangentMapWithin tangentInput
    programPT06AmbientCoordinateBasisTangentInput
    programPT06EffectiveBulkChartTangentFrame
  rw [mfderivWithin_of_isOpen hOpen hCoordinate]

/-- Every physical metric coefficient is differentiable at a coordinate in
the valid inverse-chart domain. -/
theorem programPT06EffectiveBulkChartPhysicalMetricMatrix_apply_differentiableAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor)
    (first second : Fin 4) :
    DifferentiableAt Real
      (fun nearby =>
        programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor nearby first second)
      coordinate := by
  let domain := programPT06EffectiveBulkChartCoordinateDomain
    period hPeriod anchor
  let pointMap := programPT06EffectiveBulkChartPoint period hPeriod anchor
  have hPoint := programPT06EffectiveBulkChartPoint_contMDiffOn
    period hPeriod anchor
  have hTensor := metric.tensor.tensor.contMDiff.comp_contMDiffOn hPoint
  have hApplied := ContMDiffOn.clm_bundle_apply₂
    (𝕜 := Real) (B := ProgramPT06EffectiveBulk period hPeriod)
    (M := ProgramPT06AmbientCoordinate4)
    (IM := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    (IB := coverModelWithCorners)
    (F₁ := CoverCoordinates) (F₂ := CoverCoordinates) (F₃ := Real)
    (E₁ := fun point => TangentSpace coverModelWithCorners point)
    (E₂ := fun point => TangentSpace coverModelWithCorners point)
    (E₃ := fun _ : ProgramPT06EffectiveBulk period hPeriod => Real)
    (b := pointMap)
    (ψ := fun nearby => metric.tensor.tensor (pointMap nearby))
    (v := fun nearby =>
      programPT06EffectiveBulkChartTangentFrame
        period hPeriod anchor nearby first)
    (w := fun nearby =>
      programPT06EffectiveBulkChartTangentFrame
        period hPeriod anchor nearby second)
    hTensor
    (programPT06EffectiveBulkChartTangentFrame_contMDiffOn
      period hPeriod anchor first)
    (programPT06EffectiveBulkChartTangentFrame_contMDiffOn
      period hPeriod anchor second)
  have hCoordinates :=
    ((trivializationAt Real
      (Bundle.Trivial (ProgramPT06EffectiveBulk period hPeriod) Real)
      (pointMap coordinate)).contMDiffOn_iff
        (fun _ _ => by simp)).1 hApplied
  have hCoefficient : ContDiffOn Real ∞
      (fun nearby =>
        metric.tensor.tensor (pointMap nearby)
          (programPT06EffectiveBulkChartTangentFrame
            period hPeriod anchor nearby first)
          (programPT06EffectiveBulkChartTangentFrame
            period hPeriod anchor nearby second)) domain := by
    rw [← contMDiffOn_iff_contDiffOn]
    simpa [Bundle.Trivial.trivialization,
      Bundle.Trivial.homeomorphProd] using hCoordinates.2
  have hAt := hCoefficient.contDiffAt
    ((programPT06EffectiveBulkChartCoordinateDomain_isOpen
      period hPeriod anchor).mem_nhds hCoordinate)
  change DifferentiableAt Real (fun nearby =>
    metric.tensor.tensor (pointMap nearby)
      (programPT06EffectiveBulkChartTangentFrame
        period hPeriod anchor nearby first)
      (programPT06EffectiveBulkChartTangentFrame
        period hPeriod anchor nearby second)) coordinate
  exact hAt.differentiableAt (by simp)

/-- The complete matrix-valued physical metric is differentiable on the
valid inverse-chart domain. -/
theorem programPT06EffectiveBulkChartPhysicalMetricMatrix_differentiableAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    DifferentiableAt Real
      (programPT06EffectiveBulkChartPhysicalMetricMatrix
        period hPeriod metric anchor) coordinate := by
  apply differentiableAt_pi.mpr
  intro first
  apply differentiableAt_pi.mpr
  intro second
  exact
    programPT06EffectiveBulkChartPhysicalMetricMatrix_apply_differentiableAt
      period hPeriod metric anchor coordinate hCoordinate first second

/-- The extended chart, bundled with its smoothness at infinite order. -/
private def programPT06EffectiveBulkExtChartPartialDiffeomorph
    (anchor : ProgramPT06EffectiveBulk period hPeriod) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates)
      (ProgramPT06EffectiveBulk period hPeriod) CoverCoordinates ∞ where
  toPartialEquiv := extChartAt coverModelWithCorners anchor
  open_source := isOpen_extChartAt_source (I := coverModelWithCorners) anchor
  open_target := isOpen_extChartAt_target (I := coverModelWithCorners) anchor
  contMDiffOn_toFun := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt
      (I := coverModelWithCorners) (n := ∞) (x := anchor)
  contMDiffOn_invFun :=
    contMDiffOn_extChartAt_symm
      (I := coverModelWithCorners) (n := ∞) anchor

/-- The inverse-chart point map is locally a diffeomorphism at every valid
coordinate. -/
theorem programPT06EffectiveBulkChartPoint_isLocalDiffeomorphAt
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      coverModelWithCorners ∞
      (programPT06EffectiveBulkChartPoint period hPeriod anchor)
      coordinate := by
  have hLinear : IsLocalDiffeomorphAt
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real CoverCoordinates) ∞
      programPT06AmbientCoverCoordinate coordinate := by
    exact PartialDiffeomorph.isLocalDiffeomorphAt
      (I := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (J := modelWithCornersSelf Real CoverCoordinates)
      (M := ProgramPT06AmbientCoordinate4) (N := CoverCoordinates)
      (n := ∞) programPT06AmbientCoverCoordinatePartialDiffeomorph
      (Set.mem_univ coordinate)
  have hChart : IsLocalDiffeomorphAt
      (modelWithCornersSelf Real CoverCoordinates)
      coverModelWithCorners ∞
      (extChartAt coverModelWithCorners anchor).symm
      (programPT06AmbientCoverCoordinate coordinate) := by
    exact PartialDiffeomorph.isLocalDiffeomorphAt
      (I := modelWithCornersSelf Real CoverCoordinates)
      (J := coverModelWithCorners)
      (M := CoverCoordinates)
      (N := ProgramPT06EffectiveBulk period hPeriod) (n := ∞)
      (programPT06EffectiveBulkExtChartPartialDiffeomorph
        period hPeriod anchor).symm hCoordinate
  change IsLocalDiffeomorphAt
    (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    coverModelWithCorners ∞
    (fun nearby => (extChartAt coverModelWithCorners anchor).symm
      (programPT06AmbientCoverCoordinate nearby)) coordinate
  exact
    IsLocalDiffeomorphAt.comp
      (I := modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (J := modelWithCornersSelf Real CoverCoordinates)
      (K := coverModelWithCorners)
      (M := ProgramPT06AmbientCoordinate4) (N := CoverCoordinates)
      (P := ProgramPT06EffectiveBulk period hPeriod) (n := ∞)
      hLinear hChart

/-- Coordinate basis transported by the derivative of the valid inverse
chart. -/
def programPT06EffectiveBulkChartTangentBasis
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners
        (programPT06EffectiveBulkChartPoint
          period hPeriod anchor coordinate)) :=
  programPT06AmbientCoordinateBasis.map
    ((programPT06EffectiveBulkChartPoint_isLocalDiffeomorphAt
      period hPeriod anchor coordinate hCoordinate
      ).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv

theorem programPT06EffectiveBulkChartTangentBasis_apply
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor)
    (index : Fin 4) :
    programPT06EffectiveBulkChartTangentBasis
        period hPeriod anchor coordinate hCoordinate index =
      programPT06EffectiveBulkChartTangentFrame
        period hPeriod anchor coordinate index := by
  let hLocal := programPT06EffectiveBulkChartPoint_isLocalDiffeomorphAt
    period hPeriod anchor coordinate hCoordinate
  unfold programPT06EffectiveBulkChartTangentBasis
    programPT06EffectiveBulkChartTangentFrame
  rw [Module.Basis.map_apply]
  rw [← hLocal.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact congrFun
    (ContinuousLinearEquiv.coe_toLinearEquiv
      (hLocal.mfderivToContinuousLinearEquiv (by simp)))
    (programPT06AmbientCoordinateBasis index)

/-- Intrinsic metric as a bilinear form at the point represented by a valid
inverse-chart coordinate. -/
private def programPT06EffectiveBulkChartPhysicalMetricBilinForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    LinearMap.BilinForm Real
      (TangentSpace coverModelWithCorners
        (programPT06EffectiveBulkChartPoint
          period hPeriod anchor coordinate)) :=
  (metric.tensor.tensor
    (programPT06EffectiveBulkChartPoint
      period hPeriod anchor coordinate)).toBilinForm

private theorem programPT06EffectiveBulkChartPhysicalMetricBilinForm_nondegenerate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    (programPT06EffectiveBulkChartPhysicalMetricBilinForm
      period hPeriod metric anchor coordinate).Nondegenerate := by
  constructor
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric
    apply ContinuousLinearMap.ext
    intro second
    simpa [programPT06EffectiveBulkChartPhysicalMetricBilinForm] using
      hVector second
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric
    apply ContinuousLinearMap.ext
    intro second
    rw [metric.tensor.symmetric]
    simpa [programPT06EffectiveBulkChartPhysicalMetricBilinForm] using
      hVector second

/-- The physical metric matrix is nonsingular throughout the valid
inverse-chart domain. -/
theorem programPT06EffectiveBulkChartPhysicalMetricMatrix_det_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    (programPT06EffectiveBulkChartPhysicalMetricMatrix
      period hPeriod metric anchor coordinate).det ≠ 0 := by
  let basis := programPT06EffectiveBulkChartTangentBasis
    period hPeriod anchor coordinate hCoordinate
  have hDet :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero basis).mp
      (programPT06EffectiveBulkChartPhysicalMetricBilinForm_nondegenerate
        period hPeriod metric anchor coordinate)
  have hMatrix :
      programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor coordinate =
        LinearMap.BilinForm.toMatrix basis
          (programPT06EffectiveBulkChartPhysicalMetricBilinForm
            period hPeriod metric anchor coordinate) := by
    ext first second
    simp [basis, programPT06EffectiveBulkChartPhysicalMetricMatrix,
      metricGramMatrix,
      programPT06EffectiveBulkChartPhysicalMetricBilinForm,
      programPT06EffectiveBulkChartTangentBasis_apply]
  rw [hMatrix]
  exact hDet

/-- The determinant of the physical metric matrix is differentiable on the
valid inverse-chart domain. -/
theorem programPT06EffectiveBulkChartPhysicalMetricMatrix_det_differentiableAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    DifferentiableAt Real
      (fun nearby => Matrix.det
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor nearby)) coordinate := by
  classical
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro permutation _
  have hConstant : DifferentiableAt Real
      (fun _ : ProgramPT06AmbientCoordinate4 =>
        ((Equiv.Perm.sign permutation : Int) : Real)) coordinate :=
    differentiableAt_const ((Equiv.Perm.sign permutation : Int) : Real)
  have hProduct : DifferentiableAt Real
      (fun nearby => ∏ index,
        programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor nearby (permutation index) index)
      coordinate :=
    (HasFDerivAt.finsetProd
      (u := Finset.univ)
      (g := fun index nearby =>
        programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor nearby (permutation index) index)
      (g' := fun index => fderiv Real (fun nearby =>
        programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor nearby (permutation index) index)
        coordinate)
      (fun index _ =>
        (programPT06EffectiveBulkChartPhysicalMetricMatrix_apply_differentiableAt
          period hPeriod metric anchor coordinate hCoordinate
          (permutation index) index).hasFDerivAt)).differentiableAt
  exact hConstant.mul hProduct

/-- The coordinate metric-volume density of every smooth physical Lorentz
metric is differentiable on the valid inverse-chart domain. -/
theorem programPT06EffectiveBulkChartPhysicalMetricVolumeDensity_differentiableAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeDensity
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor)) coordinate := by
  unfold programPT06AmbientMatrixMetricVolumeDensity
  have hDetDiff :=
    programPT06EffectiveBulkChartPhysicalMetricMatrix_det_differentiableAt
      period hPeriod metric anchor coordinate hCoordinate
  have hDetNe :=
    programPT06EffectiveBulkChartPhysicalMetricMatrix_det_ne_zero
      period hPeriod metric anchor coordinate hCoordinate
  exact (hDetDiff.abs hDetNe).sqrt (abs_ne_zero.mpr hDetNe)

/-- The physical coordinate metric-volume density is strictly positive on
the valid inverse-chart domain. -/
theorem programPT06EffectiveBulkChartPhysicalMetricVolumeDensity_pos
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor) :
    0 < programPT06AmbientMatrixMetricVolumeDensity
      (programPT06EffectiveBulkChartPhysicalMetricMatrix
        period hPeriod metric anchor) coordinate := by
  unfold programPT06AmbientMatrixMetricVolumeDensity
  exact Real.sqrt_pos.2 (abs_pos.mpr
    (programPT06EffectiveBulkChartPhysicalMetricMatrix_det_ne_zero
      period hPeriod metric anchor coordinate hCoordinate))

/-- The selected warped face coordinate lies in the valid inverse incidence
chart domain. -/
theorem programPT06WarpedNullFace_mem_effectiveBulkChartCoordinateDomain
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullHyperplaneEmbedding source ∈
      programPT06EffectiveBulkChartCoordinateDomain
        period hPeriod incidence.chartAnchor := by
  change programPT06AmbientCoverCoordinate
      (programPT06WarpedNullHyperplaneEmbedding source) ∈
    (extChartAt coverModelWithCorners incidence.chartAnchor).target
  have hTarget :=
    (programPT06WarpedNullCollarTransition_eventually_mem_chartTarget
      period hPeriod datum).self_of_nhds
  rw [datum.transition_face period hPeriod] at hTarget
  exact hTarget

/-- On the valid inverse-chart domain, an ordinary differentiable current
remains differentiable after densitization by the genuine physical metric. -/
theorem programPT06EffectiveBulkChartPhysicalMetricVolumeCurrent_differentiableAt_of_mem
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : ProgramPT06EffectiveBulk period hPeriod)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (hCoordinate : coordinate ∈
      programPT06EffectiveBulkChartCoordinateDomain period hPeriod anchor)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current coordinate) :
    DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric anchor) current) coordinate := by
  unfold programPT06AmbientMatrixMetricVolumeCurrent
  exact
    (programPT06EffectiveBulkChartPhysicalMetricVolumeDensity_differentiableAt
      period hPeriod metric anchor coordinate hCoordinate).smul hCurrent

/-- Face specialization of physical metric-volume-current regularity. -/
theorem programPT06EffectiveBulkChartPhysicalMetricVolumeCurrent_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    DifferentiableAt Real
      (programPT06AmbientMatrixMetricVolumeCurrent
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric incidence.chartAnchor) current)
      (programPT06WarpedNullHyperplaneEmbedding source) :=
  programPT06EffectiveBulkChartPhysicalMetricVolumeCurrent_differentiableAt_of_mem
    period hPeriod metric incidence.chartAnchor
    (programPT06WarpedNullHyperplaneEmbedding source)
    (programPT06WarpedNullFace_mem_effectiveBulkChartCoordinateDomain
      period hPeriod datum) current hCurrent

/-- Faithful physical metric-divergence naturality now requires only
ordinary `C¹` regularity of the target current. -/
theorem programPT06WarpedNullCollarPhysicalPullbackMetric_divergence_natural_of_differentiableAt
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum metric)
        (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
          period hPeriod datum current)
        (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06AmbientMatrixMetricVolumeDivergence
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric incidence.chartAnchor)
        current (programPT06WarpedNullHyperplaneEmbedding source) :=
  programPT06WarpedNullCollarPhysicalPullbackMetric_divergence_natural
    period hPeriod datum metric current
    (programPT06EffectiveBulkChartPhysicalMetricVolumeCurrent_differentiableAt
      period hPeriod datum metric current hCurrent)

/-- Physical regularity bundle on the selected incidence-chart face. -/
theorem programPT06WarpedNullCollarPhysicalMetricRegularity_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (current : ProgramPT06AmbientCurrent4D)
    (hCurrent : DifferentiableAt Real current
      (programPT06WarpedNullHyperplaneEmbedding source)) :
    DifferentiableAt Real
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric incidence.chartAnchor)
        (programPT06WarpedNullHyperplaneEmbedding source) ∧
      (programPT06EffectiveBulkChartPhysicalMetricMatrix
        period hPeriod metric incidence.chartAnchor
        (programPT06WarpedNullHyperplaneEmbedding source)).det ≠ 0 ∧
      0 < programPT06AmbientMatrixMetricVolumeDensity
        (programPT06EffectiveBulkChartPhysicalMetricMatrix
          period hPeriod metric incidence.chartAnchor)
        (programPT06WarpedNullHyperplaneEmbedding source) ∧
      DifferentiableAt Real
        (programPT06AmbientMatrixMetricVolumeCurrent
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod metric incidence.chartAnchor)
          current)
        (programPT06WarpedNullHyperplaneEmbedding source) ∧
      programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06WarpedNullCollarPhysicalPullbackMetric
            period hPeriod datum metric)
          (programPT06WarpedNullCollarTransitionVectorPullbackCurrent
            period hPeriod datum current)
          (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06AmbientMatrixMetricVolumeDivergence
          (programPT06EffectiveBulkChartPhysicalMetricMatrix
            period hPeriod metric incidence.chartAnchor)
          current (programPT06WarpedNullHyperplaneEmbedding source) := by
  have hDomain :=
    programPT06WarpedNullFace_mem_effectiveBulkChartCoordinateDomain
      period hPeriod datum
  exact ⟨
    programPT06EffectiveBulkChartPhysicalMetricMatrix_differentiableAt
      period hPeriod metric incidence.chartAnchor
      (programPT06WarpedNullHyperplaneEmbedding source) hDomain,
    programPT06EffectiveBulkChartPhysicalMetricMatrix_det_ne_zero
      period hPeriod metric incidence.chartAnchor
      (programPT06WarpedNullHyperplaneEmbedding source) hDomain,
    programPT06EffectiveBulkChartPhysicalMetricVolumeDensity_pos
      period hPeriod metric incidence.chartAnchor
      (programPT06WarpedNullHyperplaneEmbedding source) hDomain,
    programPT06EffectiveBulkChartPhysicalMetricVolumeCurrent_differentiableAt
      period hPeriod datum metric current hCurrent,
    programPT06WarpedNullCollarPhysicalPullbackMetric_divergence_natural_of_differentiableAt
      period hPeriod datum metric current hCurrent⟩

end

end P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricRegularity4D
end JanusFormal
