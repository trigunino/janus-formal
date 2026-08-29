import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalPalatiniGHYBridge4D

/-!
# Continuum box Stokes theorem for the densitized Palatini current

The local Einstein--Hilbert variation already produces the genuine density
`∂ρ (√|g| V^ρ)`.  This file places that density in Mathlib's Bochner
divergence theorem on an arbitrary compact four-coordinate box.  The result is
a continuum integral identity over all eight oriented faces, not a finite
network telescoping surrogate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation
open P0EFTJanusGaussianNormalEHGHYCancellation
open P0EFTJanusMappingTorusLocalPalatiniGHYBridge4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev FaceCoordinate3 := Fin 3 → ℝ

/-- A compact four-coordinate rectangle. -/
structure CompactCoordinateBox4 where
  lower : Vector4
  upper : Vector4
  lower_le_upper : lower ≤ upper

/-- Densitized Palatini flux `√|g| V^ρ` along a field of compatible jets. -/
def densitizedPalatiniFlux
    (jet : Vector4 → DensitizedPalatiniJet4)
    (coordinate : Vector4) : Vector4 :=
  fun vector =>
    (jet coordinate).volume *
      palatiniVector (jet coordinate).toMetricCompatiblePalatiniJet4 vector

/-- Analytic realization of the algebraic Palatini jets on one coordinate
box.  `fluxDerivative_coordinate` says that the stored partial jets are the
actual Fréchet derivatives of the densitized current. -/
structure DensitizedPalatiniBoxField
    (box : CompactCoordinateBox4) where
  jet : Vector4 → DensitizedPalatiniJet4
  fluxDerivative : Vector4 → Vector4 →L[ℝ] Vector4
  flux_continuousOn :
    ContinuousOn (densitizedPalatiniFlux jet) (Icc box.lower box.upper)
  flux_hasFDerivAt : ∀ coordinate ∈
      Set.pi Set.univ (fun index => Ioo (box.lower index) (box.upper index)),
    HasFDerivAt (densitizedPalatiniFlux jet)
      (fluxDerivative coordinate) coordinate
  fluxDerivative_coordinate : ∀ coordinate index,
    fluxDerivative coordinate (Pi.single index 1) index =
      densitizedPalatiniVectorPartialDerivative
        (jet coordinate) index index
  divergence_integrable :
    IntegrableOn
      (fun coordinate =>
        densitizedPalatiniCoordinateDivergence (jet coordinate))
      (Icc box.lower box.upper)

/-- Exact continuum Stokes theorem for the actual densitized Palatini current
on a four-coordinate box. -/
theorem integral_densitizedPalatiniCoordinateDivergence_eq_orientedFaces
    (box : CompactCoordinateBox4)
    (field : DensitizedPalatiniBoxField box) :
    (∫ coordinate in Icc box.lower box.upper,
      densitizedPalatiniCoordinateDivergence (field.jet coordinate)) =
      ∑ index : Index4,
        ((∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            densitizedPalatiniFlux field.jet
              (index.insertNth (box.upper index) face) index) -
          ∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            densitizedPalatiniFlux field.jet
              (index.insertNth (box.lower index) face) index) := by
  have hDerivative :
      (fun coordinate =>
        ∑ index : Index4,
          field.fluxDerivative coordinate (Pi.single index 1) index) =
        fun coordinate =>
          densitizedPalatiniCoordinateDivergence (field.jet coordinate) := by
    funext coordinate
    unfold densitizedPalatiniCoordinateDivergence
    apply Finset.sum_congr rfl
    intro index _
    exact field.fluxDerivative_coordinate coordinate index
  have hDerivativeIntegrable :
      IntegrableOn
        (fun coordinate =>
          ∑ index : Index4,
            field.fluxDerivative coordinate (Pi.single index 1) index)
        (Icc box.lower box.upper) := by
    rw [hDerivative]
    exact field.divergence_integrable
  rw [← hDerivative]
  exact MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
    box.lower box.upper box.lower_le_upper
    (densitizedPalatiniFlux field.jet) field.fluxDerivative
    ∅ Set.countable_empty field.flux_continuousOn
    (fun coordinate hCoordinate =>
      field.flux_hasFDerivAt coordinate hCoordinate.1)
    hDerivativeIntegrable

/-- Pointwise geometric realization of the eight outward face fluxes by
Gaussian-normal Dirichlet data.  The signs are exactly those appearing in the
oriented box boundary: front faces are positive and back faces negative. -/
structure PalatiniGHYBoxBoundaryRealization
    (box : CompactCoordinateBox4)
    (field : DensitizedPalatiniBoxField box)
    (einsteinScale : ℝ) where
  frontData : Index4 → FaceCoordinate3 → NonNullBoundaryPointData
  backData : Index4 → FaceCoordinate3 → NonNullBoundaryPointData
  frontJet : Index4 → FaceCoordinate3 → GaussianNormalDirichletJet
  backJet : Index4 → FaceCoordinate3 → GaussianNormalDirichletJet
  front_orientation_match : ∀ index face,
    einsteinHilbertDirichletBoundaryFlux einsteinScale
        (frontData index face) (frontJet index face) =
      (einsteinScale / 2) *
        densitizedPalatiniFlux field.jet
          (index.insertNth (box.upper index) face) index
  back_orientation_match : ∀ index face,
    einsteinHilbertDirichletBoundaryFlux einsteinScale
        (backData index face) (backJet index face) =
      -(einsteinScale / 2) *
        densitizedPalatiniFlux field.jet
          (index.insertNth (box.lower index) face) index

/-- Sum of the genuine exact-inverse GHY derivatives over all eight faces. -/
def integratedBoxExactGHYDerivative
    (box : CompactCoordinateBox4)
    (field : DensitizedPalatiniBoxField box)
    (einsteinScale : ℝ)
    (boundary :
      PalatiniGHYBoxBoundaryRealization box field einsteinScale) : ℝ :=
  ∑ index : Index4,
    ((∫ face in
          Icc (box.lower ∘ index.succAbove)
            (box.upper ∘ index.succAbove),
        nonNullGHYFirstVariation einsteinScale
          (boundary.frontData index face)
          (metricFirstJetVariation (boundary.frontData index face)
            (gaussianDirichletBoundaryVariation
              (boundary.frontJet index face)))) +
      ∫ face in
          Icc (box.lower ∘ index.succAbove)
            (box.upper ∘ index.succAbove),
        nonNullGHYFirstVariation einsteinScale
          (boundary.backData index face)
          (metricFirstJetVariation (boundary.backData index face)
            (gaussianDirichletBoundaryVariation
              (boundary.backJet index face))))

/-- On every front face the exact GHY derivative is the negative scaled
coordinate flux. -/
theorem front_exactGHYDerivative_eq_neg_scaledFlux
    (box : CompactCoordinateBox4)
    (field : DensitizedPalatiniBoxField box)
    (einsteinScale : ℝ)
    (boundary :
      PalatiniGHYBoxBoundaryRealization box field einsteinScale)
    (index : Index4) :
    (fun face =>
      nonNullGHYFirstVariation einsteinScale
        (boundary.frontData index face)
        (metricFirstJetVariation (boundary.frontData index face)
          (gaussianDirichletBoundaryVariation
            (boundary.frontJet index face)))) =
      fun face =>
        -(einsteinScale / 2) *
          densitizedPalatiniFlux field.jet
            (index.insertNth (box.upper index) face) index := by
  funext face
  have hCancel :=
    einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
      einsteinScale (boundary.frontData index face)
        (boundary.frontJet index face)
  rw [boundary.front_orientation_match index face] at hCancel
  linarith

/-- On every back face the outward orientation reverses the coordinate
current, so the exact GHY derivative is the positive scaled coordinate flux. -/
theorem back_exactGHYDerivative_eq_scaledFlux
    (box : CompactCoordinateBox4)
    (field : DensitizedPalatiniBoxField box)
    (einsteinScale : ℝ)
    (boundary :
      PalatiniGHYBoxBoundaryRealization box field einsteinScale)
    (index : Index4) :
    (fun face =>
      nonNullGHYFirstVariation einsteinScale
        (boundary.backData index face)
        (metricFirstJetVariation (boundary.backData index face)
          (gaussianDirichletBoundaryVariation
            (boundary.backJet index face)))) =
      fun face =>
        (einsteinScale / 2) *
          densitizedPalatiniFlux field.jet
            (index.insertNth (box.lower index) face) index := by
  funext face
  have hCancel :=
    einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
      einsteinScale (boundary.backData index face)
        (boundary.backJet index face)
  rw [boundary.back_orientation_match index face] at hCancel
  linarith

/-- Complete continuum Einstein--Hilbert/Palatini plus exact-GHY
cancellation on the four-coordinate box. -/
theorem scaled_integral_Palatini_add_integrated_exact_GHY_eq_zero
    (box : CompactCoordinateBox4)
    (field : DensitizedPalatiniBoxField box)
    (einsteinScale : ℝ)
    (boundary :
      PalatiniGHYBoxBoundaryRealization box field einsteinScale) :
    (einsteinScale / 2) *
        (∫ coordinate in Icc box.lower box.upper,
          densitizedPalatiniCoordinateDivergence (field.jet coordinate)) +
      integratedBoxExactGHYDerivative box field einsteinScale boundary = 0 := by
  rw [integral_densitizedPalatiniCoordinateDivergence_eq_orientedFaces]
  unfold integratedBoxExactGHYDerivative
  simp_rw [front_exactGHYDerivative_eq_neg_scaledFlux,
    back_exactGHYDerivative_eq_scaledFlux,
    integral_const_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro index _
  ring

/-- A finite collection of genuine coordinate boxes.  Every cell carries the
actual densitized Palatini current and the exact GHY realization on all of its
faces. -/
structure FinitePalatiniGHYBoxAtlas (einsteinScale : ℝ) where
  cellCount : ℕ
  box : Fin cellCount → CompactCoordinateBox4
  field : ∀ cell, DensitizedPalatiniBoxField (box cell)
  boundary : ∀ cell,
    PalatiniGHYBoxBoundaryRealization
      (box cell) (field cell) einsteinScale

/-- Sum of the continuum Palatini bulk variations over a finite box atlas. -/
def finiteAtlasPalatiniBulkVariation
    (einsteinScale : ℝ)
    (atlas : FinitePalatiniGHYBoxAtlas einsteinScale) : ℝ :=
  ∑ cell : Fin atlas.cellCount,
    (einsteinScale / 2) *
      ∫ coordinate in Icc (atlas.box cell).lower (atlas.box cell).upper,
        densitizedPalatiniCoordinateDivergence
          ((atlas.field cell).jet coordinate)

/-- Sum of the exact GHY derivatives over every face of every cell. -/
def finiteAtlasExactGHYDerivative
    (einsteinScale : ℝ)
    (atlas : FinitePalatiniGHYBoxAtlas einsteinScale) : ℝ :=
  ∑ cell : Fin atlas.cellCount,
    integratedBoxExactGHYDerivative
      (atlas.box cell) (atlas.field cell) einsteinScale
        (atlas.boundary cell)

/-- Finite-atlas continuum Stokes--Palatini--GHY cancellation.  This is a
Bochner-integral theorem on every cell; it is not the older finite-difference
telescoping proxy. -/
theorem finiteAtlasPalatini_add_exactGHY_eq_zero
    (einsteinScale : ℝ)
    (atlas : FinitePalatiniGHYBoxAtlas einsteinScale) :
    finiteAtlasPalatiniBulkVariation einsteinScale atlas +
      finiteAtlasExactGHYDerivative einsteinScale atlas = 0 := by
  unfold finiteAtlasPalatiniBulkVariation finiteAtlasExactGHYDerivative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro cell _
  exact scaled_integral_Palatini_add_integrated_exact_GHY_eq_zero
    (atlas.box cell) (atlas.field cell) einsteinScale
      (atlas.boundary cell)

end

end P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
end JanusFormal
