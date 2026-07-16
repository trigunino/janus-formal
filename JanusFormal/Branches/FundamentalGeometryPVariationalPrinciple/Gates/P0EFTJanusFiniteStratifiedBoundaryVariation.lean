import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEHGHYCancellation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNullJointReparametrizationCancellation

/-!
# Finite stratified EH/GHY/null/joint boundary variation

This gate assembles two already geometric local calculations into one finite
oriented boundary ledger.

* On every non-null face, the exact-inverse GHY curve has derivative equal to
  the negative Gaussian-normal Einstein--Hilbert Palatini flux.
* On every null generator interval, the face reparametrization density is
  genuinely integrated.  The fundamental theorem of calculus identifies it
  with the endpoint transgression, which is cancelled by the two oriented
  joint shifts.
* Arbitrary finite collections of both kinds of strata therefore have zero
  total residual.

Face weights are explicit real coefficients, so the theorem applies after any
finite quadrature or cell decomposition, including opposite orientations.
This is not an arbitrary-coordinate continuum Einstein--Hilbert variation:
the non-null calculation remains Gaussian-normal and the null calculation is
one-dimensional along each generator.  It does not construct the ambient
mapping-torus stratification or the LL worldvolume action.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteStratifiedBoundaryVariation

set_option autoImplicit false

noncomputable section

open scoped BigOperators

open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusExplicitBoundaryDensityLocalVariations
open P0EFTJanusGaussianNormalEHGHYCancellation
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation
open P0EFTJanusNonNullGHYExactInverseCurve
open P0EFTJanusNullJointReparametrizationCancellation

/-- Geometric and variational data attached to one non-null boundary face. -/
structure NonNullFaceDatum where
  weight : ℝ
  einsteinScale : ℝ
  geometry : NonNullBoundaryPointData
  dirichletJet : GaussianNormalDirichletJet

/-- Weighted Einstein--Hilbert Palatini flux through one oriented face. -/
def nonNullEHFlux (face : NonNullFaceDatum) : ℝ :=
  face.weight *
    einsteinHilbertDirichletBoundaryFlux face.einsteinScale
      face.geometry face.dirichletJet

/-- Exact GHY curve corresponding to the same face and Dirichlet jet. -/
def nonNullGHYCurve (face : NonNullFaceDatum) (parameter : ℝ) : ℝ :=
  face.weight *
    nonNullGHYExactInverseCurve face.einsteinScale face.geometry
      (gaussianDirichletBoundaryVariation face.dirichletJet) parameter

/-- Weighted exact GHY first variation, independently displayed from the EH
flux that it cancels. -/
def nonNullGHYDerivative (face : NonNullFaceDatum) : ℝ :=
  face.weight *
    nonNullGHYFirstVariation face.einsteinScale face.geometry
      (metricFirstJetVariation face.geometry
        (gaussianDirichletBoundaryVariation face.dirichletJet))

/-- Pointwise EH/GHY cancellation survives every face weight. -/
theorem nonNullEHFlux_add_GHYDerivative_eq_zero
    (face : NonNullFaceDatum) :
    nonNullEHFlux face + nonNullGHYDerivative face = 0 := by
  have h := einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
    face.einsteinScale face.geometry face.dirichletJet
  unfold nonNullEHFlux nonNullGHYDerivative
  calc
    face.weight *
          einsteinHilbertDirichletBoundaryFlux face.einsteinScale
            face.geometry face.dirichletJet +
        face.weight *
          nonNullGHYFirstVariation face.einsteinScale face.geometry
            (metricFirstJetVariation face.geometry
              (gaussianDirichletBoundaryVariation face.dirichletJet)) =
        face.weight *
          (einsteinHilbertDirichletBoundaryFlux face.einsteinScale
              face.geometry face.dirichletJet +
            nonNullGHYFirstVariation face.einsteinScale face.geometry
              (metricFirstJetVariation face.geometry
                (gaussianDirichletBoundaryVariation face.dirichletJet))) := by
          ring
    _ = 0 := by rw [h, mul_zero]

/-- The actual face GHY curve differentiates to the opposite EH flux. -/
theorem nonNullGHYCurve_hasDerivative_neg_EHFlux
    (face : NonNullFaceDatum) :
    FrobeniusScalarHasDerivAt (nonNullGHYCurve face)
      (-nonNullEHFlux face) 0 := by
  have h := exactGHYCurve_hasDerivative_neg_einsteinHilbertFlux
    face.einsteinScale face.geometry face.dirichletJet
  unfold FrobeniusScalarHasDerivAt at h ⊢
  have hWeighted := h.const_mul face.weight
  refine (hWeighted.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  ext
  simp [nonNullEHFlux]

/-- Total EH flux over an arbitrary finite family of non-null faces. -/
def totalNonNullEHFlux
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) : ℝ :=
  ∑ face : Face, nonNullEHFlux (faces face)

/-- Total exact GHY first variation over all non-null faces. -/
def totalNonNullGHYDerivative
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) : ℝ :=
  ∑ face : Face, nonNullGHYDerivative (faces face)

/-- Sum of the exact GHY curves over the same finite face family. -/
def totalNonNullGHYCurve
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum)
    (parameter : ℝ) : ℝ :=
  ∑ face : Face, nonNullGHYCurve (faces face) parameter

/-- The finite global GHY curve differentiates to the opposite total EH flux. -/
theorem totalNonNullGHYCurve_hasDerivative_neg_totalEHFlux
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) :
    FrobeniusScalarHasDerivAt (totalNonNullGHYCurve faces)
      (-totalNonNullEHFlux faces) 0 := by
  unfold FrobeniusScalarHasDerivAt totalNonNullGHYCurve totalNonNullEHFlux
  have hSum := HasFDerivAt.fun_sum (u := Finset.univ) (fun face _ => by
    exact nonNullGHYCurve_hasDerivative_neg_EHFlux (faces face))
  refine (hSum.congr_fderiv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  ext
  simp

/-- Non-null first-variation residual, retaining the independently constructed
EH and exact GHY terms. -/
def totalNonNullVariationResidual
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) : ℝ :=
  totalNonNullEHFlux faces + totalNonNullGHYDerivative faces

theorem totalNonNullVariationResidual_eq_zero
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) :
    totalNonNullVariationResidual faces = 0 := by
  unfold totalNonNullVariationResidual totalNonNullEHFlux
    totalNonNullGHYDerivative
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun face _ =>
    nonNullEHFlux_add_GHYDerivative_eq_zero (faces face)

theorem totalNonNullGHYDerivative_eq_neg_totalEHFlux
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) :
    totalNonNullGHYDerivative faces = -totalNonNullEHFlux faces := by
  have h := totalNonNullVariationResidual_eq_zero faces
  unfold totalNonNullVariationResidual at h
  linarith

/-- The derivative of the summed exact GHY action is precisely its separately
assembled first-variation ledger. -/
theorem totalNonNullGHYCurve_hasDerivative_totalGHYDerivative
    {Face : Type*} [Fintype Face] (faces : Face → NonNullFaceDatum) :
    FrobeniusScalarHasDerivAt (totalNonNullGHYCurve faces)
      (totalNonNullGHYDerivative faces) 0 := by
  rw [totalNonNullGHYDerivative_eq_neg_totalEHFlux]
  exact totalNonNullGHYCurve_hasDerivative_neg_totalEHFlux faces

/-- A null face with an oriented generator interval and the exact
integrability hypothesis needed by the fundamental theorem of calculus. -/
structure NullFaceDatum where
  generator : NullGeneratorReparametrizationData
  interval : OrientedNullInterval
  faceShiftIntervalIntegrable :
    IntervalIntegrable (localFaceShift generator) MeasureTheory.volume
      interval.initialParameter interval.finalParameter

/-- Integrated normalization shift on the oriented null face. -/
def integratedNullFaceShift (face : NullFaceDatum) : ℝ :=
  ∫ parameter in face.interval.initialParameter..face.interval.finalParameter,
    localFaceShift face.generator parameter

/-- Oriented sum of the two endpoint joint shifts. -/
def nullJointShift (face : NullFaceDatum) : ℝ :=
  endpointPrimitive face.generator face.interval.initialParameter -
    endpointPrimitive face.generator face.interval.finalParameter

/-- The local null transgression integrates to its endpoint primitive. -/
theorem integratedNullFaceShift_eq_endpointTransgression
    (face : NullFaceDatum) :
    integratedNullFaceShift face =
      endpointPrimitive face.generator face.interval.finalParameter -
        endpointPrimitive face.generator face.interval.initialParameter := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro parameter _
    exact area_mul_sigma_hasDerivAt face.generator parameter
  · exact face.faceShiftIntervalIntegrable

/-- An integrated null-face shift is cancelled by its globally oriented
endpoint joints. -/
theorem integratedNullFace_add_joints_eq_zero (face : NullFaceDatum) :
    integratedNullFaceShift face + nullJointShift face = 0 := by
  rw [integratedNullFaceShift_eq_endpointTransgression]
  simp [nullJointShift]

/-- Total integrated null-face plus joint residual for a finite stratification. -/
def totalNullJointResidual
    {Face : Type*} [Fintype Face] (faces : Face → NullFaceDatum) : ℝ :=
  ∑ face : Face,
    (integratedNullFaceShift (faces face) + nullJointShift (faces face))

theorem totalNullJointResidual_eq_zero
    {Face : Type*} [Fintype Face] (faces : Face → NullFaceDatum) :
    totalNullJointResidual faces = 0 := by
  simp [totalNullJointResidual, integratedNullFace_add_joints_eq_zero]

/-- Complete finite stratified boundary residual: non-null EH/GHY pieces plus
integrated null faces and their endpoint joints. -/
def finiteStratifiedBoundaryResidual
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (nonNullFaces : NonNullFace → NonNullFaceDatum)
    (nullFaces : NullFace → NullFaceDatum) : ℝ :=
  totalNonNullVariationResidual nonNullFaces +
    totalNullJointResidual nullFaces

/-- No boundary flux remains in the finite stratified model. -/
theorem finiteStratifiedBoundaryResidual_eq_zero
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (nonNullFaces : NonNullFace → NonNullFaceDatum)
    (nullFaces : NullFace → NullFaceDatum) :
    finiteStratifiedBoundaryResidual nonNullFaces nullFaces = 0 := by
  rw [finiteStratifiedBoundaryResidual,
    totalNonNullVariationResidual_eq_zero,
    totalNullJointResidual_eq_zero, zero_add]

end

end P0EFTJanusFiniteStratifiedBoundaryVariation
end JanusFormal
