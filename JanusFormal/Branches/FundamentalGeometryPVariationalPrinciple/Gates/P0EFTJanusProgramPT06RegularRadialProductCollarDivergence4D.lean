import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D

/-!
# Regular radial current on a product collar

This gate provides a regular coordinate-split counterpart to Gate 1032's
generic ambient extension when its throat and normal components are `C¹`.
For a normal component constant along the collar coordinate, the full
transverse first derivative vanishes and the ambient four-divergence is
exactly the throat three-divergence.  An affine normal profile also realizes a
prescribed constant transverse first jet.  The genuine-face set-theoretic
completion of Gate 1032 remains separate.

The genuine cut bulk already has a smooth open collar, a smooth zero face and
an invertible derivative into the quotient.  There is still no asserted map
from a finite null-face chart into that cut boundary, so no such incidence or
integrated Stokes statement is claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Module
open scoped ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanPiolaNaturality4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional

/-- Product-collar current with its normal component held constant along the
transverse coordinate. -/
def programPT06RegularProductCollarCurrent
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06AmbientThroatTransverse4 →
      ProgramPT06AmbientThroatTransverse4 :=
  fun coordinate =>
    (throatCurrent coordinate.1, normalDensity coordinate.1)

/-- Transport the regular product-collar current to the ambient coordinates
fixed in Gate 1032. -/
def programPT06RegularAmbientCollarCurrent
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    programPT06AmbientThroatTransverseEquiv.symm
      (programPT06RegularProductCollarCurrent throatCurrent normalDensity
        (programPT06AmbientThroatTransverseEquiv coordinate))

/-- Product-collar current with a prescribed constant first derivative in the
transverse direction. -/
def programPT06AffineProductCollarCurrent
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real)
    (normalSlope : Real) :
    ProgramPT06AmbientThroatTransverse4 →
      ProgramPT06AmbientThroatTransverse4 :=
  fun coordinate =>
    (throatCurrent coordinate.1,
      normalDensity coordinate.1 + normalSlope * coordinate.2)

/-- Transport the affine product-collar current to ambient coordinates. -/
def programPT06AffineAmbientCollarCurrent
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real)
    (normalSlope : Real) :
    ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    programPT06AmbientThroatTransverseEquiv.symm
      (programPT06AffineProductCollarCurrent throatCurrent normalDensity
        normalSlope (programPT06AmbientThroatTransverseEquiv coordinate))

/-- The product-collar current has the same finite regularity as its two
throat-dependent components. -/
theorem programPT06RegularProductCollarCurrent_contDiff_one
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    (hThroat : ContDiff Real 1 throatCurrent)
    (hNormal : ContDiff Real 1 normalDensity) :
    ContDiff Real 1
      (programPT06RegularProductCollarCurrent throatCurrent normalDensity) := by
  exact (hThroat.comp contDiff_fst).prodMk (hNormal.comp contDiff_fst)

/-- Transport through the fixed linear split preserves `C¹` regularity. -/
theorem programPT06RegularAmbientCollarCurrent_contDiff_one
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    (hThroat : ContDiff Real 1 throatCurrent)
    (hNormal : ContDiff Real 1 normalDensity) :
    ContDiff Real 1
      (programPT06RegularAmbientCollarCurrent throatCurrent normalDensity) := by
  exact programPT06AmbientThroatTransverseEquiv.symm.contDiff.comp
    ((programPT06RegularProductCollarCurrent_contDiff_one hThroat hNormal).comp
      programPT06AmbientThroatTransverseEquiv.contDiff)

/-- Exact derivative of the product-collar current. -/
theorem programPT06RegularProductCollarCurrent_hasFDerivAt
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {coordinate : ProgramPT06AmbientThroatTransverse4}
    (hThroat : DifferentiableAt Real throatCurrent coordinate.1)
    (hNormal : DifferentiableAt Real normalDensity coordinate.1) :
    HasFDerivAt
      (programPT06RegularProductCollarCurrent throatCurrent normalDensity)
      (((fderiv Real throatCurrent coordinate.1).comp
          (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
        ((fderiv Real normalDensity coordinate.1).comp
          (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)))
      coordinate := by
  exact
    (hThroat.hasFDerivAt.comp coordinate
        (hasFDerivAt_fst (𝕜 := Real))).prodMk
      (hNormal.hasFDerivAt.comp coordinate
        (hasFDerivAt_fst (𝕜 := Real)))

/-- Exact derivative after transport to ambient coordinates. -/
theorem programPT06RegularAmbientCollarCurrent_hasFDerivAt
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection coordinate))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection coordinate)) :
    HasFDerivAt
      (programPT06RegularAmbientCollarCurrent throatCurrent normalDensity)
      (programPT06AmbientThroatTransverseEquiv.symm.toContinuousLinearMap.comp
        ((((fderiv Real throatCurrent
              (programPT06AmbientThroatProjection coordinate)).comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
          ((fderiv Real normalDensity
              (programPT06AmbientThroatProjection coordinate)).comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real))).comp
          programPT06AmbientThroatTransverseEquiv.toContinuousLinearMap))
      coordinate := by
  have hSplitFirst :
      (programPT06AmbientThroatTransverseEquiv coordinate).1 =
        programPT06AmbientThroatProjection coordinate := by
    rfl
  have hProduct := programPT06RegularProductCollarCurrent_hasFDerivAt
    (coordinate := programPT06AmbientThroatTransverseEquiv coordinate)
    (hSplitFirst ▸ hThroat) (hSplitFirst ▸ hNormal)
  exact programPT06AmbientThroatTransverseEquiv.symm.hasFDerivAt.comp coordinate
    (hProduct.comp coordinate
      programPT06AmbientThroatTransverseEquiv.hasFDerivAt)

/-- Exact derivative of the affine product-collar current. -/
theorem programPT06AffineProductCollarCurrent_hasFDerivAt
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    {coordinate : ProgramPT06AmbientThroatTransverse4}
    (hThroat : DifferentiableAt Real throatCurrent coordinate.1)
    (hNormal : DifferentiableAt Real normalDensity coordinate.1) :
    HasFDerivAt
      (programPT06AffineProductCollarCurrent throatCurrent normalDensity
        normalSlope)
      (((fderiv Real throatCurrent coordinate.1).comp
          (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
        (((fderiv Real normalDensity coordinate.1).comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)) +
          normalSlope •
            (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real)))
      coordinate := by
  have hFirst := hThroat.hasFDerivAt.comp coordinate
    (hasFDerivAt_fst (𝕜 := Real))
  have hDensity := hNormal.hasFDerivAt.comp coordinate
    (hasFDerivAt_fst (𝕜 := Real))
  have hSlope : HasFDerivAt
      (fun point : ProgramPT06AmbientThroatTransverse4 =>
        normalSlope * point.2)
      (normalSlope •
        (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))
      coordinate := by
    change HasFDerivAt
      (normalSlope •
        (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))
      (normalSlope •
        (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real)) coordinate
    exact (normalSlope •
      (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real)).hasFDerivAt
  exact hFirst.prodMk (hDensity.add hSlope)

/-- Exact derivative of the affine current after ambient transport. -/
theorem programPT06AffineAmbientCollarCurrent_hasFDerivAt
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection coordinate))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection coordinate)) :
    HasFDerivAt
      (programPT06AffineAmbientCollarCurrent throatCurrent normalDensity
        normalSlope)
      (programPT06AmbientThroatTransverseEquiv.symm.toContinuousLinearMap.comp
        ((((fderiv Real throatCurrent
              (programPT06AmbientThroatProjection coordinate)).comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
          (((fderiv Real normalDensity
              (programPT06AmbientThroatProjection coordinate)).comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)) +
            normalSlope •
              (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))).comp
          programPT06AmbientThroatTransverseEquiv.toContinuousLinearMap))
      coordinate := by
  have hSplitFirst :
      (programPT06AmbientThroatTransverseEquiv coordinate).1 =
        programPT06AmbientThroatProjection coordinate := by
    rfl
  have hProduct := programPT06AffineProductCollarCurrent_hasFDerivAt
    (coordinate := programPT06AmbientThroatTransverseEquiv coordinate)
    (normalSlope := normalSlope)
    (hSplitFirst ▸ hThroat) (hSplitFirst ▸ hNormal)
  exact programPT06AmbientThroatTransverseEquiv.symm.hasFDerivAt.comp coordinate
    (hProduct.comp coordinate
      programPT06AmbientThroatTransverseEquiv.hasFDerivAt)

/-- The fixed-basis throat divergence is the intrinsic trace of the Frechet
derivative. -/
theorem programPT06ThroatCoordinateDivergence_eq_trace
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (coordinate : ThroatCoverCoordinates) :
    programPT06ThroatCoordinateDivergence field coordinate =
      LinearMap.trace Real ThroatCoverCoordinates
        (fderiv Real field coordinate).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace Real programPT06ThroatSpatialBasis]
  simp [programPT06ThroatCoordinateDivergence, Matrix.trace,
    LinearMap.toMatrix_apply]

/-- The fixed-basis ambient divergence is the intrinsic trace of the Frechet
derivative. -/
theorem programPT06AmbientCoordinateDivergence_eq_trace
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientCoordinateDivergence current coordinate =
      LinearMap.trace Real ProgramPT06AmbientCoordinate4
        (fderiv Real current coordinate).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace Real programPT06AmbientCoordinateBasis]
  simp [programPT06AmbientCoordinateDivergence, Matrix.trace,
    LinearMap.toMatrix_apply]

/-- The trace of a product derivative with no transverse dependence is the
trace of its tangential diagonal block.  Dependence of the normal component
on throat coordinates is off diagonal and hence contributes no trace. -/
theorem programPT06Trace_productCollarDerivative
    (tangentDerivative : ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates)
    (normalDerivative : ThroatCoverCoordinates →L[Real] Real) :
    LinearMap.trace Real ProgramPT06AmbientThroatTransverse4
        (((tangentDerivative.comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
          (normalDerivative.comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real))).toLinearMap) =
      LinearMap.trace Real ThroatCoverCoordinates
        tangentDerivative.toLinearMap := by
  let diagonal : ProgramPT06AmbientThroatTransverse4 →ₗ[Real]
      ProgramPT06AmbientThroatTransverse4 :=
    LinearMap.prodMap tangentDerivative.toLinearMap (0 : Real →ₗ[Real] Real)
  let offDiagonal : ProgramPT06AmbientThroatTransverse4 →ₗ[Real]
      ProgramPT06AmbientThroatTransverse4 :=
    (ContinuousLinearMap.inr Real ThroatCoverCoordinates Real).toLinearMap.comp
      (normalDerivative.toLinearMap.comp
        (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real).toLinearMap)
  have hSplit :
      ((tangentDerivative.comp
          (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
        (normalDerivative.comp
          (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real))).toLinearMap =
        diagonal + offDiagonal := by
    ext vector <;> simp [diagonal, offDiagonal]
  rw [hSplit, map_add]
  have hDiagonal :
      LinearMap.trace Real ProgramPT06AmbientThroatTransverse4 diagonal =
        LinearMap.trace Real ThroatCoverCoordinates tangentDerivative.toLinearMap := by
    simp [diagonal, LinearMap.trace_prodMap']
  rw [hDiagonal]
  have hOffDiagonal :
      LinearMap.trace Real ProgramPT06AmbientThroatTransverse4 offDiagonal = 0 := by
    let projection : ProgramPT06AmbientThroatTransverse4 →ₗ[Real]
        ThroatCoverCoordinates :=
      (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real).toLinearMap
    let insertion : ThroatCoverCoordinates →ₗ[Real]
        ProgramPT06AmbientThroatTransverse4 :=
      (ContinuousLinearMap.inr Real ThroatCoverCoordinates Real).toLinearMap.comp
        normalDerivative.toLinearMap
    have hOff : offDiagonal = insertion.comp projection := by
      rfl
    rw [hOff, LinearMap.trace_comp_comm' projection insertion]
    have hZero : projection.comp insertion = 0 := by
      apply LinearMap.ext
      intro vector
      rfl
    rw [hZero]
    simp
  rw [hOffDiagonal, add_zero]

/-- Adding a constant normal slope adds exactly that scalar to the product
trace. -/
theorem programPT06Trace_affineProductCollarDerivative
    (tangentDerivative : ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates)
    (normalDerivative : ThroatCoverCoordinates →L[Real] Real)
    (normalSlope : Real) :
    LinearMap.trace Real ProgramPT06AmbientThroatTransverse4
        (((tangentDerivative.comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
          ((normalDerivative.comp
              (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)) +
            normalSlope •
              (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))).toLinearMap) =
      LinearMap.trace Real ThroatCoverCoordinates tangentDerivative.toLinearMap +
        normalSlope := by
  let constantDerivative : ProgramPT06AmbientThroatTransverse4 →L[Real]
      ProgramPT06AmbientThroatTransverse4 :=
    (tangentDerivative.comp
        (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
      (normalDerivative.comp
        (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real))
  let slopeDerivative : ProgramPT06AmbientThroatTransverse4 →L[Real]
      ProgramPT06AmbientThroatTransverse4 :=
    (0 : ProgramPT06AmbientThroatTransverse4 →L[Real]
      ThroatCoverCoordinates).prod
      (normalSlope •
        (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))
  have hSplit :
      ((tangentDerivative.comp
          (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
        ((normalDerivative.comp
            (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)) +
          normalSlope •
            (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))).toLinearMap =
        constantDerivative.toLinearMap + slopeDerivative.toLinearMap := by
    apply LinearMap.ext
    intro vector
    simp [constantDerivative, slopeDerivative]
  rw [hSplit, map_add]
  have hConstant :
      LinearMap.trace Real ProgramPT06AmbientThroatTransverse4
          constantDerivative.toLinearMap =
        LinearMap.trace Real ThroatCoverCoordinates
          tangentDerivative.toLinearMap := by
    exact programPT06Trace_productCollarDerivative _ _
  rw [hConstant]
  have hSlope :
      LinearMap.trace Real ProgramPT06AmbientThroatTransverse4
          slopeDerivative.toLinearMap = normalSlope := by
    have hSlopeMap : slopeDerivative.toLinearMap =
        LinearMap.prodMap
          (0 : ThroatCoverCoordinates →ₗ[Real] ThroatCoverCoordinates)
          (normalSlope • LinearMap.id) := by
      apply LinearMap.ext
      intro vector
      simp [slopeDerivative]
    rw [hSlopeMap, LinearMap.trace_prodMap']
    simp [LinearMap.trace_id]
  rw [hSlope]

/-- The regular construction is precisely Gate 1032's ambient extension with
the normal density pulled back from the throat projection. -/
theorem programPT06RegularAmbientCollarCurrent_eq_extension
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real) :
    programPT06RegularAmbientCollarCurrent throatCurrent normalDensity =
      programPT06ThroatCurrentAmbientExtension throatCurrent
        (fun coordinate =>
          normalDensity (programPT06AmbientThroatProjection coordinate)) := by
  funext coordinate
  apply programPT06AmbientThroatTransverseEquiv.injective
  simp [programPT06RegularAmbientCollarCurrent,
    programPT06RegularProductCollarCurrent,
    programPT06ThroatCurrentAmbientExtension,
    programPT06AmbientThroatProjection,
    programPT06ThroatZeroTransverseEmbedding,
    programPT06PureTransverseEmbedding]

/-- The full ambient first derivative in the chosen transverse direction
vanishes. -/
theorem programPT06RegularAmbientCollarCurrent_transverse_fderiv_zero
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection coordinate))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection coordinate)) :
    fderiv Real
        (programPT06RegularAmbientCollarCurrent throatCurrent normalDensity)
        coordinate (programPT06PureTransverseEmbedding 1) = 0 := by
  rw [(programPT06RegularAmbientCollarCurrent_hasFDerivAt
    hThroat hNormal).fderiv]
  simp [programPT06PureTransverseEmbedding]

/-- The fixed ambient four-divergence of the regular collar current equals
the fixed throat three-divergence. -/
theorem programPT06RegularAmbientCollarCurrent_divergence
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection coordinate))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection coordinate)) :
    programPT06AmbientCoordinateDivergence
        (programPT06RegularAmbientCollarCurrent throatCurrent normalDensity)
        coordinate =
      programPT06ThroatCoordinateDivergence throatCurrent
        (programPT06AmbientThroatProjection coordinate) := by
  rw [programPT06AmbientCoordinateDivergence_eq_trace,
    programPT06ThroatCoordinateDivergence_eq_trace]
  rw [(programPT06RegularAmbientCollarCurrent_hasFDerivAt
    hThroat hNormal).fderiv]
  let productDerivative : ProgramPT06AmbientThroatTransverse4 →L[Real]
      ProgramPT06AmbientThroatTransverse4 :=
    ((fderiv Real throatCurrent
        (programPT06AmbientThroatProjection coordinate)).comp
      (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
    ((fderiv Real normalDensity
        (programPT06AmbientThroatProjection coordinate)).comp
      (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real))
  have hConjugate :
      (programPT06AmbientThroatTransverseEquiv.symm.toContinuousLinearMap.comp
          (productDerivative.comp
            programPT06AmbientThroatTransverseEquiv.toContinuousLinearMap)).toLinearMap =
        programPT06AmbientThroatTransverseEquiv.symm.toLinearEquiv.conj
          productDerivative.toLinearMap := by
    rfl
  rw [hConjugate, LinearMap.trace_conj']
  exact programPT06Trace_productCollarDerivative _ _

/-- The affine ambient extension realizes its prescribed transverse first
jet. -/
theorem programPT06AffineAmbientCollarCurrent_transverse_fderiv
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection coordinate))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection coordinate)) :
    fderiv Real
        (programPT06AffineAmbientCollarCurrent throatCurrent normalDensity
          normalSlope)
        coordinate (programPT06PureTransverseEmbedding 1) =
      programPT06PureTransverseEmbedding normalSlope := by
  rw [(programPT06AffineAmbientCollarCurrent_hasFDerivAt
    hThroat hNormal).fderiv]
  simp [programPT06PureTransverseEmbedding]

/-- The affine normal first jet contributes additively to ambient
divergence. -/
theorem programPT06AffineAmbientCollarCurrent_divergence
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection coordinate))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection coordinate)) :
    programPT06AmbientCoordinateDivergence
        (programPT06AffineAmbientCollarCurrent throatCurrent normalDensity
          normalSlope)
        coordinate =
      programPT06ThroatCoordinateDivergence throatCurrent
          (programPT06AmbientThroatProjection coordinate) + normalSlope := by
  rw [programPT06AmbientCoordinateDivergence_eq_trace,
    programPT06ThroatCoordinateDivergence_eq_trace]
  rw [(programPT06AffineAmbientCollarCurrent_hasFDerivAt
    hThroat hNormal).fderiv]
  let productDerivative : ProgramPT06AmbientThroatTransverse4 →L[Real]
      ProgramPT06AmbientThroatTransverse4 :=
    ((fderiv Real throatCurrent
        (programPT06AmbientThroatProjection coordinate)).comp
      (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)).prod
    (((fderiv Real normalDensity
        (programPT06AmbientThroatProjection coordinate)).comp
      (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real)) +
      normalSlope •
        (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real))
  have hConjugate :
      (programPT06AmbientThroatTransverseEquiv.symm.toContinuousLinearMap.comp
          (productDerivative.comp
            programPT06AmbientThroatTransverseEquiv.toContinuousLinearMap)).toLinearMap =
        programPT06AmbientThroatTransverseEquiv.symm.toLinearEquiv.conj
          productDerivative.toLinearMap := by
    rfl
  rw [hConjugate, LinearMap.trace_conj']
  exact programPT06Trace_affineProductCollarDerivative _ _ _

/-- The affine slope changes only the off-face first jet; the zero slice keeps
the same current value as the regular constant-normal extension. -/
theorem programPT06AffineAmbientCollarCurrent_zeroTransverse
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real)
    (normalSlope : Real) (coordinate : ThroatCoverCoordinates) :
    programPT06AffineAmbientCollarCurrent throatCurrent normalDensity normalSlope
        (programPT06ThroatZeroTransverseEmbedding coordinate) =
      programPT06RegularAmbientCollarCurrent throatCurrent normalDensity
        (programPT06ThroatZeroTransverseEmbedding coordinate) := by
  simp [programPT06AffineAmbientCollarCurrent,
    programPT06RegularAmbientCollarCurrent,
    programPT06AffineProductCollarCurrent,
    programPT06RegularProductCollarCurrent,
    programPT06ThroatZeroTransverseEmbedding]

/-- Regular ambient current built from the affine Cartan slice of a physical
third-jet vector density. -/
def programPT06CartanSliceRegularAmbientCurrent
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06AmbientCurrent4D :=
  programPT06RegularAmbientCollarCurrent
    (programPT06ActualPhysicalThirdJetCartanSliceField
      density coordinate jet frame)
    normalDensity

/-- Affine-normal version of the regular Cartan-slice current. -/
def programPT06CartanSliceAffineAmbientCurrent
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real)
    (normalSlope : Real) : ProgramPT06AmbientCurrent4D :=
  programPT06AffineAmbientCollarCurrent
    (programPT06ActualPhysicalThirdJetCartanSliceField
      density coordinate jet frame)
    normalDensity normalSlope

/-- At the zero-transverse copy of the base point, the ambient divergence of
the regular Cartan-slice current is exactly the joint horizontal differential.
The supplied normal density changes the boundary flux but not this identity. -/
theorem programPT06CartanSliceRegularAmbientCurrent_divergence_eq_dH
    {density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D}
    {coordinate : ThroatCoverCoordinates}
    {jet : ActualPhysicalThirdOrderJetProductFiber}
    {frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D}
    {normalDensity : ThroatCoverCoordinates → Real}
    (hJoint : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        density point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (coordinate, jet))
    (hNormal : DifferentiableAt Real normalDensity coordinate) :
    programPT06AmbientCoordinateDivergence
        (programPT06CartanSliceRegularAmbientCurrent density coordinate jet
          frame normalDensity)
        (programPT06ThroatZeroTransverseEmbedding coordinate) =
      programPT06ActualPhysicalThirdJetJointHorizontalDifferential density
        coordinate jet frame := by
  have hSlice : DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetCartanSliceField
        density coordinate jet frame) coordinate := by
    let joint :=
      fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        density point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2)
    change DifferentiableAt Real
      (joint ∘ programPT06ActualPhysicalThirdJetCartanSlice
        coordinate jet frame) coordinate
    have hJointAtSlice : DifferentiableAt Real joint
        (programPT06ActualPhysicalThirdJetCartanSlice
          coordinate jet frame coordinate) := by
      simpa [joint] using hJoint
    exact hJointAtSlice.comp coordinate
      (programPT06ActualPhysicalThirdJetCartanSlice_hasFDerivAt
        coordinate jet frame).differentiableAt
  unfold programPT06CartanSliceRegularAmbientCurrent
  have hSliceAt : DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetCartanSliceField
        density coordinate jet frame)
      (programPT06AmbientThroatProjection
        (programPT06ThroatZeroTransverseEmbedding coordinate)) := by
    simpa using hSlice
  have hNormalAt : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection
        (programPT06ThroatZeroTransverseEmbedding coordinate)) := by
    simpa using hNormal
  rw [programPT06RegularAmbientCollarCurrent_divergence hSliceAt hNormalAt]
  simp only [programPT06AmbientThroatProjection_zeroTransverse]
  exact (programPT06ActualPhysicalThirdJetJointHorizontalDifferential_eq_divergence_slice
    density coordinate jet frame hJoint).symm

/-- The affine-normal Cartan current has ambient divergence `dH` plus its
prescribed normal slope. -/
theorem programPT06CartanSliceAffineAmbientCurrent_divergence_eq_dH_add_slope
    {density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D}
    {coordinate : ThroatCoverCoordinates}
    {jet : ActualPhysicalThirdOrderJetProductFiber}
    {frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    (hJoint : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        density point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (coordinate, jet))
    (hNormal : DifferentiableAt Real normalDensity coordinate) :
    programPT06AmbientCoordinateDivergence
        (programPT06CartanSliceAffineAmbientCurrent density coordinate jet frame
          normalDensity normalSlope)
        (programPT06ThroatZeroTransverseEmbedding coordinate) =
      programPT06ActualPhysicalThirdJetJointHorizontalDifferential density
          coordinate jet frame + normalSlope := by
  have hSlice : DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetCartanSliceField
        density coordinate jet frame) coordinate := by
    let joint :=
      fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        density point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2)
    change DifferentiableAt Real
      (joint ∘ programPT06ActualPhysicalThirdJetCartanSlice
        coordinate jet frame) coordinate
    have hJointAtSlice : DifferentiableAt Real joint
        (programPT06ActualPhysicalThirdJetCartanSlice
          coordinate jet frame coordinate) := by
      simpa [joint] using hJoint
    exact hJointAtSlice.comp coordinate
      (programPT06ActualPhysicalThirdJetCartanSlice_hasFDerivAt
        coordinate jet frame).differentiableAt
  have hSliceAt : DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetCartanSliceField
        density coordinate jet frame)
      (programPT06AmbientThroatProjection
        (programPT06ThroatZeroTransverseEmbedding coordinate)) := by
    simpa using hSlice
  have hNormalAt : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection
        (programPT06ThroatZeroTransverseEmbedding coordinate)) := by
    simpa using hNormal
  unfold programPT06CartanSliceAffineAmbientCurrent
  rw [programPT06AffineAmbientCollarCurrent_divergence hSliceAt hNormalAt]
  simp only [programPT06AmbientThroatProjection_zeroTransverse]
  rw [← programPT06ActualPhysicalThirdJetJointHorizontalDifferential_eq_divergence_slice
    density coordinate jet frame hJoint]

/-- Choose the normal first jet to cancel the Cartan horizontal differential
at the base point. -/
def programPT06CartanSliceDivergenceFreeAtBaseAmbientCurrent
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06AmbientCurrent4D :=
  programPT06CartanSliceAffineAmbientCurrent density coordinate jet frame
    normalDensity
    (-programPT06ActualPhysicalThirdJetJointHorizontalDifferential
      density coordinate jet frame)

/-- The cancelling affine extension has zero ambient divergence at its base
point. -/
theorem programPT06CartanSliceDivergenceFreeAtBaseAmbientCurrent_divergence
    {density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D}
    {coordinate : ThroatCoverCoordinates}
    {jet : ActualPhysicalThirdOrderJetProductFiber}
    {frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D}
    {normalDensity : ThroatCoverCoordinates → Real}
    (hJoint : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        density point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (coordinate, jet))
    (hNormal : DifferentiableAt Real normalDensity coordinate) :
    programPT06AmbientCoordinateDivergence
        (programPT06CartanSliceDivergenceFreeAtBaseAmbientCurrent
          density coordinate jet frame normalDensity)
        (programPT06ThroatZeroTransverseEmbedding coordinate) = 0 := by
  unfold programPT06CartanSliceDivergenceFreeAtBaseAmbientCurrent
  rw [programPT06CartanSliceAffineAmbientCurrent_divergence_eq_dH_add_slope
    hJoint hNormal]
  exact add_neg_cancel _

/-- Gate 1030's smooth radial physical density supplies the joint
differentiability needed by the Cartan-slice divergence theorem. -/
theorem programPT06T02DegreeFourRadialAutonomousJoint_differentiableAt
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber) :
    DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        programPT06BaseDependentPhysicalVectorDensityOfAutonomous
            (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
              period hPeriod functional)
          point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (coordinate, jet) := by
  let radial :=
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
      period hPeriod functional
  let radialOnTotal :=
    fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
      radial point.2
  have hRadial : ContDiff Real ∞ radial :=
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_contDiff
      period hPeriod functional
  have hRadialOnTotal : ContDiff Real ∞ radialOnTotal :=
    hRadial.comp contDiff_snd
  simpa [programPT06BaseDependentPhysicalVectorDensityOfAutonomous,
    radial, radialOnTotal,
    programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv] using
    hRadialOnTotal.contDiffAt.differentiableAt (by simp)

/-- Gate 1030's actual radial physical J3 density, restricted to its affine
Cartan slice and extended regularly across the chosen transverse coordinate. -/
def programPT06T02DegreeFourRadialCartanSliceRegularAmbientCurrent
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06AmbientCurrent4D :=
  programPT06CartanSliceRegularAmbientCurrent
    (programPT06BaseDependentPhysicalVectorDensityOfAutonomous
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional))
    coordinate jet frame normalDensity

/-- For the actual radial physical J3 density, smoothness from Gate 1030
discharges the joint regularity hypothesis: ambient divergence is exactly its
joint Cartan horizontal differential. -/
theorem
    programPT06T02DegreeFourRadialCartanSliceRegularAmbientCurrent_divergence_eq_dH
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real)
    (hNormal : DifferentiableAt Real normalDensity coordinate) :
    programPT06AmbientCoordinateDivergence
        (programPT06T02DegreeFourRadialCartanSliceRegularAmbientCurrent
          period hPeriod functional coordinate jet frame normalDensity)
        (programPT06ThroatZeroTransverseEmbedding coordinate) =
      programPT06ActualPhysicalThirdJetJointHorizontalDifferential
        (programPT06BaseDependentPhysicalVectorDensityOfAutonomous
          (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
            period hPeriod functional))
        coordinate jet frame := by
  unfold programPT06T02DegreeFourRadialCartanSliceRegularAmbientCurrent
  exact programPT06CartanSliceRegularAmbientCurrent_divergence_eq_dH
    (programPT06T02DegreeFourRadialAutonomousJoint_differentiableAt
      period hPeriod functional coordinate jet)
    hNormal

/-- Radial Cartan current with the unique constant normal slope that cancels
its joint horizontal differential at the selected base point. -/
def programPT06T02DegreeFourRadialCartanSliceDivergenceFreeAtBaseAmbientCurrent
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real) :
    ProgramPT06AmbientCurrent4D :=
  programPT06CartanSliceDivergenceFreeAtBaseAmbientCurrent
    (programPT06BaseDependentPhysicalVectorDensityOfAutonomous
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional))
    coordinate jet frame normalDensity

/-- The regular radial current with cancelling normal first jet is ambient
divergence-free at the selected zero-transverse point. -/
theorem
    programPT06T02DegreeFourRadialCartanSliceDivergenceFreeAtBaseAmbientCurrent_divergence
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (coordinate : ThroatCoverCoordinates)
    (jet : ActualPhysicalThirdOrderJetProductFiber)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (normalDensity : ThroatCoverCoordinates → Real)
    (hNormal : DifferentiableAt Real normalDensity coordinate) :
    programPT06AmbientCoordinateDivergence
        (programPT06T02DegreeFourRadialCartanSliceDivergenceFreeAtBaseAmbientCurrent
          period hPeriod functional coordinate jet frame normalDensity)
        (programPT06ThroatZeroTransverseEmbedding coordinate) = 0 := by
  unfold
    programPT06T02DegreeFourRadialCartanSliceDivergenceFreeAtBaseAmbientCurrent
  exact programPT06CartanSliceDivergenceFreeAtBaseAmbientCurrent_divergence
    (programPT06T02DegreeFourRadialAutonomousJoint_differentiableAt
      period hPeriod functional coordinate jet)
    hNormal

end
end P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D
end JanusFormal
