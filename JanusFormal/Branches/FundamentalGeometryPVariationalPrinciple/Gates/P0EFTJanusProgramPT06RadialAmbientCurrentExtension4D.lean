import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanPiolaNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientNullFluxPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricCoupledScalarMatterJetVariation

/-!
# Local ambient extension of the radial throat current

This gate fixes a local linear split of the ambient four-space into the
existing three-dimensional throat coordinates and one transverse coordinate.
It extends a throat current by an explicitly supplied transverse component,
recovers the throat current by projection, and specializes the construction to
the actual physical third-jet radial Cartan density from Gate 1030.  On a
genuine mobile null face, a nondegenerate rigging also gives a normalized
set-theoretic extension whose pulled-back flux is a prescribed scalar density.

The split, physical third-jet section, and rigging remain local data.  The
set-theoretic extension has no asserted regularity or transverse-jet control.
No global bulk/null incidence, ambient atlas covariance, integration, or
Stokes theorem is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D

/-- Local throat/transverse model of the ambient four-space. -/
abbrev ProgramPT06AmbientThroatTransverse4 :=
  ThroatCoverCoordinates × Real

/-- Four-component holonomic carrier used by the bulk jet calculus. -/
abbrev ProgramPT06HolonomicCoordinate4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Coordinate identification between the finite-null ambient Euclidean space
and the bulk holonomic four-vector carrier.  This is not an incidence map. -/
def programPT06AmbientHolonomicEquiv :
    ProgramPT06AmbientCoordinate4 ≃L[Real] ProgramPT06HolonomicCoordinate4 :=
  EuclideanSpace.equiv (Fin 4) Real

/-- An arbitrary fixed local linear split into throat and transverse
coordinates. -/
def programPT06AmbientThroatTransverseEquiv :
    ProgramPT06AmbientCoordinate4 ≃L[Real]
      ProgramPT06AmbientThroatTransverse4 :=
  ContinuousLinearEquiv.ofFinrankEq (by
    norm_num [ProgramPT06AmbientCoordinate4,
      ProgramPT06AmbientThroatTransverse4, ThroatCoverCoordinates,
      FiniteNullFaceAmbientCoordinate4])

/-- Tangential projection associated with the chosen split. -/
def programPT06AmbientThroatProjection :
    ProgramPT06AmbientCoordinate4 →L[Real] ThroatCoverCoordinates :=
  (ContinuousLinearMap.fst Real ThroatCoverCoordinates Real).comp
    programPT06AmbientThroatTransverseEquiv.toContinuousLinearMap

/-- Transverse projection associated with the chosen split. -/
def programPT06AmbientTransverseProjection :
    ProgramPT06AmbientCoordinate4 →L[Real] Real :=
  (ContinuousLinearMap.snd Real ThroatCoverCoordinates Real).comp
    programPT06AmbientThroatTransverseEquiv.toContinuousLinearMap

/-- Embed a throat vector with zero transverse component. -/
def programPT06ThroatZeroTransverseEmbedding :
    ThroatCoverCoordinates →L[Real] ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientThroatTransverseEquiv.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl Real ThroatCoverCoordinates Real)

/-- Embed a scalar purely in the transverse direction. -/
def programPT06PureTransverseEmbedding :
    Real →L[Real] ProgramPT06AmbientCoordinate4 :=
  programPT06AmbientThroatTransverseEquiv.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr Real ThroatCoverCoordinates Real)

/-- Exchange parameter/screen source coordinates with the throat's
screen/time ordering.  No orientation claim is attached to this exchange. -/
def programPT06NullSourceToThroatEquiv :
    ProgramPT06NullFaceSource3 ≃L[Real] ThroatCoverCoordinates :=
  ContinuousLinearEquiv.prodComm Real Real FiniteNullFaceScreenCoordinate2

@[simp] theorem programPT06AmbientThroatProjection_zeroTransverse
    (vector : ThroatCoverCoordinates) :
    programPT06AmbientThroatProjection
        (programPT06ThroatZeroTransverseEmbedding vector) = vector := by
  simp [programPT06AmbientThroatProjection,
    programPT06ThroatZeroTransverseEmbedding]

@[simp] theorem programPT06AmbientTransverseProjection_zeroTransverse
    (vector : ThroatCoverCoordinates) :
    programPT06AmbientTransverseProjection
        (programPT06ThroatZeroTransverseEmbedding vector) = 0 := by
  simp [programPT06AmbientTransverseProjection,
    programPT06ThroatZeroTransverseEmbedding]

@[simp] theorem programPT06AmbientThroatProjection_pureTransverse
    (scalar : Real) :
    programPT06AmbientThroatProjection
        (programPT06PureTransverseEmbedding scalar) = 0 := by
  simp [programPT06AmbientThroatProjection,
    programPT06PureTransverseEmbedding]

@[simp] theorem programPT06AmbientTransverseProjection_pureTransverse
    (scalar : Real) :
    programPT06AmbientTransverseProjection
        (programPT06PureTransverseEmbedding scalar) = scalar := by
  simp [programPT06AmbientTransverseProjection,
    programPT06PureTransverseEmbedding]

/-- A current and three tangent directions carried by the same
three-dimensional throat subspace have zero ambient four-volume. -/
theorem programPT06ThroatTangentialFlux_zero
    (vector : ThroatCoverCoordinates)
    (frame : Fin 3 → ThroatCoverCoordinates) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06ThroatZeroTransverseEmbedding vector)
        (programPT06ThroatZeroTransverseEmbedding ∘ frame) = 0 := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply]
  apply programPT06AmbientSignedVolume.toAlternatingMap.map_linearDependent
  intro hAmbient
  let vectors : Fin 4 → ThroatCoverCoordinates := Matrix.vecCons vector frame
  have hSource : LinearIndependent Real vectors := by
    apply LinearIndependent.of_comp
      programPT06ThroatZeroTransverseEmbedding.toLinearMap
    have hFamily :
        programPT06ThroatZeroTransverseEmbedding ∘ vectors =
          Matrix.vecCons
            (programPT06ThroatZeroTransverseEmbedding vector)
            (programPT06ThroatZeroTransverseEmbedding ∘ frame) := by
      funext direction
      refine Fin.cases ?_ (fun screenDirection => ?_) direction <;> rfl
    change LinearIndependent Real
      (programPT06ThroatZeroTransverseEmbedding ∘ vectors)
    rw [hFamily]
    exact hAmbient
  have hDimension := hSource.fintype_card_le_finrank
  norm_num [vectors, ThroatCoverCoordinates] at hDimension

/-- Extend a throat current by a separately supplied transverse component. -/
def programPT06ThroatCurrentAmbientExtension
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real) :
    ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    programPT06ThroatZeroTransverseEmbedding
        (throatCurrent (programPT06AmbientThroatProjection coordinate)) +
      programPT06PureTransverseEmbedding (transverseCurrent coordinate)

/-- On any throat tangent frame, only the explicitly supplied transverse
component contributes to the ambient flux. -/
theorem programPT06ThroatCurrentAmbientExtension_tangentFlux
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real)
    (coordinate : ProgramPT06AmbientCoordinate4)
    (frame : Fin 3 → ThroatCoverCoordinates) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06ThroatCurrentAmbientExtension
          throatCurrent transverseCurrent coordinate)
        (programPT06ThroatZeroTransverseEmbedding ∘ frame) =
      transverseCurrent coordinate •
        programPT06AmbientSignedVolume.curryLeft
          (programPT06PureTransverseEmbedding 1)
          (programPT06ThroatZeroTransverseEmbedding ∘ frame) := by
  unfold programPT06ThroatCurrentAmbientExtension
  rw [map_add]
  simp only [ContinuousAlternatingMap.add_apply]
  rw [programPT06ThroatTangentialFlux_zero, zero_add]
  have hTransverse :
      programPT06PureTransverseEmbedding (transverseCurrent coordinate) =
        transverseCurrent coordinate •
          programPT06PureTransverseEmbedding 1 := by
    rw [← map_smul]
    simp
  rw [hTransverse]
  simp

/-- Tangential projection recovers the supplied throat current. -/
@[simp] theorem programPT06ThroatCurrentAmbientExtension_throatProjection
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientThroatProjection
        (programPT06ThroatCurrentAmbientExtension
          throatCurrent transverseCurrent coordinate) =
      throatCurrent (programPT06AmbientThroatProjection coordinate) := by
  simp [programPT06ThroatCurrentAmbientExtension]

/-- Transverse projection recovers the independently supplied component. -/
@[simp] theorem programPT06ThroatCurrentAmbientExtension_transverseProjection
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientTransverseProjection
        (programPT06ThroatCurrentAmbientExtension
          throatCurrent transverseCurrent coordinate) =
      transverseCurrent coordinate := by
  simp [programPT06ThroatCurrentAmbientExtension]

/-- The actual Gate-1030 radial Cartan vector density, evaluated on a supplied
local physical third-jet section, with an explicit transverse completion. -/
def programPT06T02DegreeFourRadialAmbientCurrent
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ThroatCoverCoordinates →
      ActualPhysicalThirdOrderJetProductFiber)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real) :
    ProgramPT06AmbientCurrent4D :=
  programPT06ThroatCurrentAmbientExtension
    (fun coordinate =>
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional (jetSection coordinate))
    transverseCurrent

/-- Restricting the ambient completion to the zero-transverse throat and then
projecting recovers exactly Gate 1030's radial physical J3 density. -/
@[simp] theorem programPT06T02DegreeFourRadialAmbientCurrent_zeroTransverse_restrict
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ThroatCoverCoordinates →
      ActualPhysicalThirdOrderJetProductFiber)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real)
    (coordinate : ThroatCoverCoordinates) :
    programPT06AmbientThroatProjection
        (programPT06T02DegreeFourRadialAmbientCurrent period hPeriod functional
          jetSection transverseCurrent
          (programPT06ThroatZeroTransverseEmbedding coordinate)) =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional (jetSection coordinate) := by
  simp [programPT06T02DegreeFourRadialAmbientCurrent]

/-- The transverse projection of the radial ambient completion is precisely
the supplied transverse component. -/
@[simp] theorem programPT06T02DegreeFourRadialAmbientCurrent_transverseProjection
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ThroatCoverCoordinates →
      ActualPhysicalThirdOrderJetProductFiber)
    (transverseCurrent : ProgramPT06AmbientCoordinate4 → Real)
    (coordinate : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientTransverseProjection
        (programPT06T02DegreeFourRadialAmbientCurrent period hPeriod functional
          jetSection transverseCurrent coordinate) =
      transverseCurrent coordinate := by
  simp [programPT06T02DegreeFourRadialAmbientCurrent]

/-- Encode a throat vector in the genuine tangent frame using the explicit
inverse parameter/screen-to-throat exchange. -/
def programPT06RadialTangentialBoundaryLift
    (frame : Fin 3 → ProgramPT06AmbientCoordinate4)
    (radial : ThroatCoverCoordinates) : ProgramPT06AmbientCoordinate4 :=
  radial.2 • frame 0 +
    ∑ direction : Fin 2, radial.1 direction • frame direction.succ

private theorem programPT06AmbientSignedVolume_curry_frame_self_zero
    (frame : Fin 3 → ProgramPT06AmbientCoordinate4) (direction : Fin 3) :
    programPT06AmbientSignedVolume.curryLeft (frame direction) frame = 0 := by
  rw [ContinuousAlternatingMap.curryLeft_apply_apply]
  exact programPT06AmbientSignedVolume.map_eq_zero_of_eq
    (Matrix.vecCons (frame direction) frame)
    (i := (0 : Fin 4)) (j := direction.succ) (by simp)
    (Fin.succ_ne_zero direction).symm

/-- The boundary lift of the three-component radial current is tangent, hence
its four-dimensional flux through the same face vanishes. -/
theorem programPT06RadialTangentialBoundaryLift_flux_zero
    (frame : Fin 3 → ProgramPT06AmbientCoordinate4)
    (radial : ThroatCoverCoordinates) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06RadialTangentialBoundaryLift frame radial) frame = 0 := by
  simp only [programPT06RadialTangentialBoundaryLift, map_add, map_sum, map_smul,
    ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply,
    programPT06AmbientSignedVolume_curry_frame_self_zero,
    smul_zero, Finset.sum_const_zero, add_zero]

/-- Honest interface between an ambient current and its restriction to a
genuine mobile null face.  The transverse rigging is normalized against the
actual generator/screen frame; existence and regularity of a common collar
extension are deliberately left for the incidence gate. -/
structure ProgramPT06RadialAmbientExtensionDatum
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real) where
  transverse : ProgramPT06NullFaceSource3 → ProgramPT06AmbientCoordinate4
  transverse_normalized : ∀ source,
    programPT06AmbientSignedVolume.curryLeft (transverse source)
      (programPT06FiniteNullFaceGeometricTangentFrame
        geometry input face source) = 1
  current : ProgramPT06AmbientCurrent4D
  current_on_face : ∀ source,
    current (geometry.embedding input face source) =
      programPT06RadialTangentialBoundaryLift
        (programPT06FiniteNullFaceGeometricTangentFrame
          geometry input face source)
        (radial source) + density source • transverse source

/-- Normalize a supplied nondegenerate transverse rigging against the genuine
null-face tangent frame. -/
def programPT06NormalizedNullFaceTransverse
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace)
    (rawTransverse : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4) :
    ProgramPT06NullFaceSource3 → ProgramPT06AmbientCoordinate4 :=
  fun source =>
    (programPT06AmbientSignedVolume.curryLeft (rawTransverse source)
      (programPT06FiniteNullFaceGeometricTangentFrame
        geometry input face source))⁻¹ • rawTransverse source

theorem programPT06NormalizedNullFaceTransverse_flux
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace)
    (rawTransverse : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4)
    (hRawTransverse : ∀ source,
      programPT06AmbientSignedVolume.curryLeft (rawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          geometry input face source) ≠ 0)
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06NormalizedNullFaceTransverse
          geometry input face rawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          geometry input face source) = 1 := by
  unfold programPT06NormalizedNullFaceTransverse
  rw [map_smul]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact inv_mul_cancel₀ (hRawTransverse source)

/-- Totalize boundary data by the set-theoretic inverse of an injective null
embedding.  Values away from the image are arbitrary and no regularity is
claimed. -/
def programPT06SetTheoreticNullFaceAmbientExtension
    (embedding : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4)
    (boundaryCurrent : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4) :
    ProgramPT06AmbientCurrent4D :=
  boundaryCurrent ∘ Function.invFun embedding

@[simp] theorem programPT06SetTheoreticNullFaceAmbientExtension_on_face
    (embedding : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4)
    (boundaryCurrent : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4)
    (hEmbedding : Function.Injective embedding)
    (source : ProgramPT06NullFaceSource3) :
    programPT06SetTheoreticNullFaceAmbientExtension embedding boundaryCurrent
        (embedding source) = boundaryCurrent source := by
  unfold programPT06SetTheoreticNullFaceAmbientExtension
  rw [Function.comp_apply, Function.leftInverse_invFun hEmbedding source]

/-- A nondegenerate raw rigging produces an actual set-theoretic extension
datum on one mobile null face. -/
def ProgramPT06RadialAmbientExtensionDatum.setTheoreticOfRawTransverse
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real)
    (rawTransverse : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4)
    (hRawTransverse : ∀ source,
      programPT06AmbientSignedVolume.curryLeft (rawTransverse source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          geometry input face source) ≠ 0) :
    ProgramPT06RadialAmbientExtensionDatum
      geometry input face radial density where
  transverse := programPT06NormalizedNullFaceTransverse
    geometry input face rawTransverse
  transverse_normalized :=
    programPT06NormalizedNullFaceTransverse_flux
      geometry input face rawTransverse hRawTransverse
  current := programPT06SetTheoreticNullFaceAmbientExtension
    (geometry.embedding input face)
    (fun source =>
      programPT06RadialTangentialBoundaryLift
          (programPT06FiniteNullFaceGeometricTangentFrame
            geometry input face source)
          (radial source) +
        density source • programPT06NormalizedNullFaceTransverse
          geometry input face rawTransverse source)
  current_on_face := by
    intro source
    exact programPT06SetTheoreticNullFaceAmbientExtension_on_face
      (geometry.embedding input face) _
        (geometry.embedding_injective input hInput face) source

/-- A normalized transverse completion has exactly the prescribed scalar
flux on the genuine mobile null face; the radial throat vector remains encoded
in the tangential part of the ambient current. -/
theorem programPT06RadialAmbientExtensionDatum_flux_eq_density
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (radial : ProgramPT06NullFaceSource3 → ThroatCoverCoordinates)
    (density : ProgramPT06NullFaceSource3 → Real)
    (datum : ProgramPT06RadialAmbientExtensionDatum
      geometry input face radial density)
    (source : ProgramPT06NullFaceSource3) :
    programPT06NullFaceFluxPullback (geometry.embedding input face)
        datum.current source programPT06NullFaceSourceFrame = density source := by
  rw [programPT06FiniteNullFaceFluxPullback_tangent_formula
    geometry input hInput face]
  rw [datum.current_on_face]
  rw [map_add]
  simp only [ContinuousAlternatingMap.add_apply]
  rw [programPT06RadialTangentialBoundaryLift_flux_zero]
  rw [map_smul]
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [datum.transverse_normalized]
  simp

/-- Gate 1030's physical radial density, read on the null source through the
explicit parameter/screen-to-throat exchange. -/
def programPT06T02DegreeFourRadialNullFaceVectorDensity
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ThroatCoverCoordinates →
      ActualPhysicalThirdOrderJetProductFiber) :
    ProgramPT06NullFaceSource3 → ThroatCoverCoordinates :=
  fun source =>
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
      period hPeriod functional
      (jetSection (programPT06NullSourceToThroatEquiv source))

/-- The boundary value of a specialized datum contains Gate 1030's radial
vector in the genuine tangent frame and the prescribed transverse flux term. -/
theorem programPT06T02DegreeFourRadialAmbientExtension_current_on_face
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace)
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ThroatCoverCoordinates →
      ActualPhysicalThirdOrderJetProductFiber)
    (density : ProgramPT06NullFaceSource3 → Real)
    (datum : ProgramPT06RadialAmbientExtensionDatum geometry input face
      (programPT06T02DegreeFourRadialNullFaceVectorDensity
        period hPeriod functional jetSection) density)
    (source : ProgramPT06NullFaceSource3) :
    datum.current (geometry.embedding input face source) =
      programPT06RadialTangentialBoundaryLift
        (programPT06FiniteNullFaceGeometricTangentFrame
          geometry input face source)
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
          period hPeriod functional
          (jetSection (programPT06NullSourceToThroatEquiv source))) +
        density source • datum.transverse source := by
  exact datum.current_on_face source

/-- The genuine-face extension theorem specialized to the actual Gate-1030
radial current. -/
theorem programPT06T02DegreeFourRadialAmbientExtension_withPrescribedFlux_eq_density
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jetSection : ThroatCoverCoordinates →
      ActualPhysicalThirdOrderJetProductFiber)
    (density : ProgramPT06NullFaceSource3 → Real)
    (datum : ProgramPT06RadialAmbientExtensionDatum geometry input face
      (programPT06T02DegreeFourRadialNullFaceVectorDensity
        period hPeriod functional jetSection) density)
    (source : ProgramPT06NullFaceSource3) :
    programPT06NullFaceFluxPullback (geometry.embedding input face)
        datum.current source programPT06NullFaceSourceFrame = density source := by
  exact programPT06RadialAmbientExtensionDatum_flux_eq_density
    geometry input hInput face
      (programPT06T02DegreeFourRadialNullFaceVectorDensity
        period hPeriod functional jetSection)
    density datum source

end
end P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
end JanusFormal
