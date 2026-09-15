import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

/-!
# Ambient four-current and null-face flux pullback

This gate constructs the four-dimensional local current carrier needed before
the integrated bulk-to-null incidence step.  A current is contracted with the
fixed oriented ambient volume form to give a three-form.  The three-form pulls
back along the existing mobile null-face embeddings, evaluates on their actual
generator/screen tangent frame, and obeys pullback functoriality under
differentiable source and ambient map composition.  For inverse ambient
Jacobians, its signed Piola vector-density transform gives exactly the same
pulled-back flux.

No bulk-boundary incidence or Stokes integration is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientNullFluxPullback4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Module Set
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

/-- Ambient coordinate space used by the finite null-face realization. -/
abbrev ProgramPT06AmbientCoordinate4 := FiniteNullFaceAmbientCoordinate4

/-- Parameter times the two-dimensional screen coordinate. -/
abbrev ProgramPT06NullFaceSource3 := Real × FiniteNullFaceScreenCoordinate2

/-- A local four-dimensional current in ambient coordinates. -/
abbrev ProgramPT06AmbientCurrent4D :=
  ProgramPT06AmbientCoordinate4 → ProgramPT06AmbientCoordinate4

/-- Fixed coordinate basis of the ambient four-space. -/
def programPT06AmbientCoordinateBasis :
    Basis (Fin 4) Real ProgramPT06AmbientCoordinate4 :=
  (EuclideanSpace.basisFun (Fin 4) Real).toBasis

/-- Signed ambient four-volume selected by the fixed coordinate basis. -/
def programPT06AmbientSignedVolume :
    ProgramPT06AmbientCoordinate4 [⋀^Fin 4]→L[Real] Real :=
  { programPT06AmbientCoordinateBasis.det with
    cont := by
      change Continuous (fun vectors =>
        Matrix.det (programPT06AmbientCoordinateBasis.toMatrix vectors))
      exact programPT06AmbientCoordinateBasis.continuous_toMatrix.matrix_det }

@[simp] theorem programPT06AmbientSignedVolume_apply_basis :
    programPT06AmbientSignedVolume programPT06AmbientCoordinateBasis = 1 := by
  change programPT06AmbientCoordinateBasis.det
      programPT06AmbientCoordinateBasis = 1
  exact programPT06AmbientCoordinateBasis.det_self

private theorem programPT06AmbientSignedVolume_insert_basis
    (direction : Fin 4) (vector : ProgramPT06AmbientCoordinate4) :
    programPT06AmbientSignedVolume
        (direction.insertNth vector
          (direction.removeNth programPT06AmbientCoordinateBasis)) =
      programPT06AmbientCoordinateBasis.equivFun vector direction := by
  rw [Fin.insertNth_removeNth]
  change programPT06AmbientCoordinateBasis.det
      (Function.update programPT06AmbientCoordinateBasis direction vector) =
    programPT06AmbientCoordinateBasis.repr vector direction
  rw [Basis.det_apply, Basis.toMatrix_update, Basis.toMatrix_self]
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

private theorem programPT06AmbientSignedVolume_curry_remove_basis
    (direction : Fin 4) (vector : ProgramPT06AmbientCoordinate4) :
    (-1 : Int) ^ direction.val •
        programPT06AmbientSignedVolume.curryLeft vector
          (direction.removeNth programPT06AmbientCoordinateBasis) =
      programPT06AmbientCoordinateBasis.equivFun vector direction := by
  calc
    _ = programPT06AmbientSignedVolume
        (direction.insertNth vector
          (direction.removeNth programPT06AmbientCoordinateBasis)) := by
      symm
      simpa [ContinuousAlternatingMap.curryLeft_apply_apply] using
        programPT06AmbientSignedVolume.toAlternatingMap.map_insertNth
          direction vector
          (direction.removeNth programPT06AmbientCoordinateBasis)
    _ = _ := programPT06AmbientSignedVolume_insert_basis direction vector

/-- Flux three-form obtained by contracting the ambient volume with a current. -/
def programPT06AmbientFluxThreeForm
    (current : ProgramPT06AmbientCurrent4D) :
    ProgramPT06AmbientCoordinate4 →
      ProgramPT06AmbientCoordinate4 [⋀^Fin 3]→L[Real] Real :=
  fun coordinate => programPT06AmbientSignedVolume.curryLeft (current coordinate)

/-- Coordinate divergence of an ambient current. -/
def programPT06AmbientCoordinateDivergence
    (current : ProgramPT06AmbientCurrent4D)
    (coordinate : ProgramPT06AmbientCoordinate4) : Real :=
  ∑ direction : Fin 4,
    programPT06AmbientCoordinateBasis.equivFun
      (fderiv Real current coordinate
        (programPT06AmbientCoordinateBasis direction)) direction

private theorem programPT06AmbientFluxThreeForm_differentiableAt
    {current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hCurrent : DifferentiableAt Real current coordinate) :
    DifferentiableAt Real (programPT06AmbientFluxThreeForm current) coordinate :=
  programPT06AmbientSignedVolume.curryLeft.differentiableAt.comp coordinate hCurrent

/-- The exterior derivative of the ambient flux is current divergence times
the signed ambient volume. -/
theorem programPT06AmbientFluxThreeForm_extDeriv
    {current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hCurrent : DifferentiableAt Real current coordinate) :
    extDeriv (programPT06AmbientFluxThreeForm current) coordinate =
      programPT06AmbientCoordinateDivergence current coordinate •
        programPT06AmbientSignedVolume := by
  have hFlux : DifferentiableAt Real
      (programPT06AmbientFluxThreeForm current) coordinate :=
    programPT06AmbientFluxThreeForm_differentiableAt hCurrent
  have hFluxDerivative : HasFDerivAt
      (programPT06AmbientFluxThreeForm current)
      (programPT06AmbientSignedVolume.curryLeft.comp
        (fderiv Real current coordinate)) coordinate :=
    programPT06AmbientSignedVolume.curryLeft.hasFDerivAt.comp coordinate
      hCurrent.hasFDerivAt
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [(extDeriv (programPT06AmbientFluxThreeForm current) coordinate).toAlternatingMap
    |>.eq_smul_basis_det programPT06AmbientCoordinateBasis]
  have hEvaluation :
      (extDeriv (programPT06AmbientFluxThreeForm current) coordinate).toAlternatingMap
          programPT06AmbientCoordinateBasis =
        programPT06AmbientCoordinateDivergence current coordinate := by
    change extDeriv (programPT06AmbientFluxThreeForm current) coordinate
        programPT06AmbientCoordinateBasis = _
    rw [extDeriv_apply hFlux programPT06AmbientCoordinateBasis]
    unfold programPT06AmbientCoordinateDivergence
    apply Finset.sum_congr rfl
    intro direction _
    rw [fderiv_continuousAlternatingMap_apply_const_apply hFlux]
    rw [hFluxDerivative.fderiv]
    simpa only [ContinuousLinearMap.comp_apply] using
      programPT06AmbientSignedVolume_curry_remove_basis direction
        (fderiv Real current coordinate
          (programPT06AmbientCoordinateBasis direction))
  rw [hEvaluation]
  rfl

/-- A signed ambient top form acquires the determinant of a linear map. -/
theorem programPT06AmbientSignedTopForm_comp
    (form : ProgramPT06AmbientCoordinate4 [⋀^Fin 4]→L[Real] Real)
    (linear : ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4) :
    form.compContinuousLinearMap linear =
      LinearMap.det linear.toLinearMap • form := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [(form.compContinuousLinearMap linear).toAlternatingMap
    |>.eq_smul_basis_det programPT06AmbientCoordinateBasis]
  rw [(LinearMap.det linear.toLinearMap • form).toAlternatingMap
    |>.eq_smul_basis_det programPT06AmbientCoordinateBasis]
  have hEvaluation :
      (form.compContinuousLinearMap linear).toAlternatingMap
          programPT06AmbientCoordinateBasis =
        LinearMap.det linear.toLinearMap *
          form programPT06AmbientCoordinateBasis := by
    change (form.compContinuousLinearMap linear)
        programPT06AmbientCoordinateBasis = _
    change form.toAlternatingMap
        (linear ∘ programPT06AmbientCoordinateBasis) = _
    rw [form.toAlternatingMap.eq_smul_basis_det
      programPT06AmbientCoordinateBasis]
    have hDet :
        programPT06AmbientCoordinateBasis.det
            (linear ∘ programPT06AmbientCoordinateBasis) =
          LinearMap.det linear.toLinearMap := by
      convert programPT06AmbientCoordinateBasis.det_comp linear.toLinearMap
        programPT06AmbientCoordinateBasis using 1
      · rfl
      · simp only [programPT06AmbientCoordinateBasis.det_self, mul_one]
    simp only [AlternatingMap.smul_apply, smul_eq_mul]
    rw [hDet]
    exact mul_comm _ _
  rw [hEvaluation]
  rfl

private theorem programPT06AmbientLinear_rightInverse_of_leftInverse
    (forward reverse : ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4)
    (hLeft : reverse.comp forward =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4) :
    forward.comp reverse =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4 := by
  have hLeftPointwise : Function.LeftInverse reverse forward := by
    intro vector
    have hApplied := congrArg (fun operator => operator vector) hLeft
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  have hForwardSurjective : Function.Surjective forward :=
    LinearMap.surjective_of_injective hLeftPointwise.injective
  have hRightPointwise : Function.RightInverse reverse forward :=
    hLeftPointwise.rightInverse_of_surjective hForwardSurjective
  apply ContinuousLinearMap.ext
  intro vector
  exact hRightPointwise vector

/-- Pulling back a flux through inverse ambient linear maps equals the flux of
the signed vector-density pullback. -/
theorem programPT06AmbientSignedFlux_comp
    (forward reverse : ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4)
    (vector : ProgramPT06AmbientCoordinate4)
    (hLeft : reverse.comp forward =
      ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4) :
    (programPT06AmbientSignedVolume.curryLeft vector).compContinuousLinearMap
        forward =
      programPT06AmbientSignedVolume.curryLeft
        (LinearMap.det forward.toLinearMap • reverse vector) := by
  have hRight :=
    programPT06AmbientLinear_rightInverse_of_leftInverse forward reverse hLeft
  have hRightApply : forward (reverse vector) = vector := by
    have hApplied := congrArg (fun operator => operator vector) hRight
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hApplied
  calc
    _ = (programPT06AmbientSignedVolume.curryLeft
        (forward (reverse vector))).compContinuousLinearMap forward := by
      rw [hRightApply]
    _ = (programPT06AmbientSignedVolume.compContinuousLinearMap forward).curryLeft
        (reverse vector) := by
      symm
      exact ContinuousAlternatingMap.curryLeft_compContinuousLinearMap
        programPT06AmbientSignedVolume forward (reverse vector)
    _ = (LinearMap.det forward.toLinearMap •
        programPT06AmbientSignedVolume).curryLeft (reverse vector) := by
      rw [programPT06AmbientSignedTopForm_comp]
    _ = _ := by simp

/-- Signed ambient vector-density pullback formed from forward and reverse
Jacobians at corresponding points. -/
def programPT06AmbientSignedVectorPullback
    (forward reverse current : ProgramPT06AmbientCurrent4D) :
    ProgramPT06AmbientCurrent4D :=
  fun coordinate =>
    LinearMap.det (fderiv Real forward coordinate).toLinearMap •
      fderiv Real reverse (forward coordinate) (current (forward coordinate))

/-- At inverse Jacobians, signed vector-density and differential-form
pullbacks give exactly the same ambient flux three-form. -/
theorem programPT06AmbientSignedVectorPullback_fluxThreeForm_eq_at
    {forward reverse current : ProgramPT06AmbientCurrent4D}
    {coordinate : ProgramPT06AmbientCoordinate4}
    (hInverse :
      (fderiv Real reverse (forward coordinate)).comp
          (fderiv Real forward coordinate) =
        ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4) :
    programPT06AmbientFluxThreeForm
        (programPT06AmbientSignedVectorPullback forward reverse current)
        coordinate =
      (programPT06AmbientFluxThreeForm current
        (forward coordinate)).compContinuousLinearMap
          (fderiv Real forward coordinate) := by
  unfold programPT06AmbientFluxThreeForm
    programPT06AmbientSignedVectorPullback
  exact (programPT06AmbientSignedFlux_comp
    (fderiv Real forward coordinate)
    (fderiv Real reverse (forward coordinate))
    (current (forward coordinate)) hInverse).symm

/-- Pullback of a three-form field along a differentiable coordinate map. -/
def programPT06ThreeFormPullback
    {Source Target : Type*}
    [NormedAddCommGroup Source] [NormedSpace Real Source]
    [NormedAddCommGroup Target] [NormedSpace Real Target]
    (coordinateMap : Source → Target)
    (form : Target → Target [⋀^Fin 3]→L[Real] Real) :
    Source → Source [⋀^Fin 3]→L[Real] Real :=
  fun coordinate =>
    (form (coordinateMap coordinate)).compContinuousLinearMap
      (fderiv Real coordinateMap coordinate)

/-- Pullback is functorial at every point where the two maps are
differentiable. -/
theorem programPT06ThreeFormPullback_comp
    {First Second Third : Type*}
    [NormedAddCommGroup First] [NormedSpace Real First]
    [NormedAddCommGroup Second] [NormedSpace Real Second]
    [NormedAddCommGroup Third] [NormedSpace Real Third]
    (outer : Second → Third) (inner : First → Second)
    (form : Third → Third [⋀^Fin 3]→L[Real] Real)
    (coordinate : First)
    (hOuter : DifferentiableAt Real outer (inner coordinate))
    (hInner : DifferentiableAt Real inner coordinate) :
    programPT06ThreeFormPullback (outer ∘ inner) form coordinate =
      programPT06ThreeFormPullback inner
        (programPT06ThreeFormPullback outer form) coordinate := by
  apply ContinuousAlternatingMap.ext
  intro vectors
  simp only [programPT06ThreeFormPullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [fderiv_comp coordinate hOuter hInner]
  rfl

/-- Standard parameter/screen frame on a null-face source chart. -/
def programPT06NullFaceSourceFrame :
    Fin 3 → ProgramPT06NullFaceSource3 :=
  Fin.cases (1, 0)
    (fun direction : Fin 2 =>
      (0, EuclideanSpace.single direction 1))

/-- Actual tangent frame of an arbitrary null-face embedding. -/
def programPT06NullFaceEmbeddingTangentFrame
    (embedding : ProgramPT06NullFaceSource3 → ProgramPT06AmbientCoordinate4)
    (source : ProgramPT06NullFaceSource3) :
    Fin 3 → ProgramPT06AmbientCoordinate4 :=
  fderiv Real embedding source ∘ programPT06NullFaceSourceFrame

/-- Pullback of the ambient flux along an arbitrary null-face embedding. -/
def programPT06NullFaceFluxPullback
    (embedding : ProgramPT06NullFaceSource3 → ProgramPT06AmbientCoordinate4)
    (current : ProgramPT06AmbientCurrent4D) :
    ProgramPT06NullFaceSource3 →
      ProgramPT06NullFaceSource3 [⋀^Fin 3]→L[Real] Real :=
  programPT06ThreeFormPullback embedding
    (programPT06AmbientFluxThreeForm current)

/-- Evaluation of the pulled-back flux is the ambient flux evaluated on the
actual embedding tangent frame. -/
theorem programPT06NullFaceFluxPullback_apply_sourceFrame
    (embedding : ProgramPT06NullFaceSource3 → ProgramPT06AmbientCoordinate4)
    (current : ProgramPT06AmbientCurrent4D)
    (source : ProgramPT06NullFaceSource3) :
    programPT06NullFaceFluxPullback embedding current source
        programPT06NullFaceSourceFrame =
      programPT06AmbientFluxThreeForm current (embedding source)
        (programPT06NullFaceEmbeddingTangentFrame embedding source) := by
  rfl

/-- Tangent frame stored by the mobile geometric null-face realization. -/
def programPT06FiniteNullFaceGeometricTangentFrame
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace)
    (source : ProgramPT06NullFaceSource3) :
    Fin 3 → ProgramPT06AmbientCoordinate4 :=
  Fin.cases
    (geometry.generatorDifferential input face source.1 source.2 1)
    (fun direction : Fin 2 =>
      geometry.screenDifferential input face source.1 source.2
        (EuclideanSpace.single direction 1))

theorem programPT06FiniteNullFaceEmbedding_differentiableAt
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (source : ProgramPT06NullFaceSource3) :
    DifferentiableAt Real (geometry.embedding input face) source := by
  have hState : (input, source) ∈ geometry.domain ×ˢ Set.univ :=
    ⟨hInput, Set.mem_univ source⟩
  have hJoint :=
    (geometry.embedding_contDiffOn_three face).contDiffAt
      ((geometry.domain_isOpen.prod isOpen_univ).mem_nhds hState)
  have hInsertion : ContDiffAt Real 3
      (fun variedSource : ProgramPT06NullFaceSource3 => (input, variedSource))
      source := contDiffAt_const.prodMk contDiffAt_id
  exact (hJoint.comp source hInsertion).differentiableAt (by norm_num)

private theorem programPT06FiniteNullFaceEmbedding_fderiv_parameter
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (source : ProgramPT06NullFaceSource3) :
    fderiv Real (geometry.embedding input face) source (1, 0) =
      geometry.generatorDifferential input face source.1 source.2 1 := by
  have hEmbedding :=
    programPT06FiniteNullFaceEmbedding_differentiableAt
      geometry input hInput face source
  have hInsertion := hasFDerivAt_prodMk_left (𝕜 := Real) source.1 source.2
  have hComposed := hEmbedding.hasFDerivAt.comp source.1 hInsertion
  have hStored := geometry.generatorEmbedding_hasFDerivAt
    input hInput face source.1 source.2
  have hUnique := hComposed.unique hStored
  have hAtOne := DFunLike.congr_fun hUnique 1
  simpa [ContinuousLinearMap.comp_apply] using hAtOne

private theorem programPT06FiniteNullFaceEmbedding_fderiv_screen
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (source : ProgramPT06NullFaceSource3)
    (direction : Fin 2) :
    fderiv Real (geometry.embedding input face) source
        (0, EuclideanSpace.single direction 1) =
      geometry.screenDifferential input face source.1 source.2
        (EuclideanSpace.single direction 1) := by
  have hEmbedding :=
    programPT06FiniteNullFaceEmbedding_differentiableAt
      geometry input hInput face source
  have hInsertion := hasFDerivAt_prodMk_right (𝕜 := Real) source.1 source.2
  have hComposed := hEmbedding.hasFDerivAt.comp source.2 hInsertion
  have hStored := geometry.screenEmbedding_hasFDerivAt
    input hInput face source.1 source.2
  have hUnique := hComposed.unique hStored
  have hAtDirection := DFunLike.congr_fun hUnique
    (EuclideanSpace.single direction 1)
  simpa [ContinuousLinearMap.comp_apply] using hAtDirection

/-- The derivative-defined frame of the embedding is exactly its stored
generator plus the two stored screen tangents. -/
theorem programPT06FiniteNullFaceEmbeddingTangentFrame_eq_geometric
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (source : ProgramPT06NullFaceSource3) :
    programPT06NullFaceEmbeddingTangentFrame
        (geometry.embedding input face) source =
      programPT06FiniteNullFaceGeometricTangentFrame
        geometry input face source := by
  funext direction
  refine Fin.cases ?_ (fun screenDirection => ?_) direction
  · exact programPT06FiniteNullFaceEmbedding_fderiv_parameter
      geometry input hInput face source
  · exact programPT06FiniteNullFaceEmbedding_fderiv_screen
      geometry input hInput face source screenDirection

/-- The pulled-back ambient flux on the mobile geometric null face is the
ambient current contraction evaluated on the genuine generator/screen tangent
frame. -/
theorem programPT06FiniteNullFaceFluxPullback_tangent_formula
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (current : ProgramPT06AmbientCurrent4D)
    (source : ProgramPT06NullFaceSource3) :
    programPT06NullFaceFluxPullback (geometry.embedding input face) current
        source programPT06NullFaceSourceFrame =
      programPT06AmbientSignedVolume.curryLeft
        (current (geometry.embedding input face source))
        (programPT06FiniteNullFaceGeometricTangentFrame
          geometry input face source) := by
  rw [programPT06NullFaceFluxPullback_apply_sourceFrame]
  unfold programPT06AmbientFluxThreeForm
  rw [programPT06FiniteNullFaceEmbeddingTangentFrame_eq_geometric
    geometry input hInput face source]

/-- Composing a null-face source map pulls its flux back functorially. -/
theorem programPT06FiniteNullFaceFluxPullback_source_composition
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (current : ProgramPT06AmbientCurrent4D)
    (reparametrization : ProgramPT06NullFaceSource3 →
      ProgramPT06NullFaceSource3)
    (source : ProgramPT06NullFaceSource3)
    (hReparametrization : DifferentiableAt Real reparametrization source) :
    programPT06NullFaceFluxPullback
        ((geometry.embedding input face) ∘ reparametrization) current source =
      (programPT06NullFaceFluxPullback (geometry.embedding input face) current
        (reparametrization source)).compContinuousLinearMap
          (fderiv Real reparametrization source) := by
  exact programPT06ThreeFormPullback_comp
    (geometry.embedding input face) reparametrization
      (programPT06AmbientFluxThreeForm current) source
      (programPT06FiniteNullFaceEmbedding_differentiableAt
        geometry input hInput face (reparametrization source))
      hReparametrization

/-- Pulling the flux through an ambient map and then through a null embedding
equals pullback through their composition. -/
theorem programPT06FiniteNullFaceFluxPullback_ambient_composition
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (current : ProgramPT06AmbientCurrent4D)
    (ambientMap : ProgramPT06AmbientCoordinate4 →
      ProgramPT06AmbientCoordinate4)
    (source : ProgramPT06NullFaceSource3)
    (hAmbient : DifferentiableAt Real ambientMap
      (geometry.embedding input face source)) :
    programPT06ThreeFormPullback
        (ambientMap ∘ geometry.embedding input face)
        (programPT06AmbientFluxThreeForm current) source =
      programPT06ThreeFormPullback (geometry.embedding input face)
        (programPT06ThreeFormPullback ambientMap
          (programPT06AmbientFluxThreeForm current)) source := by
  exact programPT06ThreeFormPullback_comp ambientMap
    (geometry.embedding input face) (programPT06AmbientFluxThreeForm current)
    source hAmbient
      (programPT06FiniteNullFaceEmbedding_differentiableAt
        geometry input hInput face source)

/-- Signed Piola covariance on a mobile null face: pulling back the transformed
ambient vector density along the source embedding equals pulling back the
original flux along the ambient-transformed embedding. -/
theorem programPT06FiniteNullFaceSignedVectorPullback_flux_covariance
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ geometry.domain) (face : NullFace)
    (forward reverse current : ProgramPT06AmbientCurrent4D)
    (source : ProgramPT06NullFaceSource3)
    (hInverse :
      (fderiv Real reverse
          (forward (geometry.embedding input face source))).comp
        (fderiv Real forward (geometry.embedding input face source)) =
          ContinuousLinearMap.id Real ProgramPT06AmbientCoordinate4)
    (hForward : DifferentiableAt Real forward
      (geometry.embedding input face source)) :
    programPT06NullFaceFluxPullback (geometry.embedding input face)
        (programPT06AmbientSignedVectorPullback forward reverse current)
        source =
      programPT06NullFaceFluxPullback
        (forward ∘ geometry.embedding input face) current source := by
  calc
    _ = programPT06ThreeFormPullback (geometry.embedding input face)
        (programPT06ThreeFormPullback forward
          (programPT06AmbientFluxThreeForm current)) source := by
      unfold programPT06NullFaceFluxPullback programPT06ThreeFormPullback
      rw [programPT06AmbientSignedVectorPullback_fluxThreeForm_eq_at hInverse]
    _ = _ :=
      (programPT06ThreeFormPullback_comp forward
        (geometry.embedding input face)
        (programPT06AmbientFluxThreeForm current) source hForward
        (programPT06FiniteNullFaceEmbedding_differentiableAt
          geometry input hInput face source)).symm

end
end P0EFTJanusProgramPT06AmbientNullFluxPullback4D
end JanusFormal
