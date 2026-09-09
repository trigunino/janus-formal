import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFacePhysicalActionRealization4D

/-!
# Mobile finite null-face geometric realization

The preceding realization gate accepts an arbitrary map into
`FiniteNullFaceActionDatum`.  This gate exposes the geometric content hidden
by such a map.  A mobile face now carries

* a three-dimensional embedding into a four-dimensional coordinate space;
* a defining function whose nonzero differential is null on the face;
* an ambient metric and its inverse;
* the two screen derivatives and their induced positive metric;
* a generator derivative and its covariant acceleration;
* the expansion, inaffinity, normalization and endpoint-joint data used by
  the existing finite null action.

The construction is a finite-mode coordinate realization.  The screen metric
is homogeneous in its two screen coordinates, as required by the existing
one-dimensional action.  Its area is computed as `sqrt |det q|`, the endpoint
actions are computed with the existing `jointDensity`, and these quantities
give a concrete `FiniteNullFaceActionDatum`.

The differential identities which still require an ambient null-geometry
calculation are fields with exact types: induced-screen agreement, nullness,
the inaffinity acceleration law, the area/expansion law, interval
integrability and `C²` regularity of the integrated action.  Thus this gate
does not claim that those computations follow from the current mapping-torus
library.  Once they are supplied, domain openness, action agreement,
differentiability and Euler agreement follow without another abstract map to
the reduced datum.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators ContDiff
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D

/-- Four real ambient coordinates for one finite null-face chart. -/
abbrev FiniteNullFaceAmbientCoordinate4 := EuclideanSpace Real (Fin 4)

/-- Two real coordinates on a homogeneous screen cross-section. -/
abbrev FiniteNullFaceScreenCoordinate2 := EuclideanSpace Real (Fin 2)

/-- Ambient metric matrix in the finite null-face chart. -/
abbrev FiniteNullFaceAmbientMatrix4 := Matrix (Fin 4) (Fin 4) Real

/-- Two-sided inverse certificate for an ambient four-metric. -/
structure FiniteNullFaceAmbientMatrix4InverseWitness
    (metric inverse : FiniteNullFaceAmbientMatrix4) : Prop where
  inverse_mul : inverse * metric = 1
  mul_inverse : metric * inverse = 1

/-- Coordinate pairing defined by an ambient four-metric matrix. -/
def finiteNullFaceAmbientMetricPairing
    (metric : FiniteNullFaceAmbientMatrix4)
    (first second : FiniteNullFaceAmbientCoordinate4) : Real :=
  ∑ row : Fin 4, ∑ column : Fin 4,
    metric row column * first row * second column

/-- Coordinate square of a defining covector using the inverse ambient
metric. -/
def finiteNullFaceDefiningCovectorSquare
    (inverseMetric : FiniteNullFaceAmbientMatrix4)
    (differential :
      FiniteNullFaceAmbientCoordinate4 →L[Real] Real) : Real :=
  ∑ row : Fin 4, ∑ column : Fin 4,
    inverseMetric row column *
      differential (EuclideanSpace.single row 1) *
      differential (EuclideanSpace.single column 1)

/-- Metric component induced on a screen by its coordinate differential. -/
def finiteNullFaceInducedScreenMetricComponent
    (metric : FiniteNullFaceAmbientMatrix4)
    (screenDifferential :
      FiniteNullFaceScreenCoordinate2 →L[Real]
        FiniteNullFaceAmbientCoordinate4)
    (first second : Fin 2) : Real :=
  finiteNullFaceAmbientMetricPairing metric
    (screenDifferential (EuclideanSpace.single first 1))
    (screenDifferential (EuclideanSpace.single second 1))

/-- Homogeneous screen area used by the existing one-dimensional null-face
action. -/
def finiteNullFaceHomogeneousScreenArea
    (screenMetric : Real → Matrix2) (parameter : Real) : Real :=
  Real.sqrt |Matrix.det (screenMetric parameter)|

/-- Explicit mobile null-face coordinate geometry.

The regularity fields are joint regularity in the physical coordinate and in
the displayed geometric coordinate.  The exact calculation fields state what
must be proved when this finite chart is constructed from the mapping-torus
metric and Levi-Civita connection. -/
structure FiniteNullFaceMobileGeometricDatum
    (NullFace : Type*) [Fintype NullFace] where
  domain : Set (FiniteNullFacePhysicalHilbert NullFace)
  domain_isOpen : IsOpen domain
  zero_mem_domain :
    (0 : FiniteNullFacePhysicalHilbert NullFace) ∈ domain
  embedding :
    FiniteNullFacePhysicalHilbert NullFace → NullFace →
      (Real × FiniteNullFaceScreenCoordinate2) →
        FiniteNullFaceAmbientCoordinate4
  definingFunction :
    FiniteNullFacePhysicalHilbert NullFace → NullFace →
      FiniteNullFaceAmbientCoordinate4 → Real
  ambientMetric :
    FiniteNullFacePhysicalHilbert NullFace → NullFace →
      FiniteNullFaceAmbientCoordinate4 → FiniteNullFaceAmbientMatrix4
  ambientInverseMetric :
    FiniteNullFacePhysicalHilbert NullFace → NullFace →
      FiniteNullFaceAmbientCoordinate4 → FiniteNullFaceAmbientMatrix4
  definingDifferential :
    FiniteNullFacePhysicalHilbert NullFace → NullFace →
      FiniteNullFaceAmbientCoordinate4 →
        (FiniteNullFaceAmbientCoordinate4 →L[Real] Real)
  screenDifferential :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real →
      FiniteNullFaceScreenCoordinate2 →
        (FiniteNullFaceScreenCoordinate2 →L[Real]
          FiniteNullFaceAmbientCoordinate4)
  generatorDifferential :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real →
      FiniteNullFaceScreenCoordinate2 →
        (Real →L[Real] FiniteNullFaceAmbientCoordinate4)
  generatorCovariantAcceleration :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real →
      FiniteNullFaceScreenCoordinate2 →
        FiniteNullFaceAmbientCoordinate4
  screenMetric :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real → Matrix2
  screenInverse :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real → Matrix2
  expansion :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real → Real
  inaffinity :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real → Real
  sigma :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real → Real
  sigmaDerivative :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real → Real
  interval : NullFace → OrientedNullInterval
  einsteinScale : NullFace → Real
  faceOrientationSign : NullFace → Real
  faceOrientationSignAdmissible :
    ∀ face, IsOrientationSign (faceOrientationSign face)
  renormalizationLengthScale : NullFace → Real
  renormalizationLengthScalePositive :
    ∀ face, 0 < renormalizationLengthScale face
  initialJointOrientationSign : NullFace → Real
  initialJointOrientationSignAdmissible :
    ∀ face, IsOrientationSign (initialJointOrientationSign face)
  finalJointOrientationSign : NullFace → Real
  finalJointOrientationSignAdmissible :
    ∀ face, IsOrientationSign (finalJointOrientationSign face)
  initialJointAngle :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real
  finalJointAngle :
    FiniteNullFacePhysicalHilbert NullFace → NullFace → Real
  embedding_contDiffOn_three : ∀ face,
    ContDiffOn Real 3
      (fun state : FiniteNullFacePhysicalHilbert NullFace ×
          (Real × FiniteNullFaceScreenCoordinate2) =>
        embedding state.1 face state.2)
      (domain ×ˢ Set.univ)
  definingFunction_contDiffOn_three : ∀ face,
    ContDiffOn Real 3
      (fun state : FiniteNullFacePhysicalHilbert NullFace ×
          FiniteNullFaceAmbientCoordinate4 =>
        definingFunction state.1 face state.2)
      (domain ×ˢ Set.univ)
  ambientMetric_contDiffOn_two : ∀ face row column,
    ContDiffOn Real 2
      (fun state : FiniteNullFacePhysicalHilbert NullFace ×
          FiniteNullFaceAmbientCoordinate4 =>
        ambientMetric state.1 face state.2 row column)
      (domain ×ˢ Set.univ)
  screenMetric_contDiffOn_two : ∀ face row column,
    ContDiffOn Real 2
      (fun state : FiniteNullFacePhysicalHilbert NullFace × Real =>
        screenMetric state.1 face state.2 row column)
      (domain ×ˢ Set.univ)
  expansion_contDiffOn_two : ∀ face,
    ContDiffOn Real 2
      (fun state : FiniteNullFacePhysicalHilbert NullFace × Real =>
        expansion state.1 face state.2)
      (domain ×ˢ Set.univ)
  inaffinity_contDiffOn_two : ∀ face,
    ContDiffOn Real 2
      (fun state : FiniteNullFacePhysicalHilbert NullFace × Real =>
        inaffinity state.1 face state.2)
      (domain ×ˢ Set.univ)
  embedding_injective :
    ∀ input, input ∈ domain → ∀ face, Function.Injective (embedding input face)
  embedding_zero_level :
    ∀ input, input ∈ domain → ∀ face source,
      definingFunction input face (embedding input face source) = 0
  definingFunction_hasFDerivAt :
    ∀ input, input ∈ domain → ∀ face point,
      HasFDerivAt (definingFunction input face)
        (definingDifferential input face point) point
  definingDifferential_ne_zero_on_face :
    ∀ input, input ∈ domain → ∀ face source,
      definingDifferential input face (embedding input face source) ≠ 0
  ambientMetricSymmetric :
    ∀ input face point,
      (ambientMetric input face point).transpose = ambientMetric input face point
  ambientMetricInverseWitness :
    ∀ input face point,
      FiniteNullFaceAmbientMatrix4InverseWitness
        (ambientMetric input face point) (ambientInverseMetric input face point)
  definingDifferential_null_on_face :
    ∀ input, input ∈ domain → ∀ face source,
      finiteNullFaceDefiningCovectorSquare
        (ambientInverseMetric input face (embedding input face source))
        (definingDifferential input face (embedding input face source)) = 0
  screenEmbedding_hasFDerivAt :
    ∀ input, input ∈ domain → ∀ face parameter screen,
      HasFDerivAt
        (fun variedScreen => embedding input face (parameter, variedScreen))
        (screenDifferential input face parameter screen) screen
  screenDifferential_injective :
    ∀ input, input ∈ domain → ∀ face parameter screen,
      Function.Injective (screenDifferential input face parameter screen)
  generatorEmbedding_hasFDerivAt :
    ∀ input, input ∈ domain → ∀ face parameter screen,
      HasFDerivAt
        (fun variedParameter => embedding input face (variedParameter, screen))
        (generatorDifferential input face parameter screen) parameter
  generatorTangent_ne_zero :
    ∀ input, input ∈ domain → ∀ face parameter screen,
      generatorDifferential input face parameter screen 1 ≠ 0
  generatorTangent_null :
    ∀ input, input ∈ domain → ∀ face parameter screen,
      finiteNullFaceAmbientMetricPairing
        (ambientMetric input face (embedding input face (parameter, screen)))
        (generatorDifferential input face parameter screen 1)
        (generatorDifferential input face parameter screen 1) = 0
  generatorTangent_screen_orthogonal :
    ∀ input, input ∈ domain → ∀ face parameter screen index,
      finiteNullFaceAmbientMetricPairing
        (ambientMetric input face (embedding input face (parameter, screen)))
        (generatorDifferential input face parameter screen 1)
        (screenDifferential input face parameter screen
          (EuclideanSpace.single index 1)) = 0
  screenMetric_eq_induced :
    ∀ input, input ∈ domain → ∀ face parameter screen first second,
      screenMetric input face parameter first second =
        finiteNullFaceInducedScreenMetricComponent
          (ambientMetric input face (embedding input face (parameter, screen)))
          (screenDifferential input face parameter screen) first second
  screenMetricSymmetric :
    ∀ input face parameter,
      (screenMetric input face parameter).transpose =
        screenMetric input face parameter
  screenMetricDeterminantPositive :
    ∀ input face parameter, 0 < Matrix.det (screenMetric input face parameter)
  screenInverseWitness :
    ∀ input face parameter,
      Matrix2InverseWitness (screenMetric input face parameter)
        (screenInverse input face parameter)
  inaffinity_acceleration_law :
    ∀ input, input ∈ domain → ∀ face parameter screen,
      generatorCovariantAcceleration input face parameter screen =
        inaffinity input face parameter •
          generatorDifferential input face parameter screen 1
  screenArea_hasDerivAt :
    ∀ input face parameter,
      HasDerivAt
        (finiteNullFaceHomogeneousScreenArea (screenMetric input face))
        (finiteNullFaceHomogeneousScreenArea (screenMetric input face) parameter *
          expansion input face parameter) parameter
  sigma_hasDerivAt :
    ∀ input face parameter,
      HasDerivAt (sigma input face) (sigmaDerivative input face parameter) parameter
  expansion_ne_zero_on_domain :
    ∀ input, input ∈ domain → ∀ face parameter,
      parameter ∈ Set.uIcc (interval face).initialParameter
          (interval face).finalParameter →
        expansion input face parameter ≠ 0

/-- Initial endpoint joint computed from the screen metric and supplied joint
angle. -/
def FiniteNullFaceMobileGeometricDatum.initialJointPointData
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    JointPointData where
  cornerMetric :=
    geometry.screenMetric input face (geometry.interval face).initialParameter
  cornerInverse :=
    geometry.screenInverse input face (geometry.interval face).initialParameter
  orientationSign := geometry.initialJointOrientationSign face
  jointAngle := geometry.initialJointAngle input face
  inverseWitness := geometry.screenInverseWitness input face
    (geometry.interval face).initialParameter
  cornerMetricSymmetric := geometry.screenMetricSymmetric input face
    (geometry.interval face).initialParameter
  cornerMetricDeterminantPositive :=
    geometry.screenMetricDeterminantPositive input face
      (geometry.interval face).initialParameter
  orientationSignAdmissible :=
    geometry.initialJointOrientationSignAdmissible face

/-- Final endpoint joint computed from the same mobile screen geometry. -/
def FiniteNullFaceMobileGeometricDatum.finalJointPointData
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    JointPointData where
  cornerMetric :=
    geometry.screenMetric input face (geometry.interval face).finalParameter
  cornerInverse :=
    geometry.screenInverse input face (geometry.interval face).finalParameter
  orientationSign := geometry.finalJointOrientationSign face
  jointAngle := geometry.finalJointAngle input face
  inverseWitness := geometry.screenInverseWitness input face
    (geometry.interval face).finalParameter
  cornerMetricSymmetric := geometry.screenMetricSymmetric input face
    (geometry.interval face).finalParameter
  cornerMetricDeterminantPositive :=
    geometry.screenMetricDeterminantPositive input face
      (geometry.interval face).finalParameter
  orientationSignAdmissible :=
    geometry.finalJointOrientationSignAdmissible face

/-- Concrete projection from mobile embedding/screen data to the existing
finite null-face action datum. -/
def FiniteNullFaceMobileGeometricDatum.toFiniteNullFaceActionDatum
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    FiniteNullFaceActionDatum where
  generator :=
    { area := finiteNullFaceHomogeneousScreenArea (geometry.screenMetric input face)
      expansion := geometry.expansion input face
      inaffinity := geometry.inaffinity input face
      sigma := geometry.sigma input face
      sigmaDerivative := geometry.sigmaDerivative input face
      area_hasDerivAt := geometry.screenArea_hasDerivAt input face
      sigma_hasDerivAt := geometry.sigma_hasDerivAt input face }
  interval := geometry.interval face
  einsteinScale := geometry.einsteinScale face
  orientationSign := geometry.faceOrientationSign face
  orientationSignAdmissible := geometry.faceOrientationSignAdmissible face
  renormalizationLengthScale := geometry.renormalizationLengthScale face
  renormalizationLengthScalePositive :=
    geometry.renormalizationLengthScalePositive face
  initialJointAction := jointDensity (geometry.einsteinScale face)
    (geometry.initialJointPointData input face)
  finalJointAction := jointDensity (geometry.einsteinScale face)
    (geometry.finalJointPointData input face)

@[simp] theorem toFiniteNullFaceActionDatum_generator_area
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    (geometry.toFiniteNullFaceActionDatum input face).generator.area =
      finiteNullFaceHomogeneousScreenArea (geometry.screenMetric input face) :=
  rfl

@[simp] theorem toFiniteNullFaceActionDatum_initialJointAction
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) (face : NullFace) :
    (geometry.toFiniteNullFaceActionDatum input face).initialJointAction =
      jointDensity (geometry.einsteinScale face)
        (geometry.initialJointPointData input face) :=
  rfl

/-- Existing finite null-boundary action evaluated on the concrete geometric
projection. -/
def finiteNullFaceMobileGeometricTotalAction
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  totalFiniteNullBoundaryAction
    (fun face => geometry.toFiniteNullFaceActionDatum input face)

/-- The remaining analytic realization laws.  They are separated from the
geometric coordinate data so their proof obligations are visible. -/
structure FiniteNullFaceMobileGeometricActionRealization
    (NullFace : Type*) [Fintype NullFace] where
  geometry : FiniteNullFaceMobileGeometricDatum NullFace
  intervalIntegrability :
    ∀ input, input ∈ geometry.domain → ∀ face,
      NullFaceIntervalIntegrability
        (geometry.toFiniteNullFaceActionDatum input face)
  totalAction_contDiffOn_two :
    ContDiffOn Real 2
      (finiteNullFaceMobileGeometricTotalAction geometry) geometry.domain

/-- Relative action on the mobile geometric chart. -/
def finiteNullFaceMobileGeometricRelativeAction
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  finiteNullFaceMobileGeometricTotalAction realization.geometry input -
    finiteNullFaceMobileGeometricTotalAction realization.geometry 0

theorem finiteNullFaceMobileGeometricRelativeAction_contDiffOn_two
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace) :
    ContDiffOn Real 2
      (finiteNullFaceMobileGeometricRelativeAction realization)
      realization.geometry.domain := by
  exact realization.totalAction_contDiffOn_two.sub contDiffOn_const

@[simp] theorem finiteNullFaceMobileGeometricRelativeAction_zero
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace) :
    finiteNullFaceMobileGeometricRelativeAction realization 0 = 0 := by
  simp [finiteNullFaceMobileGeometricRelativeAction]

/-- The concrete geometric realization instantiates the preceding physical
realization interface. -/
def FiniteNullFaceMobileGeometricActionRealization.toPhysicalActionRealization
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace) :
    FiniteNullFacePhysicalActionRealization NullFace where
  toDatum := fun input face =>
    realization.geometry.toFiniteNullFaceActionDatum input face
  domain := realization.geometry.domain
  domain_isOpen := realization.geometry.domain_isOpen
  zero_mem_domain := realization.geometry.zero_mem_domain
  totalAction_contDiffOn_two := realization.totalAction_contDiffOn_two

@[simp] theorem toPhysicalActionRealization_domain
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace) :
    realization.toPhysicalActionRealization.domain =
      realization.geometry.domain :=
  rfl

theorem finiteNullFaceMobileGeometric_domain_isOpen
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace) :
    IsOpen realization.geometry.domain :=
  realization.geometry.domain_isOpen

/-- Exact agreement between the induced action model and the action computed
from the embeddings, screen metrics and joints. -/
theorem toPhysicalActionRealization_action_eq_geometric
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    realization.toPhysicalActionRealization.toActionModel.action input =
      finiteNullFaceMobileGeometricRelativeAction realization input :=
  rfl

/-- The geometric action is invariant under the already-proved simultaneous
finite generator reparametrization on every face. -/
theorem totalReparametrizedFiniteNullBoundaryAction_geometric_eq
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ realization.geometry.domain) :
    totalReparametrizedFiniteNullBoundaryAction
        (fun face =>
          realization.geometry.toFiniteNullFaceActionDatum input face) =
      finiteNullFaceMobileGeometricTotalAction realization.geometry input := by
  exact totalReparametrizedFiniteNullBoundaryAction_eq
    (fun face => realization.geometry.toFiniteNullFaceActionDatum input face)
    (realization.intervalIntegrability input hInput)

/-- On the open geometric domain, the physical null Euler covector is the
Fréchet derivative of the concretely projected finite face-plus-joint action. -/
theorem finiteNullFacePhysicalEuler_geometric_eq_fderiv
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ realization.geometry.domain) :
    finiteNullFacePhysicalEuler
        realization.toPhysicalActionRealization.toActionModel input =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction realization.geometry) input := by
  exact finiteNullFacePhysicalEuler_toActionModel_eq_realizedTotal_fderiv
    realization.toPhysicalActionRealization input hInput

/-- Stationarity of the geometric physical-null block is exactly vanishing
of the derivative of the existing finite null-face action after the concrete
geometric projection. -/
theorem finiteNullFacePhysicalEuler_geometric_eq_zero_iff
    {NullFace : Type*} [Fintype NullFace]
    (realization : FiniteNullFaceMobileGeometricActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ realization.geometry.domain) :
    finiteNullFacePhysicalEuler
        realization.toPhysicalActionRealization.toActionModel input = 0 ↔
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction realization.geometry) input = 0 := by
  rw [finiteNullFacePhysicalEuler_geometric_eq_fderiv realization input hInput]

end
end P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
end JanusFormal
