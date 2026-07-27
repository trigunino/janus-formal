import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteStratifiedBoundaryVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalPalatiniGHYBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLGeometricStokes4D

/-!
# Global boundary completion for Program P

The canonical throat is inserted into the exact Gaussian-normal EH/GHY
ledger.  Finite null faces and joints retain their oriented transgression
cancellation.  Scalar flux is kept in the unrestricted Green--Stokes formula
and vanishes only in the selected PT-fixed or Dirichlet domain.  The genuine
LL action uses the proved divergence-free canonical throat frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalBoundaryCompletion4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusGaussianNormalEHGHYCancellation
open P0EFTJanusGaussianNormalEmbeddedHypersurface
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D
open P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D
open P0EFTJanusMappingTorusLocalPalatiniGHYBridge4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLGeometricStokes4D
open P0EFTJanusProgramPGlobalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The true canonical throat written as the non-null point datum used by the
EH/GHY ledger.  Its second fundamental form is the proved zero tensor. -/
def canonicalThroatNonNullBoundaryPointData
    (orientation : NormalOrientation) :
    NonNullBoundaryPointData where
  inducedMetric := canonicalThroatInducedMetric
  inducedInverse := canonicalThroatInducedMetric
  extrinsicCurvature := 0
  orientationSign := orientation.sign
  inverseWitness :=
    { inverse_mul :=
        (canonicalThroatGaussianData period hPeriod).inverse_mul_induced
      mul_inverse :=
        (canonicalThroatGaussianData period hPeriod).induced_mul_inverse }
  inducedMetricSymmetric := by
    simp [canonicalThroatInducedMetric]
  extrinsicCurvatureSymmetric := by simp
  orientationSignAdmissible := by
    cases orientation <;>
      simp [NormalOrientation.sign, IsOrientationSign]

@[simp]
theorem canonicalThroatNonNullBoundaryPointData_extrinsic_eq_actual
    (orientation : NormalOrientation) :
    (canonicalThroatNonNullBoundaryPointData
        period hPeriod orientation).extrinsicCurvature =
      secondFundamentalForm .covariantNormal
        (canonicalThroatGaussianData period hPeriod) orientation := by
  rw [canonicalThroat_secondFundamentalForm_zero]
  rfl

/-- A non-null face is derived from the actual canonical throat geometry;
only its weight, coupling, orientation and admissible Dirichlet jet vary. -/
def canonicalThroatNonNullFaceDatum
    (weight einsteinScale : Real)
    (orientation : NormalOrientation)
    (dirichletJet : GaussianNormalDirichletJet) :
    NonNullFaceDatum where
  weight := weight
  einsteinScale := einsteinScale
  geometry :=
    canonicalThroatNonNullBoundaryPointData period hPeriod orientation
  dirichletJet := dirichletJet

/-- The EH flux of every canonical face is the normal component of the same
Palatini vector used by the local bulk variation. -/
theorem canonicalThroatNonNullFace_ehFlux_uses_localPalatini
    (weight einsteinScale : Real)
    (orientation : NormalOrientation)
    (dirichletJet : GaussianNormalDirichletJet) :
    nonNullEHFlux
        (canonicalThroatNonNullFaceDatum period hPeriod weight einsteinScale
          orientation dirichletJet) =
      weight * ((einsteinScale / 2) *
        Real.sqrt
          |Matrix.det
            (canonicalThroatNonNullBoundaryPointData
              period hPeriod orientation).inducedMetric| *
        ((canonicalThroatNonNullBoundaryPointData
              period hPeriod orientation).orientationSign *
          (canonicalThroatNonNullBoundaryPointData
              period hPeriod orientation).orientationSign *
          palatiniVector
            (gaussianMetricCompatiblePalatiniJet
              (canonicalThroatNonNullBoundaryPointData
                period hPeriod orientation) dirichletJet)
            normalIndex)) := by
  unfold nonNullEHFlux canonicalThroatNonNullFaceDatum
  rw [einsteinHilbertDirichletBoundaryFlux_eq_localPalatiniVector]

/-- Exact physical scalar boundary choices.  No universal zero-flux
constructor exists. -/
inductive ScalarBoundaryControl
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) : Prop
  | ptFixed
      (fieldEuler :
        CanonicalLatitudeScalarEulerSolution
          period hPeriod massSquared field)
      (testEuler :
        CanonicalLatitudeScalarEulerSolution
          period hPeriod massSquared test)
      (fieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
      (testPT : CanonicalLatitudeScalarPTFixed period hPeriod test)
  | dirichlet
      (fieldDirichlet :
        CanonicalLatitudeScalarDirichletEulerSolution
          period hPeriod massSquared field)
      (testDirichlet :
        CanonicalLatitudeScalarDirichletEulerSolution
          period hPeriod massSquared test)

theorem ScalarBoundaryControl.euler
    {massSquared : Real}
    {field test : SmoothQuotientField period hPeriod Real}
    (control :
      ScalarBoundaryControl period hPeriod massSquared field test) :
    CanonicalLatitudeScalarEulerSolution
        period hPeriod massSquared field ∧
      CanonicalLatitudeScalarEulerSolution
        period hPeriod massSquared test := by
  cases control with
  | ptFixed fieldEuler testEuler _ _ =>
      exact ⟨fieldEuler, testEuler⟩
  | dirichlet fieldDirichlet testDirichlet =>
      exact ⟨fieldDirichlet.euler, testDirichlet.euler⟩

/-- The unrestricted formula deliberately retains the oriented flux. -/
theorem scalarGreenStokes_retains_orientedFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (fieldEuler :
      CanonicalLatitudeScalarEulerSolution
        period hPeriod massSquared field)
    (testEuler :
      CanonicalLatitudeScalarEulerSolution
        period hPeriod massSquared test) :
    (2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
          period hPeriod massSquared field test =
        -cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test) ↔
      cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod field test = 0 :=
  cutBulkGlobalMetricGreenStokes_iff_orientedBoundary_zero
    period hPeriod massSquared field test fieldEuler testEuler

theorem ScalarBoundaryControl.orientedFlux_eq_zero
    {massSquared : Real}
    {field test : SmoothQuotientField period hPeriod Real}
    (control :
      ScalarBoundaryControl period hPeriod massSquared field test) :
    cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod field test = 0 := by
  cases control with
  | ptFixed _ _ fieldPT testPT =>
      exact cutBulkGlobalOrientedBoundaryCurrent_zero_of_ptFixed
        period hPeriod field test fieldPT testPT
  | dirichlet fieldDirichlet testDirichlet =>
      exact cutBulkGlobalOrientedBoundaryCurrent_zero_of_dirichletEuler
        period hPeriod massSquared field test
          fieldDirichlet testDirichlet

theorem ScalarBoundaryControl.metricDivergence_eq_zero
    {massSquared : Real}
    {field test : SmoothQuotientField period hPeriod Real}
    (control :
      ScalarBoundaryControl period hPeriod massSquared field test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral
        period hPeriod massSquared field test = 0 := by
  cases control with
  | ptFixed fieldEuler testEuler fieldPT testPT =>
      exact cutBulkGlobalMetricDivergence_zero_of_ptFixed
        period hPeriod massSquared field test
          fieldEuler testEuler fieldPT testPT
  | dirichlet fieldDirichlet testDirichlet =>
      exact cutBulkGlobalMetricDivergence_zero_of_dirichletEuler
        period hPeriod massSquared field test
          fieldDirichlet testDirichlet

/-- Concrete zero scalar used only to witness that the controlled boundary
domain is inhabited. -/
def zeroBoundaryScalarField :
    SmoothQuotientField period hPeriod Real where
  toFun := fun _ => 0
  contMDiff_toFun := contMDiff_const

theorem zeroBoundaryScalarField_dirichletEuler :
    CanonicalLatitudeScalarDirichletEulerSolution period hPeriod 0
      (zeroBoundaryScalarField period hPeriod) := by
  constructor
  · intro base normal
    change deriv (deriv (fun _ : Real => 0)) normal + 0 * 0 = 0
    simp
  · apply SmoothThroatField.ext period hPeriod Real
    intro point
    rfl
  · intro base
    rfl

/-- The existing smooth derivative theorem supplies the regularity object
needed by the strong LL operator; no new analytic hypothesis is introduced. -/
def smoothLLStrongRegularity
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    LLStrongAnalyticRegularityContract period hPeriod frame where
  derivativeComponent field index :=
    { toFun := fun point =>
        throatFrameDerivative period hPeriod LLFieldFiber
          frame field point index
      contMDiff_toFun := by
        have hDerivative :=
          throatFrameDerivative_contMDiff
            period hPeriod LLFieldFiber frame field
        rw [contMDiff_pi_space] at hDerivative
        exact hDerivative index }
  derivativeComponent_apply := by
    intros
    rfl

/-- All boundary inputs for the one global field configuration.  Non-null
faces are forced to be canonical-throat faces; null data are explicit finite
oriented generator strata. -/
structure GlobalBoundaryVariationData
    (configuration : GlobalFieldConfiguration period hPeriod)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] where
  nonNullWeight : NonNullFace → Real
  nonNullEinsteinScale : NonNullFace → Real
  nonNullOrientation : NonNullFace → NormalOrientation
  nonNullDirichletJet : NonNullFace → GaussianNormalDirichletJet
  nullFaces : NullFace → NullFaceDatum
  scalarMassSquared : Real
  scalarField : SmoothQuotientField period hPeriod Real
  scalarTest : SmoothQuotientField period hPeriod Real
  scalarControl :
    ScalarBoundaryControl period hPeriod scalarMassSquared
      scalarField scalarTest

def GlobalBoundaryVariationData.nonNullFaces
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace) :
    NonNullFace → NonNullFaceDatum :=
  fun face =>
    canonicalThroatNonNullFaceDatum period hPeriod
      (data.nonNullWeight face)
      (data.nonNullEinsteinScale face)
      (data.nonNullOrientation face)
      (data.nonNullDirichletJet face)

def GlobalBoundaryVariationData.llFields
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (_data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace) :
    IndependentFields period hPeriod :=
  diagonalScaffold period hPeriod configuration.coefficientFields

def GlobalBoundaryVariationData.llStokesContract
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace) :
    CanonicalThroatGeometricStokesContractFor period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (data.llFields period hPeriod)
      (smoothLLStrongRegularity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)) :=
  canonicalDivergenceFreeLLFrameGeometricStokesContract
    period hPeriod (data.llFields period hPeriod)
      (smoothLLStrongRegularity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod))

/-- Sum of EH/GHY, null-face and joint residuals. -/
def GlobalBoundaryVariationData.gravityResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace) : Real :=
  finiteStratifiedBoundaryResidual data.nonNullFaces data.nullFaces

/-- Genuine LL boundary flux produced by the global manifold IPP. -/
def GlobalBoundaryVariationData.llBoundaryResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  data.llStokesContract period hPeriod |>.geometricBoundaryFlux direction

/-- Complete residual of the implemented boundary sectors. -/
def GlobalBoundaryVariationData.totalResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  data.gravityResidual period hPeriod +
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod
      data.scalarField data.scalarTest +
    data.llBoundaryResidual period hPeriod llDirection

theorem GlobalBoundaryVariationData.gravityResidual_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace) :
    data.gravityResidual period hPeriod = 0 :=
  finiteStratifiedBoundaryResidual_eq_zero
    data.nonNullFaces data.nullFaces

theorem GlobalBoundaryVariationData.llBoundaryResidual_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    data.llBoundaryResidual period hPeriod direction = 0 :=
  (data.llStokesContract period hPeriod).geometricBoundaryFlux_eq_zero
    period hPeriod direction

/-- No uncontrolled boundary term remains on the displayed physical domain. -/
theorem GlobalBoundaryVariationData.totalResidual_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) :
    data.totalResidual period hPeriod llDirection = 0 := by
  rw [GlobalBoundaryVariationData.totalResidual,
    data.gravityResidual_eq_zero period hPeriod,
    data.scalarControl.orientedFlux_eq_zero period hPeriod,
    data.llBoundaryResidual_eq_zero period hPeriod]
  ring

/-- Retained LL action: weak stationarity and the strong equation agree on
the same configuration, with the boundary condition discharged geometrically. -/
theorem GlobalBoundaryVariationData.llStationary_iff_strong
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalBoundaryVariationData period hPeriod configuration
      NonNullFace NullFace) :
    PTSymmetricDifferentialLLFluxStationary period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.llFields period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (smoothLLStrongRegularity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod))
        (data.llFields period hPeriod) :=
  canonicalDivergenceFreeLLFrame_stationary_iff_strong
    period hPeriod (data.llFields period hPeriod)
      (smoothLLStrongRegularity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod))

/-- The global boundary package is nonempty for every global configuration.
The main residual theorem above remains valid for arbitrary supplied finite
face families, not only for this empty-face witness. -/
def emptyFaceGlobalBoundaryVariationData
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalBoundaryVariationData period hPeriod configuration PEmpty PEmpty where
  nonNullWeight := PEmpty.elim
  nonNullEinsteinScale := PEmpty.elim
  nonNullOrientation := PEmpty.elim
  nonNullDirichletJet := PEmpty.elim
  nullFaces := PEmpty.elim
  scalarMassSquared := 0
  scalarField := zeroBoundaryScalarField period hPeriod
  scalarTest := zeroBoundaryScalarField period hPeriod
  scalarControl := .dirichlet
    (zeroBoundaryScalarField_dirichletEuler period hPeriod)
    (zeroBoundaryScalarField_dirichletEuler period hPeriod)

theorem globalBoundaryVariationData_nonempty
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Nonempty
      (GlobalBoundaryVariationData period hPeriod configuration PEmpty PEmpty) :=
  ⟨emptyFaceGlobalBoundaryVariationData period hPeriod configuration⟩

end
end P0EFTJanusProgramPGlobalBoundaryCompletion4D
end JanusFormal
