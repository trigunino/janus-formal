import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeVariationalObstructionExactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D

/-!
# Exact T03 relative variational realization for T05

This gate realizes the relative algebraic bicomplex by the oriented cellular
complex of the four physical strata, tensorized with a two-term vertical
variation complex.  Both differentials are nonzero.  Its distinguished
Lagrangian and Euler cochains evaluate to the exact T03 action and Euler
covector.  Gate 816 separately identifies that exact Euler covector with the
actual action gradient on the T03 domain.

This remains an integrated cellular realization.  It does not claim a local
jet-density realization, fill the three open T04 residual families, or close a
terminal gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetVariationalBicomplexCore
open P0EFTJanusProgramPRelativeVariationalObstructionExactness4D
open P0EFTJanusProgramPRelativeVariationalObstructionExactness4D.RelativeFirstVariationData
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
open P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusReciprocalBimetricPotential

/-- Re-export of the Gate 816 identification of the exact T03 Euler covector
with the action gradient on its admissible domain. -/
def programPT05ExactT03Euler_eq_actionGradient :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler_eq_actionGradient

/-- Two generators: an integrated density generator and its vertical
variation generator. -/
abbrev ProgramPT05PhysicalJetComponent
    (_ : RelativeJetStratum4D) (_ _ : Nat) := Real × Real

local notation "C" => ProgramPT05PhysicalJetComponent

/-- Oriented cellular coboundary for
`bulk -> nonNullBoundary/nullBoundary -> joint`. -/
def programPT05RelativeHorizontalDifferential (p q : Nat) :
    RelativeJetCochain C p q →ₗ[Real] RelativeJetCochain C (p + 1) q where
  toFun cochain
    | .bulk => 0
    | .nonNullBoundary => cochain .bulk
    | .nullBoundary => cochain .bulk
    | .joint => cochain .nonNullBoundary - cochain .nullBoundary
  map_add' first second := by
    funext stratum
    cases stratum <;> simp
    abel
  map_smul' scalar cochain := by
    funext stratum
    cases stratum <;> simp [smul_sub]

/-- Signed vertical differential.  The sign depending on horizontal degree is
what makes it anticommute with the cellular horizontal differential. -/
def programPT05RelativeVerticalDifferential (p q : Nat) :
    RelativeJetCochain C p q →ₗ[Real] RelativeJetCochain C p (q + 1) where
  toFun cochain stratum :=
    (0, (-1 : Real) ^ p * (cochain stratum).1)
  map_add' first second := by
    funext stratum
    apply Prod.ext <;> simp [mul_add]
  map_smul' scalar cochain := by
    funext stratum
    apply Prod.ext <;> simp
    ring

/-- Concrete relative cellular/vertical bicomplex. -/
def programPT05ExactT03RelativeBicomplex :
    RelativeJetVariationalBicomplexCore Real C where
  dH := programPT05RelativeHorizontalDifferential
  dV := programPT05RelativeVerticalDifferential
  dH_dH := by
    intro p q cochain
    funext stratum
    cases stratum <;>
      simp [programPT05RelativeHorizontalDifferential]
  dV_dV := by
    intro p q cochain
    funext stratum
    apply Prod.ext <;>
      simp [programPT05RelativeVerticalDifferential]
  mixed_anticommutes := by
    intro p q cochain
    funext stratum
    cases stratum <;>
      apply Prod.ext <;>
      simp [programPT05RelativeHorizontalDifferential,
        programPT05RelativeVerticalDifferential, pow_succ]
    all_goals ring
  dH_respects_incidence := by
    intro p q source cochain hSupport target hForbidden
    cases target with
    | bulk => rfl
    | nonNullBoundary =>
        change cochain .bulk = 0
        apply hSupport
        intro hSource
        subst source
        exact hForbidden (Or.inr IsImmediateBoundary.bulk_nonNull)
    | nullBoundary =>
        change cochain .bulk = 0
        apply hSupport
        intro hSource
        subst source
        exact hForbidden (Or.inr IsImmediateBoundary.bulk_null)
    | joint =>
        cases source with
        | bulk =>
            change cochain .nonNullBoundary - cochain .nullBoundary = 0
            rw [hSupport .nonNullBoundary (by decide),
              hSupport .nullBoundary (by decide)]
            simp
        | nonNullBoundary =>
            exact (hForbidden (Or.inr IsImmediateBoundary.nonNull_joint)).elim
        | nullBoundary =>
            exact (hForbidden (Or.inr IsImmediateBoundary.null_joint)).elim
        | joint =>
            exact (hForbidden (Or.inl rfl)).elim
  dV_preserves_stratum := by
    intro p q source cochain hSupport target hTarget
    change (0, (-1 : Real) ^ p * (cochain target).1) = 0
    rw [hSupport target hTarget]
    simp

/-- Unit integrated-density generator supported on the bulk stratum. -/
def programPT05BulkGenerator (p q : Nat) : RelativeJetCochain C p q
  | .bulk => (1, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

/-- Four-dimensional relative Lagrangian cochain. -/
def programPT05RelativeLagrangian : RelativeJetCochain C 4 0 :=
  programPT05BulkGenerator 4 0

/-- Nonzero relative boundary potential in horizontal degree three. -/
def programPT05RelativeBoundaryPotential : RelativeJetCochain C 3 1 :=
  programPT05BulkGenerator 3 1

/-- Euler cochain determined by the exact first-variation decomposition. -/
def programPT05RelativeEuler : RelativeJetCochain C 4 1 :=
  programPT05ExactT03RelativeBicomplex.dV 4 0
      programPT05RelativeLagrangian -
    programPT05ExactT03RelativeBicomplex.dH 3 1
      programPT05RelativeBoundaryPotential

/-- Genuine relative first-variation data in top horizontal degree. -/
def programPT05ExactT03RelativeFirstVariation :
    RelativeFirstVariationData programPT05ExactT03RelativeBicomplex 3 where
  lagrangian := programPT05RelativeLagrangian
  euler := programPT05RelativeEuler
  boundaryPotential := programPT05RelativeBoundaryPotential
  firstVariation := by
    symm
    exact sub_add_cancel _ _

/-- The cellular horizontal differential is genuinely nonzero. -/
theorem programPT05RelativeHorizontalDifferential_ne_zero :
    programPT05ExactT03RelativeBicomplex.dH 0 0 ≠ 0 := by
  intro hZero
  have hComponent := congrArg
    (fun operator =>
      (operator (programPT05BulkGenerator 0 0))
        RelativeJetStratum4D.nonNullBoundary) hZero
  norm_num [programPT05ExactT03RelativeBicomplex,
    programPT05RelativeHorizontalDifferential, programPT05BulkGenerator] at hComponent

/-- The vertical variation differential is genuinely nonzero. -/
theorem programPT05RelativeVerticalDifferential_ne_zero :
    programPT05ExactT03RelativeBicomplex.dV 0 0 ≠ 0 := by
  intro hZero
  have hComponent := congrArg
    (fun operator =>
      (operator (programPT05BulkGenerator 0 0)) RelativeJetStratum4D.bulk) hZero
  norm_num [programPT05ExactT03RelativeBicomplex,
    programPT05RelativeVerticalDifferential, programPT05BulkGenerator] at hComponent

/-- The represented Euler obstruction is itself nonzero before passage to
horizontal cohomology. -/
theorem programPT05RelativeEulerObstruction_ne_zero :
    programPT05ExactT03RelativeBicomplex.dV 4 1
        programPT05RelativeEuler ≠ 0 := by
  intro hZero
  have hComponent := congrFun hZero RelativeJetStratum4D.nonNullBoundary
  norm_num [programPT05RelativeEuler, programPT05RelativeLagrangian,
    programPT05RelativeBoundaryPotential, programPT05BulkGenerator,
    programPT05ExactT03RelativeBicomplex,
    programPT05RelativeHorizontalDifferential,
    programPT05RelativeVerticalDifferential] at hComponent

/-- Its horizontal cohomology class nevertheless vanishes by the proved
relative first-variation exactness theorem. -/
theorem programPT05ExactT03RelativeObstructionClass_eq_zero :
    programPT05ExactT03RelativeFirstVariation.eulerObstructionClass = 0 :=
  programPT05ExactT03RelativeFirstVariation.eulerObstructionClass_eq_zero

variable (period : Real) (hPeriod : period ≠ 0)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
  (couplings : GlobalCandidateAActionCouplings)

section

variable {NullFace : Type*} [Fintype NullFace]
  {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (model : FiniteNullFacePhysicalActionModel NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local notation "ExactAction" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients

local notation "ExactEuler" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data model einsteinScale
      interactionScale coefficients

/-- Evaluation of a density-generator cochain against the exact integrated T03
action. -/
def programPT05ExactT03ActionEvaluation
    (input : Input) (cochain : RelativeJetCochain C 4 0) : Real :=
  (cochain .bulk).1 * ExactAction input

/-- Evaluation of a vertical-generator cochain against the exact T03 Euler
covector, tested in one exact T03 direction. -/
def programPT05ExactT03EulerEvaluation
    (input direction : Input) (cochain : RelativeJetCochain C 4 1) : Real :=
  (cochain .bulk).2 * ExactEuler input direction

/-- The distinguished relative Lagrangian evaluates to the exact T03 action. -/
theorem programPT05RelativeLagrangian_evaluates_to_exactT03Action
    (input : Input) :
    programPT05ExactT03ActionEvaluation period hPeriod plusBase minusBase hChart
        couplings data model einsteinScale interactionScale coefficients input
          programPT05RelativeLagrangian =
      ExactAction input := by
  simp [programPT05ExactT03ActionEvaluation,
    programPT05RelativeLagrangian, programPT05BulkGenerator]

/-- Evaluating the actual vertical differential of the Lagrangian gives the
exact T03 Euler covector in every direction. -/
theorem programPT05_dV_lagrangian_evaluates_to_exactT03Euler
    (input direction : Input) :
    programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase hChart
        couplings data model einsteinScale interactionScale coefficients input
          direction
          (programPT05ExactT03RelativeBicomplex.dV 4 0
            programPT05RelativeLagrangian) =
      ExactEuler input direction := by
  norm_num [programPT05ExactT03EulerEvaluation,
    programPT05RelativeLagrangian, programPT05BulkGenerator,
    programPT05ExactT03RelativeBicomplex,
    programPT05RelativeVerticalDifferential]

/-- The distinguished Euler cochain also evaluates to the exact T03 Euler;
its extra cellular terms are the relative boundary contribution. -/
theorem programPT05RelativeEuler_evaluates_to_exactT03Euler
    (input direction : Input) :
    programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase hChart
        couplings data model einsteinScale interactionScale coefficients input
          direction programPT05RelativeEuler =
      ExactEuler input direction := by
  norm_num [programPT05ExactT03EulerEvaluation, programPT05RelativeEuler,
    programPT05RelativeLagrangian, programPT05RelativeBoundaryPotential,
    programPT05BulkGenerator, programPT05ExactT03RelativeBicomplex,
    programPT05RelativeHorizontalDifferential,
    programPT05RelativeVerticalDifferential]

end

end
end P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
end JanusFormal
