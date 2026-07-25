import JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators.Gates.P0EFTJanusNaturalOperatorBlueprint
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCorrectedJetUniversality

/-!
# Natural-operator classification at the Program-P EFT frontier

The unrestricted corrected classification is by smooth equivariant finite-jet
evaluators.  The finite EFT truncation used below keeps the six displayed
zero-order immersion invariants.  In that truncation the coefficient package
is recovered uniquely by evaluation on six basis jets.

This separates a genuine classification theorem from a uniqueness claim:
canonical principal symbols and Helmholtz symmetry leave all six zero-order
couplings free in every displayed sector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNaturalOperatorClassification4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusNaturalOperatorBlueprint
open P0EFTJanusNaturalLowerOrderFreedom
open P0EFTJanusFiniteJetEquivariance
open P0EFTJanusCorrectedJetUniversality

universe u v w x

/-- Exact corrected classification of any supplied regular local natural
operator: it has one and only one equivariant finite-jet evaluator. -/
theorem regularLocalNaturalOperator_classifiedByUniqueEquivariantJetEvaluator
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : CorrectedLocalJetData Symmetry Section Jet Target)
    (hNatural :
      IsNaturalOperator data.presentation.sectionAction
        data.presentation.targetAction data.presentation.operator) :
    ∃! evaluator : Jet → Target,
      (∀ sectionValue,
        data.presentation.operator sectionValue =
          evaluator (data.presentation.jet sectionValue)) ∧
      IsEquivariant data.presentation.jetAction
        data.presentation.targetAction evaluator :=
  corrected_local_jet_universality data hNatural

/-- The six invariant coordinates retained by the displayed second-order EFT
truncation. -/
inductive ZeroOrderInvariant where
  | scalarCurvature
  | meanCurvatureSquared
  | secondFundamentalNormSquared
  | gaugeCurvatureNormSquared
  | normalCurvaturePotential
  | massSquared
  deriving DecidableEq, Fintype, Repr

/-- Coordinate basis of the six-dimensional invariant-jet test space. -/
def invariantBasisJet : ZeroOrderInvariant → ImmersionInvariantJet
  | .scalarCurvature =>
      { scalarCurvature := 1
        meanCurvatureSquared := 0
        secondFundamentalNormSquared := 0
        gaugeCurvatureNormSquared := 0
        normalCurvaturePotential := 0 }
  | .meanCurvatureSquared =>
      { scalarCurvature := 0
        meanCurvatureSquared := 1
        secondFundamentalNormSquared := 0
        gaugeCurvatureNormSquared := 0
        normalCurvaturePotential := 0 }
  | .secondFundamentalNormSquared =>
      { scalarCurvature := 0
        meanCurvatureSquared := 0
        secondFundamentalNormSquared := 1
        gaugeCurvatureNormSquared := 0
        normalCurvaturePotential := 0 }
  | .gaugeCurvatureNormSquared =>
      { scalarCurvature := 0
        meanCurvatureSquared := 0
        secondFundamentalNormSquared := 0
        gaugeCurvatureNormSquared := 1
        normalCurvaturePotential := 0 }
  | .normalCurvaturePotential =>
      { scalarCurvature := 0
        meanCurvatureSquared := 0
        secondFundamentalNormSquared := 0
        gaugeCurvatureNormSquared := 0
        normalCurvaturePotential := 1 }
  | .massSquared =>
      { scalarCurvature := 0
        meanCurvatureSquared := 0
        secondFundamentalNormSquared := 0
        gaugeCurvatureNormSquared := 0
        normalCurvaturePotential := 0 }

/-- Coordinate accessor on a coupling package. -/
def couplingCoordinate
    (couplings : NaturalPotentialCouplings) :
    ZeroOrderInvariant → ℝ
  | .scalarCurvature => couplings.scalarCurvature
  | .meanCurvatureSquared => couplings.meanCurvatureSquared
  | .secondFundamentalNormSquared =>
      couplings.secondFundamentalNormSquared
  | .gaugeCurvatureNormSquared => couplings.gaugeCurvatureNormSquared
  | .normalCurvaturePotential => couplings.normalCurvaturePotential
  | .massSquared => couplings.massSquared

/-- Recover one affine coefficient from a potential.  The mass is its value at
the zero jet; every other coefficient is a basis value minus that value. -/
def potentialCoordinate
    (potential : ImmersionInvariantJet → ℝ) :
    ZeroOrderInvariant → ℝ
  | .scalarCurvature =>
      potential (invariantBasisJet .scalarCurvature) -
        potential (invariantBasisJet .massSquared)
  | .meanCurvatureSquared =>
      potential (invariantBasisJet .meanCurvatureSquared) -
        potential (invariantBasisJet .massSquared)
  | .secondFundamentalNormSquared =>
      potential (invariantBasisJet .secondFundamentalNormSquared) -
        potential (invariantBasisJet .massSquared)
  | .gaugeCurvatureNormSquared =>
      potential (invariantBasisJet .gaugeCurvatureNormSquared) -
        potential (invariantBasisJet .massSquared)
  | .normalCurvaturePotential =>
      potential (invariantBasisJet .normalCurvaturePotential) -
        potential (invariantBasisJet .massSquared)
  | .massSquared =>
      potential (invariantBasisJet .massSquared)

/-- Each coupling is recovered by the corresponding affine coordinate
evaluation. -/
@[simp]
theorem potentialCoordinate_naturalPotential
    (couplings : NaturalPotentialCouplings)
    (coordinate : ZeroOrderInvariant) :
    potentialCoordinate (naturalPotential couplings) coordinate =
      couplingCoordinate couplings coordinate := by
  cases coordinate <;>
    simp [potentialCoordinate, naturalPotential, invariantBasisJet,
      couplingCoordinate]

/-- The six-invariant evaluator loses no coefficient. -/
theorem naturalPotential_evaluator_injective :
    Function.Injective
      (fun couplings : NaturalPotentialCouplings =>
        fun jet => naturalPotential couplings jet) := by
  intro first second hEqual
  have hCoordinate :
      ∀ coordinate,
        couplingCoordinate first coordinate =
          couplingCoordinate second coordinate := by
    intro coordinate
    calc
      couplingCoordinate first coordinate =
          potentialCoordinate (naturalPotential first) coordinate :=
        (potentialCoordinate_naturalPotential first coordinate).symm
      _ = potentialCoordinate (naturalPotential second) coordinate :=
        congrArg (fun potential => potentialCoordinate potential coordinate)
          hEqual
      _ = couplingCoordinate second coordinate :=
        potentialCoordinate_naturalPotential second coordinate
  cases first with
  | mk firstR firstH firstII firstF firstN firstM =>
      cases second with
      | mk secondR secondH secondII secondF secondN secondM =>
          have hR := hCoordinate ZeroOrderInvariant.scalarCurvature
          have hH := hCoordinate ZeroOrderInvariant.meanCurvatureSquared
          have hII :=
            hCoordinate ZeroOrderInvariant.secondFundamentalNormSquared
          have hF :=
            hCoordinate ZeroOrderInvariant.gaugeCurvatureNormSquared
          have hN :=
            hCoordinate ZeroOrderInvariant.normalCurvaturePotential
          have hM := hCoordinate ZeroOrderInvariant.massSquared
          simp only [couplingCoordinate] at hR hH hII hF hN hM
          subst secondR
          subst secondH
          subst secondII
          subst secondF
          subst secondN
          subst secondM
          rfl

/-- A zero-order potential belongs to the displayed EFT truncation exactly
when it is a linear combination of the six retained invariant coordinates. -/
def IsSixInvariantEFTPotential
    (potential : ImmersionInvariantJet → ℝ) : Prop :=
  ∃ couplings : NaturalPotentialCouplings,
    potential = naturalPotential couplings

/-- Every potential in the six-invariant truncation has unique coefficients. -/
theorem sixInvariantEFTPotential_existsUnique_coefficients
    (potential : ImmersionInvariantJet → ℝ)
    (hEFT : IsSixInvariantEFTPotential potential) :
    ∃! couplings : NaturalPotentialCouplings,
      potential = naturalPotential couplings := by
  obtain ⟨couplings, hCouplings⟩ := hEFT
  refine ⟨couplings, hCouplings, ?_⟩
  intro other hOther
  apply naturalPotential_evaluator_injective
  exact hOther.symm.trans hCouplings

/-- Independent lower-order coefficients for every natural sector. -/
abbrev ProgramPLowerOrderCoefficients :=
  NaturalOperatorSector → NaturalPotentialCouplings

/-- Pointwise lower-order evaluator for the six displayed sectors. -/
def programPLowerOrderEvaluator
    (coefficients : ProgramPLowerOrderCoefficients) :
    NaturalOperatorSector → ImmersionInvariantJet → ℝ :=
  fun sector jet => naturalPotential (coefficients sector) jet

/-- Sectorwise evaluation still recovers the complete coefficient family. -/
theorem programPLowerOrderEvaluator_injective :
    Function.Injective programPLowerOrderEvaluator := by
  intro first second hEqual
  funext sector
  apply naturalPotential_evaluator_injective
  funext jet
  exact congrFun (congrFun hEqual sector) jet

/-- Full pointwise scalar Laplace-type model with the canonical principal
symbol and a classified six-invariant lower-order term. -/
def programPLaplaceTypeOperator
    (coefficients : ProgramPLowerOrderCoefficients)
    (sector : NaturalOperatorSector)
    (normSquared field : ℝ)
    (jet : ImmersionInvariantJet) : ℝ :=
  normSquared * field +
    naturalPotential (coefficients sector) jet * field

/-- Every classified lower-order choice has the same canonical principal
symbol. -/
theorem programPLaplaceTypeOperator_principalSymbol
    (first second : ProgramPLowerOrderCoefficients)
    (sector : NaturalOperatorSector)
    (normSquared field : ℝ) :
    principalSymbol
        (laplaceModelFromNaturalData (first sector)
          (invariantBasisJet .massSquared))
        normSquared field =
      principalSymbol
        (laplaceModelFromNaturalData (second sector)
          (invariantBasisJet .massSquared))
        normSquared field := by
  rfl

/-- Pointwise real multiplication by every classified Laplace-type operator is
formally self-adjoint.  Thus this Helmholtz test does not fix the lower-order
couplings. -/
theorem programPLaplaceTypeOperator_pointwiseSelfAdjoint
    (coefficients : ProgramPLowerOrderCoefficients)
    (sector : NaturalOperatorSector)
    (normSquared : ℝ)
    (jet : ImmersionInvariantJet)
    (first second : ℝ) :
    programPLaplaceTypeOperator coefficients sector normSquared first jet *
        second =
      first *
        programPLaplaceTypeOperator coefficients sector normSquared second
          jet := by
  unfold programPLaplaceTypeOperator
  ring

/-- Coefficient package with every lower-order invariant set to zero. -/
def zeroProgramPLowerOrderCoefficients : ProgramPLowerOrderCoefficients :=
  fun _ => zeroNaturalCouplings

/-- A unit mass only in the normal-Jacobi sector. -/
def unitNormalMassProgramPLowerOrderCoefficients :
    ProgramPLowerOrderCoefficients :=
  fun sector =>
    if sector = NaturalOperatorSector.normalJacobi then
      { zeroNaturalCouplings with massSquared := 1 }
    else
      zeroNaturalCouplings

/-- Canonical principal symbols plus pointwise Helmholtz symmetry do not select
a unique Program-P operator: the normal mass remains free. -/
theorem canonicalSymbol_and_pointwiseHelmholtz_do_not_fix_operator :
    zeroProgramPLowerOrderCoefficients ≠
      unitNormalMassProgramPLowerOrderCoefficients := by
  intro hEqual
  have hNormal := congrArg
    (fun coefficients =>
      (coefficients NaturalOperatorSector.normalJacobi).massSquared)
    hEqual
  norm_num [zeroProgramPLowerOrderCoefficients,
    unitNormalMassProgramPLowerOrderCoefficients, zeroNaturalCouplings] at hNormal

end

end P0EFTJanusProgramPNaturalOperatorClassification4D
end JanusFormal
