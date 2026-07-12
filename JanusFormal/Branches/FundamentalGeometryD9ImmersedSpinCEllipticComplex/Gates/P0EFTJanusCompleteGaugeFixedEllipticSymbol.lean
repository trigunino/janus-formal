import Mathlib
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusGaugeFixedPrincipalSymbols
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCliffordDiracPrincipalSymbol

namespace JanusFormal
namespace P0EFTJanusCompleteGaugeFixedEllipticSymbol

set_option autoImplicit false

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCliffordDiracPrincipalSymbol

/-- Bosonic fields of the local gauge-fixed immersion theory. -/
@[ext] structure GaugeFixedBosonicField where
  normalMode : ℝ
  gaugeOneForm : TangentVector3
  metricPerturbation : SymmetricTensor3

/-- Ghost fields for `U(1)` gauge symmetry and throat diffeomorphisms. -/
@[ext] structure GaugeFixedGhostField where
  u1Ghost : ℝ
  diffeomorphismGhost : TangentVector3

/-- Zero bosonic field. -/
def zeroBosonicField : GaugeFixedBosonicField :=
  { normalMode := 0
    gaugeOneForm := zeroTangent
    metricPerturbation := zeroSymmetric }

/-- Zero ghost field. -/
def zeroGhostField : GaugeFixedGhostField :=
  { u1Ghost := 0
    diffeomorphismGhost := zeroTangent }

/-- Block-diagonal bosonic principal symbol. -/
def bosonicPrincipalSymbol
    (covector : TangentVector3)
    (field : GaugeFixedBosonicField) : GaugeFixedBosonicField :=
  { normalMode := normalJacobiSymbol covector field.normalMode
    gaugeOneForm := maxwellGaugeFixedSymbol covector field.gaugeOneForm
    metricPerturbation :=
      metricLaplacianSymbol covector field.metricPerturbation }

/-- Block-diagonal ghost principal symbol. -/
def ghostPrincipalSymbol
    (covector : TangentVector3)
    (field : GaugeFixedGhostField) : GaugeFixedGhostField :=
  { u1Ghost := normSquared covector * field.u1Ghost
    diffeomorphismGhost :=
      ghostLaplacianSymbol covector field.diffeomorphismGhost }

/-- The full bosonic symbol has trivial kernel at nonzero covector. -/
theorem bosonic_principal_symbol_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (field : GaugeFixedBosonicField)
    (hKernel :
      bosonicPrincipalSymbol covector field = zeroBosonicField) :
    field = zeroBosonicField := by
  have hNormal :
      normalJacobiSymbol covector field.normalMode = 0 :=
    congrArg GaugeFixedBosonicField.normalMode hKernel
  have hGauge :
      maxwellGaugeFixedSymbol covector field.gaugeOneForm =
        zeroTangent :=
    congrArg GaugeFixedBosonicField.gaugeOneForm hKernel
  have hMetric :
      metricLaplacianSymbol covector field.metricPerturbation =
        zeroSymmetric :=
    congrArg GaugeFixedBosonicField.metricPerturbation hKernel
  exact GaugeFixedBosonicField.ext
    (normal_jacobi_kernel_trivial covector hCovector
      field.normalMode hNormal)
    (maxwell_symbol_kernel_trivial covector hCovector
      field.gaugeOneForm hGauge)
    (metric_symbol_kernel_trivial covector hCovector
      field.metricPerturbation hMetric)

/-- The complete ghost symbol has trivial kernel. -/
theorem ghost_principal_symbol_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (field : GaugeFixedGhostField)
    (hKernel :
      ghostPrincipalSymbol covector field = zeroGhostField) :
    field = zeroGhostField := by
  have hU1 : normSquared covector * field.u1Ghost = 0 :=
    congrArg GaugeFixedGhostField.u1Ghost hKernel
  have hDiff :
      ghostLaplacianSymbol covector field.diffeomorphismGhost =
        zeroTangent :=
    congrArg GaugeFixedGhostField.diffeomorphismGhost hKernel
  have hU1Zero : field.u1Ghost = 0 :=
    (mul_eq_zero.mp hU1).resolve_left
      (ne_of_gt (norm_squared_positive_of_nonzero
        covector hCovector))
  exact GaugeFixedGhostField.ext hU1Zero
    (ghost_symbol_kernel_trivial covector hCovector
      field.diffeomorphismGhost hDiff)

/-- Full local field at principal-symbol level. -/
@[ext] structure CompleteLocalField
    (Spinor : Type*) where
  bosonic : GaugeFixedBosonicField
  ghosts : GaugeFixedGhostField
  spinor : Spinor

/-- Zero full field. -/
def zeroCompleteLocalField
    {Spinor : Type*}
    [Zero Spinor] : CompleteLocalField Spinor :=
  { bosonic := zeroBosonicField
    ghosts := zeroGhostField
    spinor := 0 }

/-- Complete block symbol. -/
def completePrincipalSymbol
    {Spinor : Type*}
    [Zero Spinor]
    [SMul ℝ Spinor]
    (clifford : CliffordSymbolData Spinor)
    (covector : TangentVector3)
    (field : CompleteLocalField Spinor) : CompleteLocalField Spinor :=
  { bosonic := bosonicPrincipalSymbol covector field.bosonic
    ghosts := ghostPrincipalSymbol covector field.ghosts
    spinor := clifford.symbol covector field.spinor }

/-- The assembled gauge-fixed symbol is elliptic. -/
theorem complete_principal_symbol_kernel_trivial
    {Spinor : Type*}
    [Zero Spinor]
    [SMul ℝ Spinor]
    (clifford : CliffordSymbolData Spinor)
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (field : CompleteLocalField Spinor)
    (hKernel :
      completePrincipalSymbol clifford covector field =
        zeroCompleteLocalField) :
    field = zeroCompleteLocalField := by
  have hBosonic :
      bosonicPrincipalSymbol covector field.bosonic =
        zeroBosonicField :=
    congrArg (fun value => value.bosonic) hKernel
  have hGhosts :
      ghostPrincipalSymbol covector field.ghosts =
        zeroGhostField :=
    congrArg (fun value => value.ghosts) hKernel
  have hSpinor : clifford.symbol covector field.spinor = 0 :=
    congrArg (fun value => value.spinor) hKernel
  exact CompleteLocalField.ext
    (bosonic_principal_symbol_kernel_trivial
      covector hCovector field.bosonic hBosonic)
    (ghost_principal_symbol_kernel_trivial
      covector hCovector field.ghosts hGhosts)
    (dirac_symbol_kernel_trivial
      clifford covector hCovector field.spinor hSpinor)

/-- Raw fiber ranks before gauge quotient. -/
def normalBosonRank : ℕ := 1

def gaugeOneFormRank : ℕ := 3

def metricTensorRank : ℕ := 6

def u1GhostRank : ℕ := 1

def diffeomorphismGhostRank : ℕ := 3

/-- Gravity BRST super-rank `6 - 2*3 = 0` in three dimensions. -/
def gravityOneLoopSuperRank : ℤ :=
  (metricTensorRank : ℤ) - 2 * diffeomorphismGhostRank

/-- Maxwell BRST super-rank `3 - 2*1 = 1`. -/
def maxwellOneLoopSuperRank : ℤ :=
  (gaugeOneFormRank : ℤ) - 2 * u1GhostRank

@[simp] theorem gravity_one_loop_super_rank_zero :
    gravityOneLoopSuperRank = 0 := by
  norm_num [gravityOneLoopSuperRank,
    metricTensorRank, diffeomorphismGhostRank]

@[simp] theorem maxwell_one_loop_super_rank_one :
    maxwellOneLoopSuperRank = 1 := by
  norm_num [maxwellOneLoopSuperRank,
    gaugeOneFormRank, u1GhostRank]

/-- The immersion contributes one independent normal scalar after quotienting reparametrizations. -/
@[simp] theorem physical_normal_rank_one :
    normalBosonRank = 1 := by rfl

/--
This is the complete local principal-symbol complex requested by D9. It proves
ellipticity after gauge fixing, but not the determinant weights: lower-order
curvature, masses, boundary phases, zero modes and Jacobians remain essential.
-/
structure CompleteEllipticComplexPhysicalStatus where
  immersedSpinCHypersurfaceConstructed : Prop
  normalJacobiOperatorConstructed : Prop
  maxwellOperatorConstructed : Prop
  u1GaugeFixingAndGhostsDerived : Prop
  lichnerowiczOperatorConstructed : Prop
  diffeomorphismGaugeFixingAndGhostsDerived : Prop
  twistedDiracOperatorConstructed : Prop
  commonDomainAndBoundaryConditionsDerived : Prop
  principalSymbolIdentifiedWithBlockModel : Prop
  ellipticityProvedGlobally : Prop
  zeroModesAndCohomologyComputed : Prop
  zetaSuperdeterminantDefined : Prop


def completeEllipticComplexPhysicalClosure
    (s : CompleteEllipticComplexPhysicalStatus) : Prop :=
  s.immersedSpinCHypersurfaceConstructed /\
  s.normalJacobiOperatorConstructed /\
  s.maxwellOperatorConstructed /\
  s.u1GaugeFixingAndGhostsDerived /\
  s.lichnerowiczOperatorConstructed /\
  s.diffeomorphismGaugeFixingAndGhostsDerived /\
  s.twistedDiracOperatorConstructed /\
  s.commonDomainAndBoundaryConditionsDerived /\
  s.principalSymbolIdentifiedWithBlockModel /\
  s.ellipticityProvedGlobally /\
  s.zeroModesAndCohomologyComputed /\
  s.zetaSuperdeterminantDefined

end P0EFTJanusCompleteGaugeFixedEllipticSymbol
end JanusFormal
