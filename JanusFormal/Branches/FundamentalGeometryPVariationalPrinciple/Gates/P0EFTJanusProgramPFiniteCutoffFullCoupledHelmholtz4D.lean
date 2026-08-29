import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteRankPolynomialHelmholtz
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-!
# Finite-cutoff realization of the full coupled Helmholtz bridge

For any finite mode type, all nine Program-P blocks are represented on the
single normed chart `ι → ℝ`.  Cubic polynomial blocks are genuinely `C²`, so
the abstract full-coupled bridge is inhabited.  Conversely, nine finite Euler
blocks satisfying the actual Helmholtz condition reconstruct a normalized
full action: every block has its prescribed Fréchet derivative and the sum is
genuinely `C²` with Helmholtz-symmetric Jacobian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteCutoffFullCoupledHelmholtz4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusFiniteRankPolynomialHelmholtz
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

universe u

/-- One common finite-dimensional cutoff chart. -/
abbrev FiniteConfiguration (ι : Type u) := ι → ℝ

/-- Cubic polynomial data for all nine action blocks. -/
structure FullCoupledFinitePolynomialData
    (ι : Type u) where
  candidateA : CubicPotentialCoefficients ι
  matter : CubicPotentialCoefficients ι
  robin : CubicPotentialCoefficients ι
  ll : CubicPotentialCoefficients ι
  einsteinHilbertPlus : CubicPotentialCoefficients ι
  einsteinHilbertMinus : CubicPotentialCoefficients ι
  maxwellPlus : CubicPotentialCoefficients ι
  maxwellMinus : CubicPotentialCoefficients ι
  finiteBV : CubicPotentialCoefficients ι

/-- The nine finite polynomial functionals on one chart. -/
def finitePolynomialActionBlocks
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι) :
    FullCoupledActionBlocks (FiniteConfiguration ι) where
  candidateA := potentialValue data.candidateA
  matter := potentialValue data.matter
  robin := potentialValue data.robin
  ll := potentialValue data.ll
  einsteinHilbertPlus := potentialValue data.einsteinHilbertPlus
  einsteinHilbertMinus := potentialValue data.einsteinHilbertMinus
  maxwellPlus := potentialValue data.maxwellPlus
  maxwellMinus := potentialValue data.maxwellMinus
  finiteBV := potentialValue data.finiteBV

/-- Every normalized finite polynomial block is genuinely `C²`. -/
theorem finitePolynomialPotential_contDiffAt_two
    {ι : Type u} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (configuration : FiniteConfiguration ι) :
    ContDiffAt ℝ 2 (potentialValue potential) configuration := by
  apply ContDiff.contDiffAt
  unfold potentialValue
  fun_prop

/-- Concrete common-chart `C²` certificate for all nine blocks. -/
def finitePolynomialActionBlocks_c2
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι)
    (configuration : FiniteConfiguration ι) :
    FullCoupledC2At
      (finitePolynomialActionBlocks data) configuration where
  candidateA :=
    finitePolynomialPotential_contDiffAt_two data.candidateA configuration
  matter :=
    finitePolynomialPotential_contDiffAt_two data.matter configuration
  robin :=
    finitePolynomialPotential_contDiffAt_two data.robin configuration
  ll :=
    finitePolynomialPotential_contDiffAt_two data.ll configuration
  einsteinHilbertPlus :=
    finitePolynomialPotential_contDiffAt_two
      data.einsteinHilbertPlus configuration
  einsteinHilbertMinus :=
    finitePolynomialPotential_contDiffAt_two
      data.einsteinHilbertMinus configuration
  maxwellPlus :=
    finitePolynomialPotential_contDiffAt_two data.maxwellPlus configuration
  maxwellMinus :=
    finitePolynomialPotential_contDiffAt_two data.maxwellMinus configuration
  finiteBV :=
    finitePolynomialPotential_contDiffAt_two data.finiteBV configuration

/-- Actual summed finite-cutoff action. -/
def finitePolynomialFullAction
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι) :
    FiniteConfiguration ι → ℝ :=
  fullCoupledAction (finitePolynomialActionBlocks data)

/-- Affine action curve on the common finite chart. -/
def finitePolynomialFullActionCurve
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι)
    (configuration variation : FiniteConfiguration ι)
    (parameter : ℝ) : ℝ :=
  finitePolynomialFullAction data
    (configuration + parameter • variation)

/-- The abstract concrete-Fréchet bridge is inhabited without assumptions at
every finite cutoff. -/
def finitePolynomialConcreteFrechetBridge
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι) :
    ConcreteFullActionFrechetBridge
      (FiniteConfiguration ι) (FiniteConfiguration ι)
      (finitePolynomialFullActionCurve data) where
  Configuration := FiniteConfiguration ι
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  encodeConfiguration := id
  encodeVariation := id
  blocks := finitePolynomialActionBlocks data
  affineCurve := fun configuration variation parameter =>
    configuration + parameter • variation
  affineCurve_zero := by
    intro configuration variation
    simp
  curve_agreement := by
    intro configuration variation parameter
    rfl
  blocks_c2 := finitePolynomialActionBlocks_c2 data

/-- Genuine nonlinear Helmholtz reciprocity of the finite-cutoff full action. -/
theorem finitePolynomialFullAction_helmholtz
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι)
    (configuration : FiniteConfiguration ι) :
    HelmholtzJacobianAt
      (actionGradient (finitePolynomialFullAction data)) configuration := by
  exact fullCoupledAction_helmholtz
    (finitePolynomialActionBlocks data) configuration
      (finitePolynomialActionBlocks_c2 data configuration)

@[simp]
theorem finitePolynomialFullAction_zero
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFinitePolynomialData ι) :
    finitePolynomialFullAction data 0 = 0 := by
  simp [finitePolynomialFullAction, finitePolynomialActionBlocks,
    fullCoupledAction, potentialValue]

/-- A finite Euler block satisfying the actual Jacobian Helmholtz condition. -/
structure FiniteHelmholtzEulerBlock
    (ι : Type u) [Fintype ι] where
  euler : QuadraticEulerCoefficients ι
  helmholtz : ActualFiniteHelmholtz euler

def FiniteHelmholtzEulerBlock.linearReciprocity
    {ι : Type u} [Fintype ι]
    (block : FiniteHelmholtzEulerBlock ι) :
    LinearReciprocity block.euler :=
  ((actual_finite_helmholtz_iff_coefficient_helmholtz block.euler).1
    block.helmholtz).1

def FiniteHelmholtzEulerBlock.quadraticHelmholtz
    {ι : Type u} [Fintype ι]
    (block : FiniteHelmholtzEulerBlock ι) :
    QuadraticHelmholtzSwap block.euler :=
  ((actual_finite_helmholtz_iff_coefficient_helmholtz block.euler).1
    block.helmholtz).2

/-- Canonical normalized primitive reconstructed from one Euler block. -/
def FiniteHelmholtzEulerBlock.potential
    {ι : Type u} [Fintype ι]
    (block : FiniteHelmholtzEulerBlock ι) :
    CubicPotentialCoefficients ι :=
  reconstructedPotential block.euler block.linearReciprocity
    block.quadraticHelmholtz

/-- The reconstructed primitive has exactly the prescribed Euler derivative. -/
theorem FiniteHelmholtzEulerBlock.potential_hasFDerivAt
    {ι : Type u} [Fintype ι]
    (block : FiniteHelmholtzEulerBlock ι)
    (configuration : FiniteConfiguration ι) :
    HasFDerivAt (potentialValue block.potential)
      (eulerGradientFunctional block.euler configuration) configuration := by
  exact formal_gradient_is_actual_polynomial_gradient block.euler
    block.potential
      (reconstructed_is_formal_gradient block.euler
        block.linearReciprocity block.quadraticHelmholtz)
      configuration

/-- Nine actual finite Helmholtz Euler blocks. -/
structure FullCoupledFiniteEulerData
    (ι : Type u) [Fintype ι] where
  candidateA : FiniteHelmholtzEulerBlock ι
  matter : FiniteHelmholtzEulerBlock ι
  robin : FiniteHelmholtzEulerBlock ι
  ll : FiniteHelmholtzEulerBlock ι
  einsteinHilbertPlus : FiniteHelmholtzEulerBlock ι
  einsteinHilbertMinus : FiniteHelmholtzEulerBlock ι
  maxwellPlus : FiniteHelmholtzEulerBlock ι
  maxwellMinus : FiniteHelmholtzEulerBlock ι
  finiteBV : FiniteHelmholtzEulerBlock ι

/-- Canonical nine-block action data reconstructed from the Euler system. -/
def FullCoupledFiniteEulerData.polynomialData
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFiniteEulerData ι) :
    FullCoupledFinitePolynomialData ι where
  candidateA := data.candidateA.potential
  matter := data.matter.potential
  robin := data.robin.potential
  ll := data.ll.potential
  einsteinHilbertPlus := data.einsteinHilbertPlus.potential
  einsteinHilbertMinus := data.einsteinHilbertMinus.potential
  maxwellPlus := data.maxwellPlus.potential
  maxwellMinus := data.maxwellMinus.potential
  finiteBV := data.finiteBV.potential

/-- Exact blockwise Euler realization of the reconstructed finite action. -/
structure FullCoupledFiniteEulerRealizationAt
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFiniteEulerData ι)
    (configuration : FiniteConfiguration ι) : Prop where
  candidateA : HasFDerivAt (potentialValue data.candidateA.potential)
    (eulerGradientFunctional data.candidateA.euler configuration) configuration
  matter : HasFDerivAt (potentialValue data.matter.potential)
    (eulerGradientFunctional data.matter.euler configuration) configuration
  robin : HasFDerivAt (potentialValue data.robin.potential)
    (eulerGradientFunctional data.robin.euler configuration) configuration
  ll : HasFDerivAt (potentialValue data.ll.potential)
    (eulerGradientFunctional data.ll.euler configuration) configuration
  einsteinHilbertPlus :
    HasFDerivAt (potentialValue data.einsteinHilbertPlus.potential)
      (eulerGradientFunctional data.einsteinHilbertPlus.euler configuration)
      configuration
  einsteinHilbertMinus :
    HasFDerivAt (potentialValue data.einsteinHilbertMinus.potential)
      (eulerGradientFunctional data.einsteinHilbertMinus.euler configuration)
      configuration
  maxwellPlus : HasFDerivAt (potentialValue data.maxwellPlus.potential)
    (eulerGradientFunctional data.maxwellPlus.euler configuration) configuration
  maxwellMinus : HasFDerivAt (potentialValue data.maxwellMinus.potential)
    (eulerGradientFunctional data.maxwellMinus.euler configuration) configuration
  finiteBV : HasFDerivAt (potentialValue data.finiteBV.potential)
    (eulerGradientFunctional data.finiteBV.euler configuration) configuration

/-- All nine reconstructed blocks have exactly their prescribed Euler forms. -/
def reconstructedFullAction_eulerRealizationAt
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFiniteEulerData ι)
    (configuration : FiniteConfiguration ι) :
    FullCoupledFiniteEulerRealizationAt data configuration where
  candidateA := data.candidateA.potential_hasFDerivAt configuration
  matter := data.matter.potential_hasFDerivAt configuration
  robin := data.robin.potential_hasFDerivAt configuration
  ll := data.ll.potential_hasFDerivAt configuration
  einsteinHilbertPlus :=
    data.einsteinHilbertPlus.potential_hasFDerivAt configuration
  einsteinHilbertMinus :=
    data.einsteinHilbertMinus.potential_hasFDerivAt configuration
  maxwellPlus := data.maxwellPlus.potential_hasFDerivAt configuration
  maxwellMinus := data.maxwellMinus.potential_hasFDerivAt configuration
  finiteBV := data.finiteBV.potential_hasFDerivAt configuration

/-- The Helmholtz-reconstructed nine-block action inhabits the concrete
common-chart bridge. -/
def reconstructedFullConcreteFrechetBridge
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFiniteEulerData ι) :
    ConcreteFullActionFrechetBridge
      (FiniteConfiguration ι) (FiniteConfiguration ι)
      (finitePolynomialFullActionCurve data.polynomialData) :=
  finitePolynomialConcreteFrechetBridge data.polynomialData

/-- The reconstructed complete finite action has an actual symmetric
Fréchet Hessian at every configuration. -/
theorem reconstructedFullAction_helmholtz
    {ι : Type u} [Fintype ι]
    (data : FullCoupledFiniteEulerData ι)
    (configuration : FiniteConfiguration ι) :
    HelmholtzJacobianAt
      (actionGradient (finitePolynomialFullAction data.polynomialData))
      configuration :=
  finitePolynomialFullAction_helmholtz data.polynomialData configuration

end

end P0EFTJanusProgramPFiniteCutoffFullCoupledHelmholtz4D
end JanusFormal
