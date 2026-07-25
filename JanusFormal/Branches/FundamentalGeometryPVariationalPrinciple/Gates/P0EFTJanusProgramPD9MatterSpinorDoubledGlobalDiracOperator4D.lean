import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D

/-!
# Global first-order Dirac contraction on the doubled D9 spinor bundle

The actual smooth doubled D9 bundle already carries a global covariant
derivative and three compatible Clifford generators.  A fixed basis of the
three-dimensional throat model contracts these data to a pointwise global
first-order operator.  Its local-cover formula is exact and its principal
Clifford symbol has the negative Euclidean square law and trivial kernel away
from the zero covector.

This gate does not identify the chosen model basis with a metric orthonormal
coframe, nor construct the independent primitive-monopole connection or an
unbounded self-adjoint realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDiracOperator4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- A fixed basis of the three-dimensional throat model.  It is coordinate
data, not yet a metric orthonormal coframe. -/
def d9ThroatModelBasis : Basis (Fin 3) Real ThroatCoverCoordinates := by
  let basis := Module.finBasis Real ThroatCoverCoordinates
  have hDimension : Module.finrank Real ThroatCoverCoordinates = 3 := by
    simp [ThroatCoverCoordinates]
  simpa [hDimension] using basis

/-- Coordinate square norm associated with the fixed model basis. -/
def d9ThroatModelCovectorNormSq
    (covector : ThroatCoverCoordinates) : Real :=
  ∑ direction : Fin 3,
    (d9ThroatModelBasis.repr covector direction) ^ 2

theorem d9ThroatModelCovectorNormSq_pos
    (covector : ThroatCoverCoordinates) (hCovector : covector ≠ 0) :
    0 < d9ThroatModelCovectorNormSq covector := by
  let coordinate := d9ThroatModelBasis.repr covector
  have hCoordinate : coordinate ≠ 0 := by
    intro hZero
    apply hCovector
    apply d9ThroatModelBasis.repr.injective
    simpa [coordinate] using hZero
  have hExists : ∃ direction : Fin 3, coordinate direction ≠ 0 := by
    by_contra h
    push Not at h
    apply hCoordinate
    ext direction
    simp [h direction]
  rcases hExists with ⟨direction, hDirection⟩
  exact Finset.sum_pos'
    (fun index _ => sq_nonneg (coordinate index))
    ⟨direction, Finset.mem_univ direction,
      sq_pos_of_ne_zero hDirection⟩

theorem d9ThroatModelCovectorNormSq_ne_zero
    (covector : ThroatCoverCoordinates) (hCovector : covector ≠ 0) :
    d9ThroatModelCovectorNormSq covector ≠ 0 :=
  ne_of_gt (d9ThroatModelCovectorNormSq_pos covector hCovector)

/-- Principal Clifford symbol in the fixed throat model basis. -/
def d9DoubledMatterFiberCliffordSymbol
    (covector : ThroatCoverCoordinates) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  (d9ThroatModelBasis.repr covector 0) •
      d9DoubledMatterFiberCliffordGammaCLM 0 +
    (d9ThroatModelBasis.repr covector 1) •
      d9DoubledMatterFiberCliffordGammaCLM 1 +
    (d9ThroatModelBasis.repr covector 2) •
      d9DoubledMatterFiberCliffordGammaCLM 2

@[simp] theorem d9DoubledMatterFiberCliffordSymbol_zero :
    d9DoubledMatterFiberCliffordSymbol
      (0 : ThroatCoverCoordinates) = 0 := by
  simp [d9DoubledMatterFiberCliffordSymbol]
  module

theorem d9DoubledMatterFiberCliffordSymbol_sq
    (covector : ThroatCoverCoordinates)
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordSymbol covector
        (d9DoubledMatterFiberCliffordSymbol covector matter) =
      -(d9ThroatModelCovectorNormSq covector) • matter := by
  let a := d9ThroatModelBasis.repr covector 0
  let b := d9ThroatModelBasis.repr covector 1
  let c := d9ThroatModelBasis.repr covector 2
  have h00 := d9DoubledMatterFiberCliffordGamma_sq (0 : Fin 3) matter
  have h11 := d9DoubledMatterFiberCliffordGamma_sq (1 : Fin 3) matter
  have h22 := d9DoubledMatterFiberCliffordGamma_sq (2 : Fin 3) matter
  have h01 := d9DoubledMatterFiberCliffordGamma_anticommute
    (0 : Fin 3) (1 : Fin 3) (by decide) matter
  have h02 := d9DoubledMatterFiberCliffordGamma_anticommute
    (0 : Fin 3) (2 : Fin 3) (by decide) matter
  have h12 := d9DoubledMatterFiberCliffordGamma_anticommute
    (1 : Fin 3) (2 : Fin 3) (by decide) matter
  have hNorm :
      d9ThroatModelCovectorNormSq covector =
        a ^ 2 + b ^ 2 + c ^ 2 := by
    simp [d9ThroatModelCovectorNormSq, a, b, c,
      Fin.sum_univ_succ]
    ring
  rw [hNorm]
  unfold d9DoubledMatterFiberCliffordSymbol
  change
    (a • d9DoubledMatterFiberCliffordGammaCLM 0 +
      b • d9DoubledMatterFiberCliffordGammaCLM 1 +
      c • d9DoubledMatterFiberCliffordGammaCLM 2)
        ((a • d9DoubledMatterFiberCliffordGammaCLM 0 +
          b • d9DoubledMatterFiberCliffordGammaCLM 1 +
          c • d9DoubledMatterFiberCliffordGammaCLM 2) matter) =
      -(a ^ 2 + b ^ 2 + c ^ 2) • matter
  simp only [add_apply, smul_apply,
    map_add, map_smul, d9DoubledMatterFiberCliffordGammaCLM_apply]
  rw [h00, h11, h22, h01, h02, h12]
  module

theorem d9DoubledMatterFiberCliffordSymbol_kernel_trivial
    (covector : ThroatCoverCoordinates) (hCovector : covector ≠ 0)
    (matter : D9DoubledMatterFiber)
    (hKernel : d9DoubledMatterFiberCliffordSymbol covector matter = 0) :
    matter = 0 := by
  have hSquare := congrArg
    (d9DoubledMatterFiberCliffordSymbol covector) hKernel
  rw [map_zero, d9DoubledMatterFiberCliffordSymbol_sq] at hSquare
  exact (smul_eq_zero.mp hSquare).resolve_left
    (neg_ne_zero.mpr
      (d9ThroatModelCovectorNormSq_ne_zero covector hCovector))

/-- Clifford contraction of the global covariant derivative at one point of
the actual doubled D9 bundle. -/
def d9DoubledMatterSpinorGlobalDiracAt
    (choice : NormalRootChoice)
    (spinorSection : ∀ base : ThroatBase period hPeriod,
      D9DoubledMatterSpinorFiber period hPeriod choice base)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterSpinorFiber period hPeriod choice base :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGammaCLM direction
      (d9DoubledMatterSpinorGlobalCovariantDerivativeAt
        period hPeriod choice spinorSection base
          (d9ThroatModelBasis direction))

/-- The global Dirac contraction applied to a genuine smooth doubled lift. -/
def d9DoubledMatterSpinorGlobalDirac
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    ∀ base : ThroatBase period hPeriod,
      D9DoubledMatterSpinorFiber period hPeriod choice base :=
  fun base =>
    d9DoubledMatterSpinorGlobalDiracAt period hPeriod choice
      (d9DoubledMatterSpinorSectionFiber
        period hPeriod choice lift) base

/-- Exact local-cover formula for the global Dirac contraction. -/
theorem d9DoubledMatterSpinorGlobalDirac_descended_flatCover
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorGlobalDirac period hPeriod choice lift base =
      ∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9DoubledMatterSpinorFlatCoverDerivative
            period hPeriod choice lift
              (normalBundleIndexAt period hPeriod base)
            (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              ((mappingTorusMk_isCoveringMap
                (ThroatData period hPeriod)).isLocalHomeomorph.localInverseAt
                  (normalBundleIndexAt period hPeriod base)) base
              (d9ThroatModelBasis direction))) := by
  unfold d9DoubledMatterSpinorGlobalDirac
    d9DoubledMatterSpinorGlobalDiracAt
  rw [d9DoubledMatterSpinorGlobalCovariantDerivative_descended_flatCover]
  rfl

/-- Applying the Dirac contraction after a constant Clifford generator has
the expected iterated-Clifford formula. -/
theorem d9DoubledMatterSpinorGlobalDirac_clifford
    (choice : NormalRootChoice) (generator : Fin 3)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorGlobalDirac period hPeriod choice
        (d9DoubledMatterSpinorCliffordLift
          period hPeriod choice generator lift) base =
      ∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9DoubledMatterFiberCliffordGammaCLM generator
            (d9DoubledMatterSpinorGlobalCovariantDerivativeAt
              period hPeriod choice
              (d9DoubledMatterSpinorSectionFiber
                period hPeriod choice lift) base
              (d9ThroatModelBasis direction))) := by
  unfold d9DoubledMatterSpinorGlobalDirac
    d9DoubledMatterSpinorGlobalDiracAt
  rw [d9DoubledMatterSpinorGlobalCovariantDerivative_clifford]
  rfl

structure ProgramPD9MatterSpinorDoubledGlobalDiracOperatorCertificate4D where
  choice : NormalRootChoice
  modelBasis : Basis (Fin 3) Real ThroatCoverCoordinates
  modelBasisCanonical : modelBasis = d9ThroatModelBasis
  symbol :
    ThroatCoverCoordinates →
      D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber
  symbolCanonical : symbol = d9DoubledMatterFiberCliffordSymbol
  symbolSquare : ∀ covector matter,
    symbol covector (symbol covector matter) =
      -(d9ThroatModelCovectorNormSq covector) • matter
  symbolElliptic : ∀ covector, covector ≠ 0 → ∀ matter,
    symbol covector matter = 0 → matter = 0
  operator :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →
      ∀ base : ThroatBase period hPeriod,
        D9DoubledMatterSpinorFiber period hPeriod choice base
  operatorCanonical :
    operator = d9DoubledMatterSpinorGlobalDirac period hPeriod choice
  flatCoverFormula : ∀ lift base,
    operator lift base =
      ∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9DoubledMatterSpinorFlatCoverDerivative
            period hPeriod choice lift
              (normalBundleIndexAt period hPeriod base)
            (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              ((mappingTorusMk_isCoveringMap
                (ThroatData period hPeriod)).isLocalHomeomorph.localInverseAt
                  (normalBundleIndexAt period hPeriod base)) base
              (modelBasis direction)))

def programPD9MatterSpinorDoubledGlobalDiracOperatorCertificate4D :
    ProgramPD9MatterSpinorDoubledGlobalDiracOperatorCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  modelBasis := d9ThroatModelBasis
  modelBasisCanonical := rfl
  symbol := d9DoubledMatterFiberCliffordSymbol
  symbolCanonical := rfl
  symbolSquare := d9DoubledMatterFiberCliffordSymbol_sq
  symbolElliptic := d9DoubledMatterFiberCliffordSymbol_kernel_trivial
  operator := d9DoubledMatterSpinorGlobalDirac
    period hPeriod .positiveQuarter
  operatorCanonical := rfl
  flatCoverFormula :=
    d9DoubledMatterSpinorGlobalDirac_descended_flatCover
      period hPeriod .positiveQuarter

theorem
    programPD9MatterSpinorDoubledGlobalDiracOperatorCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledGlobalDiracOperatorCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledGlobalDiracOperatorCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDiracOperator4D
end JanusFormal
