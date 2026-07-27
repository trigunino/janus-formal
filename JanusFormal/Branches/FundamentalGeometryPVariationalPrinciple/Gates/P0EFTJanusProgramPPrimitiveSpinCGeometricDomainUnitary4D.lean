import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# Unitary transport of the full primitive SpinC graph domain

The complete primitive SpinC coefficient tower is already isometric to the
extended D10 labels at the ambient `L²` level.  This gate proves that the same
reindexing transports the maximal squared-Dirac domain exactly, intertwines
the unbounded operators and preserves their graph energy.

This is a coefficient-domain theorem.  The remaining geometric Fourier
frontier is the construction and completeness of all smooth eigenspinors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance primitiveSpinCExtendedD10ModeDecidableEq :
    DecidableEq (PrimitiveSpinCExtendedD10Mode period hPeriod) :=
  Classical.decEq _

/-- The full squared-Dirac weight written in the extended D10 labels. -/
def primitiveSpinCExtendedD10SquaredEigenvalue
    (mode : PrimitiveSpinCExtendedD10Mode period hPeriod) : Real :=
  primitiveSpinCGeometricSquaredEigenvalue period hPeriod
    ((primitiveSpinCGeometricFullModeEquiv period hPeriod).symm mode)

@[simp]
theorem primitiveSpinCExtendedD10SquaredEigenvalue_zero
    (choice : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCExtendedD10SquaredEigenvalue period hPeriod
        (Sum.inl (choice, circleMode)) =
      circleEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod)
        choice circleMode ^ 2 := by
  have hMode :
      (primitiveSpinCGeometricFullModeEquiv period hPeriod).symm
          (Sum.inl (choice, circleMode)) =
        primitiveSpinCGeometricZeroMode choice circleMode := by
    apply (primitiveSpinCGeometricFullModeEquiv period hPeriod).injective
    simp
  rw [primitiveSpinCExtendedD10SquaredEigenvalue, hMode,
    primitiveSpinCGeometricZeroMode_squaredEigenvalue]

@[simp]
theorem primitiveSpinCExtendedD10SquaredEigenvalue_positive
    (mode : ProgramPD10Mode4D
      (PrimitiveSpinCSpectralData period hPeriod)) :
    primitiveSpinCExtendedD10SquaredEigenvalue period hPeriod
        (Sum.inr mode) =
      productDiracEigenvalueSquared
        (PrimitiveSpinCSpectralData period hPeriod)
        mode.separatedMode := by
  have hMode :
      (primitiveSpinCGeometricFullModeEquiv period hPeriod).symm
          (Sum.inr mode) =
        programPD10ModeToPrimitiveSpinCGeometricMode
          period hPeriod mode := by
    apply (primitiveSpinCGeometricFullModeEquiv period hPeriod).injective
    simp
  rw [primitiveSpinCExtendedD10SquaredEigenvalue, hMode,
    programPD10ModeToPrimitiveSpinCGeometricMode_squaredEigenvalue]

/-- The maximal graph domain after separating the zero tower from D10. -/
abbrev PrimitiveSpinCExtendedD10H2 :=
  complexDiagonalDomain
    (PrimitiveSpinCExtendedD10Mode period hPeriod)
    (primitiveSpinCExtendedD10SquaredEigenvalue period hPeriod)

/-- The corresponding maximal diagonal operator. -/
abbrev primitiveSpinCExtendedD10UnboundedSquared :=
  complexDiagonalOperator
    (PrimitiveSpinCExtendedD10Mode period hPeriod)
    (primitiveSpinCExtendedD10SquaredEigenvalue period hPeriod)

/-- Ambient reindexing preserves maximal-domain membership exactly. -/
theorem primitiveSpinCGeometricExtendedD10L2Equiv_mem_h2_iff
    (state : PrimitiveSpinCGeometricL2) :
    primitiveSpinCGeometricExtendedD10L2Equiv period hPeriod state ∈
        PrimitiveSpinCExtendedD10H2 period hPeriod ↔
      state ∈ PrimitiveSpinCGeometricH2 period hPeriod := by
  constructor
  · rintro ⟨image, hImage⟩
    refine
      ⟨(primitiveSpinCGeometricExtendedD10L2Equiv
          period hPeriod).symm image, ?_⟩
    intro mode
    have hMode :=
      hImage (primitiveSpinCGeometricFullModeEquiv period hPeriod mode)
    change
      image (primitiveSpinCGeometricFullModeEquiv period hPeriod mode) =
        (primitiveSpinCGeometricSquaredEigenvalue
            period hPeriod mode : Complex) * state mode
    simpa [primitiveSpinCExtendedD10SquaredEigenvalue,
      primitiveSpinCGeometricExtendedD10L2Equiv,
      complexDiagonalHilbertCongr_apply] using hMode
  · rintro ⟨image, hImage⟩
    refine
      ⟨primitiveSpinCGeometricExtendedD10L2Equiv
          period hPeriod image, ?_⟩
    intro mode
    simpa [primitiveSpinCExtendedD10SquaredEigenvalue,
      primitiveSpinCGeometricExtendedD10L2Equiv,
      complexDiagonalHilbertCongr_apply] using
        hImage
          ((primitiveSpinCGeometricFullModeEquiv
            period hPeriod).symm mode)

/-- The maximal SpinC graph domain is unitarily the zero tower plus the
positive D10 domain. -/
def primitiveSpinCGeometricExtendedD10H2Equiv :
    PrimitiveSpinCGeometricH2 period hPeriod ≃ₗᵢ[Complex]
      PrimitiveSpinCExtendedD10H2 period hPeriod where
  toFun state :=
    ⟨primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod state.1,
      (primitiveSpinCGeometricExtendedD10L2Equiv_mem_h2_iff
        period hPeriod state.1).2 state.2⟩
  invFun state :=
    ⟨(primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod).symm state.1, by
      apply
        (primitiveSpinCGeometricExtendedD10L2Equiv_mem_h2_iff
          period hPeriod
          ((primitiveSpinCGeometricExtendedD10L2Equiv
            period hPeriod).symm state.1)).1
      simpa using state.2⟩
  left_inv state := by
    apply Subtype.ext
    exact
      (primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod).symm_apply_apply state.1
  right_inv state := by
    apply Subtype.ext
    exact
      (primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod).apply_symm_apply state.1
  map_add' first second := by
    apply Subtype.ext
    exact map_add
      (primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod) first.1 second.1
  map_smul' scalar state := by
    apply Subtype.ext
    exact map_smul
      (primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod) scalar state.1
  norm_map' state :=
    (primitiveSpinCGeometricExtendedD10L2Equiv
      period hPeriod).norm_map state.1

/-- Exact conjugacy of the two maximal unbounded realizations. -/
theorem primitiveSpinCGeometricExtendedD10H2Equiv_intertwines
    (state : PrimitiveSpinCGeometricH2 period hPeriod) :
    primitiveSpinCExtendedD10UnboundedSquared period hPeriod
        (primitiveSpinCGeometricExtendedD10H2Equiv
          period hPeriod state) =
      primitiveSpinCGeometricExtendedD10L2Equiv period hPeriod
        (primitiveSpinCGeometricUnboundedSquared
          period hPeriod state) := by
  ext mode
  rw [complexDiagonalOperator_apply]
  simp only [primitiveSpinCGeometricExtendedD10H2Equiv,
    primitiveSpinCGeometricExtendedD10L2Equiv,
    complexDiagonalHilbertCongr_apply]
  rw [complexDiagonalOperator_apply]
  rfl

/-- The reindexing preserves the full graph energy, not only the ambient
`L²` norm. -/
theorem primitiveSpinCGeometricExtendedD10_graphEnergy
    (state : PrimitiveSpinCGeometricH2 period hPeriod) :
    ‖(primitiveSpinCGeometricExtendedD10H2Equiv
        period hPeriod state :
      PrimitiveSpinCExtendedD10L2 period hPeriod)‖ ^ 2 +
        ‖primitiveSpinCExtendedD10UnboundedSquared period hPeriod
          (primitiveSpinCGeometricExtendedD10H2Equiv
            period hPeriod state)‖ ^ 2 =
      ‖(state : PrimitiveSpinCGeometricL2)‖ ^ 2 +
        ‖primitiveSpinCGeometricUnboundedSquared
          period hPeriod state‖ ^ 2 := by
  rw [show
      ‖(primitiveSpinCGeometricExtendedD10H2Equiv
          period hPeriod state :
        PrimitiveSpinCExtendedD10L2 period hPeriod)‖ =
        ‖(state : PrimitiveSpinCGeometricL2)‖ by
      exact
        (primitiveSpinCGeometricExtendedD10L2Equiv
          period hPeriod).norm_map state.1,
    primitiveSpinCGeometricExtendedD10H2Equiv_intertwines,
    (primitiveSpinCGeometricExtendedD10L2Equiv
      period hPeriod).norm_map]

/-- Concrete certificate for the coefficient-level common-domain closure. -/
structure ProgramPPrimitiveSpinCGeometricDomainUnitaryCertificate4D : Prop where
  zeroTowerWeight :
    ∀ choice circleMode,
      primitiveSpinCExtendedD10SquaredEigenvalue period hPeriod
          (Sum.inl (choice, circleMode)) =
        circleEigenvalue
          (PrimitiveSpinCSpectralData period hPeriod)
          choice circleMode ^ 2
  positiveD10Weight :
    ∀ mode,
      primitiveSpinCExtendedD10SquaredEigenvalue period hPeriod
          (Sum.inr mode) =
        productDiracEigenvalueSquared
          (PrimitiveSpinCSpectralData period hPeriod)
          mode.separatedMode
  operatorIntertwining :
    ∀ state,
      primitiveSpinCExtendedD10UnboundedSquared period hPeriod
          (primitiveSpinCGeometricExtendedD10H2Equiv
            period hPeriod state) =
        primitiveSpinCGeometricExtendedD10L2Equiv period hPeriod
          (primitiveSpinCGeometricUnboundedSquared
            period hPeriod state)
  graphEnergy :
    ∀ state,
      ‖(primitiveSpinCGeometricExtendedD10H2Equiv
          period hPeriod state :
        PrimitiveSpinCExtendedD10L2 period hPeriod)‖ ^ 2 +
          ‖primitiveSpinCExtendedD10UnboundedSquared period hPeriod
            (primitiveSpinCGeometricExtendedD10H2Equiv
              period hPeriod state)‖ ^ 2 =
        ‖(state : PrimitiveSpinCGeometricL2)‖ ^ 2 +
          ‖primitiveSpinCGeometricUnboundedSquared
            period hPeriod state‖ ^ 2

def programPPrimitiveSpinCGeometricDomainUnitaryCertificate4D :
    ProgramPPrimitiveSpinCGeometricDomainUnitaryCertificate4D
      period hPeriod where
  zeroTowerWeight :=
    primitiveSpinCExtendedD10SquaredEigenvalue_zero period hPeriod
  positiveD10Weight :=
    primitiveSpinCExtendedD10SquaredEigenvalue_positive period hPeriod
  operatorIntertwining :=
    primitiveSpinCGeometricExtendedD10H2Equiv_intertwines
      period hPeriod
  graphEnergy :=
    primitiveSpinCGeometricExtendedD10_graphEnergy period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCGeometricDomainUnitary4D
end JanusFormal
