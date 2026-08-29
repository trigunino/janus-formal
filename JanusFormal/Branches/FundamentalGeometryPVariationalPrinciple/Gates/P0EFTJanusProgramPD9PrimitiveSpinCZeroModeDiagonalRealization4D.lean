import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# Diagonal squared realization on the geometric zero-mode span

The explicit global smooth zero-mode synthesis is injective.  Therefore
the geometric squared eigenvalues can be transported, without a choice of
trivialization, to its finite real-linear range.

This is the genuine zero-sphere part of the geometric realization.  It
does not assert the still-missing positive monopole eigenspinor tower.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCZeroModeDiagonalRealization4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal InnerProductSpace lp
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The complete geometric squared eigenvalue attached to a zero-sphere
label. -/
def primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
    (label : PrimitiveSpinCGeometricZeroModeLabel) : Real :=
  primitiveSpinCGeometricSquaredEigenvalue period hPeriod
    (primitiveSpinCGeometricZeroMode label.1 label.2)

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue_eq
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
        period hPeriod label =
      circleEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod)
        label.1 label.2 ^ 2 := by
  exact primitiveSpinCGeometricZeroMode_squaredEigenvalue
    period hPeriod label.1 label.2

/-- The zero-sphere labels embed faithfully into the complete geometric
spectral labels. -/
def primitiveSpinCGeometricZeroModeEmbedding :
    PrimitiveSpinCGeometricZeroModeLabel ↪
      PrimitiveSpinCGeometricFullMode where
  toFun label :=
    primitiveSpinCGeometricZeroMode label.1 label.2
  inj' := by
    intro first second hEqual
    apply Prod.ext
    · exact congrArg
        (fun mode : PrimitiveSpinCGeometricFullMode => mode.1)
        hEqual
    · apply primitiveSpinCZeroSphereMode_injective
      exact congrArg
        (fun mode : PrimitiveSpinCGeometricFullMode => mode.2)
        hEqual

/-- One zero-mode coefficient inserted into the complete geometric
coefficient Hilbert space. -/
def primitiveSpinCGeometricFiniteZeroModeL2Block
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Complex] PrimitiveSpinCGeometricL2 :=
  (lp.singleContinuousLinearMap Complex
    (fun _ : PrimitiveSpinCGeometricFullMode => Complex) 2
    (primitiveSpinCGeometricZeroModeEmbedding label)).toLinearMap

/-- Canonical inclusion of a finite geometric zero-mode packet into the
complete coefficient Hilbert space. -/
def primitiveSpinCGeometricFiniteZeroModeL2Synthesis :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricL2 :=
  Finsupp.lsum Complex
    primitiveSpinCGeometricFiniteZeroModeL2Block

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeL2Synthesis_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeL2Synthesis
        (Finsupp.single label coefficient) =
      lp.single 2
        (primitiveSpinCGeometricZeroMode label.1 label.2)
        coefficient := by
  rw [primitiveSpinCGeometricFiniteZeroModeL2Synthesis,
    Finsupp.lsum_single]
  rfl

/-- Read one zero-mode coordinate from the complete coefficient Hilbert
space. -/
def primitiveSpinCGeometricZeroModeL2Coordinate
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    PrimitiveSpinCGeometricL2 →ₗ[Complex] Complex :=
  (lp.evalCLM Complex
    (fun _ : PrimitiveSpinCGeometricFullMode => Complex) 2
    (primitiveSpinCGeometricZeroModeEmbedding label)).toLinearMap

theorem primitiveSpinCGeometricZeroModeL2Coordinate_comp_synthesis
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    (primitiveSpinCGeometricZeroModeL2Coordinate label).comp
        primitiveSpinCGeometricFiniteZeroModeL2Synthesis =
      Finsupp.lapply label := by
  apply Finsupp.lhom_ext
  intro source coefficient
  rw [LinearMap.comp_apply,
    primitiveSpinCGeometricFiniteZeroModeL2Synthesis_single,
    Finsupp.lapply_apply]
  change
    (lp.single 2
          (primitiveSpinCGeometricZeroModeEmbedding source)
          coefficient :
        PrimitiveSpinCGeometricL2)
        (primitiveSpinCGeometricZeroModeEmbedding label) =
      Finsupp.single source coefficient label
  by_cases hLabel : source = label
  · subst source
    rw [lp.single_apply_self, Finsupp.single_eq_same]
  · rw [lp.single_apply_ne 2 _ _
        ((primitiveSpinCGeometricZeroModeEmbedding.injective.ne
          hLabel).symm),
      Finsupp.single_eq_of_ne (Ne.symm hLabel)]

@[simp]
theorem primitiveSpinCGeometricZeroModeL2Coordinate_synthesis
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCGeometricZeroModeL2Coordinate label
        (primitiveSpinCGeometricFiniteZeroModeL2Synthesis coefficients) =
      coefficients label := by
  exact LinearMap.congr_fun
    (primitiveSpinCGeometricZeroModeL2Coordinate_comp_synthesis label)
    coefficients

theorem primitiveSpinCGeometricFiniteZeroModeL2Synthesis_injective :
    Function.Injective
      primitiveSpinCGeometricFiniteZeroModeL2Synthesis := by
  intro first second hEqual
  apply Finsupp.ext
  intro label
  have hCoordinate := congrArg
    (primitiveSpinCGeometricZeroModeL2Coordinate label) hEqual
  simpa only [
    primitiveSpinCGeometricZeroModeL2Coordinate_synthesis]
    using hCoordinate

/-- Hilbert completion of the two normal-root zero-sphere towers alone. -/
abbrev PrimitiveSpinCGeometricZeroModeL2 :=
  ComplexDiagonalHilbert PrimitiveSpinCGeometricZeroModeLabel

/-- One finite coefficient inserted into the zero-tower Hilbert
completion. -/
def primitiveSpinCGeometricFiniteZeroModeCompletionBlock
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Complex] PrimitiveSpinCGeometricZeroModeL2 :=
  (lp.singleContinuousLinearMap Complex
    (fun _ : PrimitiveSpinCGeometricZeroModeLabel => Complex) 2
    label).toLinearMap

/-- Canonical finite-support core of the completed zero-mode Hilbert
space. -/
def primitiveSpinCGeometricFiniteZeroModeCompletion :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricZeroModeL2 :=
  Finsupp.lsum Complex
    primitiveSpinCGeometricFiniteZeroModeCompletionBlock

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeCompletion_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeCompletion
        (Finsupp.single label coefficient) =
      lp.single 2 label coefficient := by
  rw [primitiveSpinCGeometricFiniteZeroModeCompletion,
    Finsupp.lsum_single]
  rfl

/-- Finite zero-mode packets are dense in their natural Hilbert
completion. -/
theorem primitiveSpinCGeometricFiniteZeroModeCompletion_denseRange :
    DenseRange primitiveSpinCGeometricFiniteZeroModeCompletion := by
  change Dense
    (Set.range primitiveSpinCGeometricFiniteZeroModeCompletion)
  rw [← LinearMap.coe_range,
    Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex PrimitiveSpinCGeometricZeroModeL2) =
        (Submodule.span Complex
          (Set.range
            (complexDiagonalBasis
              PrimitiveSpinCGeometricZeroModeLabel))).topologicalClosure :=
      (HilbertBasis.dense_span
        (complexDiagonalBasis
          PrimitiveSpinCGeometricZeroModeLabel)).symm
    _ ≤
        (LinearMap.range
          primitiveSpinCGeometricFiniteZeroModeCompletion).topologicalClosure :=
      Submodule.topologicalClosure_mono
        (Submodule.span_le.mpr (by
          rintro state ⟨label, rfl⟩
          refine ⟨Finsupp.single label 1, ?_⟩
          rw [primitiveSpinCGeometricFiniteZeroModeCompletion_single]
          exact
            (complexDiagonalBasis_eq_single
              PrimitiveSpinCGeometricZeroModeLabel label).symm))

/-- Every completed zero-mode state is the norm-convergent sum of its
canonical mode coordinates. -/
theorem primitiveSpinCGeometricZeroModeL2_hasSum
    (state : PrimitiveSpinCGeometricZeroModeL2) :
    HasSum
      (fun label : PrimitiveSpinCGeometricZeroModeLabel =>
        lp.single 2 label (state label))
      state :=
  lp.hasSum_single ENNReal.ofNat_ne_top state

/-- Infinite Parseval identity for the completed zero-mode tower. -/
theorem primitiveSpinCGeometricZeroModeL2_parseval
    (state : PrimitiveSpinCGeometricZeroModeL2) :
    ⟪state, state⟫_Complex =
      ∑' label : PrimitiveSpinCGeometricZeroModeLabel,
        ⟪state label, state label⟫_Complex :=
  lp.inner_eq_tsum state state

/-- Complex-linear form of the diagonal coefficient block, used to enter
the complete coefficient Hilbert realization. -/
def primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientBlockComplex
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Complex]
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  (Finsupp.lsingle label).comp
    (((primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
        period hPeriod label : Real) : Complex) •
      (LinearMap.id : Complex →ₗ[Complex] Complex))

/-- Complex-linear diagonal squared operator on finite zero-mode
coefficients. -/
def primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  Finsupp.lsum Complex fun label =>
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientBlockComplex
      period hPeriod label

@[simp]
theorem
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex
        period hPeriod (Finsupp.single label coefficient) =
      (primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label : Complex) •
        Finsupp.single label coefficient := by
  simp [
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex,
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientBlockComplex]

/-- One diagonal coefficient block. -/
def primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientBlock
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Real] PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  (Finsupp.lsingle label).comp
    ((primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
        period hPeriod label) •
      (LinearMap.id : Complex →ₗ[Real] Complex))

/-- Diagonal squared operator on finite zero-mode coefficients. -/
def primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Real]
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients :=
  Finsupp.lsum Real fun label =>
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientBlock
      period hPeriod label

@[simp]
theorem
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator
        period hPeriod (Finsupp.single label coefficient) =
      primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label •
        Finsupp.single label coefficient := by
  simp [primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator,
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientBlock]

/-- The real-linear smooth-section diagonal and the complex-linear
Hilbert diagonal have the same underlying coefficient action. -/
theorem primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperators_agree
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator
        period hPeriod coefficients =
      primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex
        period hPeriod coefficients := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add label coefficient rest hCoefficient hLabel ih =>
      rw [map_add, map_add,
        primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator_single,
        primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex_single,
        ih]
      congr 1

/-- A coordinate basis vector equipped with its canonical membership in
the maximal graph domain. -/
def primitiveSpinCGeometricFiniteZeroModeH2Basis
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  ⟨complexDiagonalBasis PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricZeroModeEmbedding label),
    complexDiagonalBasis_mem_domain
      PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
      (primitiveSpinCGeometricZeroModeEmbedding label)⟩

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeH2Basis_coe
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    ((primitiveSpinCGeometricFiniteZeroModeH2Basis
          period hPeriod label :
        (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain) :
      PrimitiveSpinCGeometricL2) =
      lp.single 2
        (primitiveSpinCGeometricZeroModeEmbedding label)
        (1 : Complex) :=
  complexDiagonalBasis_eq_single
    PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricZeroModeEmbedding label)

/-- One finite zero-mode coefficient inserted into the maximal graph
domain. -/
def primitiveSpinCGeometricFiniteZeroModeH2Block
    (label : PrimitiveSpinCGeometricZeroModeLabel) :
    Complex →ₗ[Complex]
      (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  LinearMap.toSpanSingleton Complex
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain
    (primitiveSpinCGeometricFiniteZeroModeH2Basis
      period hPeriod label)

/-- Every finite zero-mode packet lies canonically in the maximal graph
domain. -/
def primitiveSpinCGeometricFiniteZeroModeH2Synthesis :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Complex]
      (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  Finsupp.lsum Complex fun label =>
    primitiveSpinCGeometricFiniteZeroModeH2Block
      period hPeriod label

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeH2Synthesis_single
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeH2Synthesis
        period hPeriod (Finsupp.single label coefficient) =
      coefficient •
        primitiveSpinCGeometricFiniteZeroModeH2Basis
          period hPeriod label := by
  rw [primitiveSpinCGeometricFiniteZeroModeH2Synthesis,
    Finsupp.lsum_single]
  simp [primitiveSpinCGeometricFiniteZeroModeH2Block]

theorem primitiveSpinCGeometricFiniteZeroModeH2Synthesis_coe
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    ((primitiveSpinCGeometricFiniteZeroModeH2Synthesis
          period hPeriod coefficients :
        (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain) :
      PrimitiveSpinCGeometricL2) =
      primitiveSpinCGeometricFiniteZeroModeL2Synthesis
        coefficients := by
  let inclusion :
      (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain →ₗ[Complex]
        PrimitiveSpinCGeometricL2 :=
    (primitiveSpinCGeometricUnboundedSquared
      period hPeriod).domain.subtype
  have hMaps :
      inclusion.comp
          (primitiveSpinCGeometricFiniteZeroModeH2Synthesis
            period hPeriod) =
        primitiveSpinCGeometricFiniteZeroModeL2Synthesis := by
    apply Finsupp.lhom_ext
    intro label coefficient
    rw [LinearMap.comp_apply,
      primitiveSpinCGeometricFiniteZeroModeH2Synthesis_single,
      primitiveSpinCGeometricFiniteZeroModeL2Synthesis_single]
    change coefficient •
        (complexDiagonalBasis PrimitiveSpinCGeometricFullMode
          (primitiveSpinCGeometricZeroModeEmbedding label)) =
      lp.single 2
        (primitiveSpinCGeometricZeroModeEmbedding label) coefficient
    rw [complexDiagonalBasis_eq_single]
    simp only [← lp.single_smul, smul_eq_mul, mul_one]
  exact LinearMap.congr_fun hMaps coefficients

/-- Restriction of the complete maximal diagonal operator to the finite
geometric zero-mode coefficients. -/
def primitiveSpinCGeometricFiniteZeroModeUnboundedSquared :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricL2 :=
  (primitiveSpinCGeometricUnboundedSquared
      period hPeriod).toFun.comp
    (primitiveSpinCGeometricFiniteZeroModeH2Synthesis
      period hPeriod)

/-- The complete maximal squared operator and the explicit finite
zero-mode diagonalization commute exactly. -/
theorem
    primitiveSpinCGeometricFiniteZeroModeUnboundedSquared_intertwines
    (coefficients :
      PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCGeometricFiniteZeroModeUnboundedSquared
        period hPeriod coefficients =
      primitiveSpinCGeometricFiniteZeroModeL2Synthesis
        (primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex
          period hPeriod coefficients) := by
  have hMaps :
      primitiveSpinCGeometricFiniteZeroModeUnboundedSquared
          period hPeriod =
        primitiveSpinCGeometricFiniteZeroModeL2Synthesis.comp
          (primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex
            period hPeriod) := by
    apply Finsupp.lhom_ext
    intro label coefficient
    rw [primitiveSpinCGeometricFiniteZeroModeUnboundedSquared,
      LinearMap.comp_apply,
      primitiveSpinCGeometricFiniteZeroModeH2Synthesis_single,
      map_smul,
      LinearMap.comp_apply,
      primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex_single,
      map_smul,
      primitiveSpinCGeometricFiniteZeroModeL2Synthesis_single]
    change coefficient •
        complexDiagonalOperator PrimitiveSpinCGeometricFullMode
          (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
          ⟨complexDiagonalBasis PrimitiveSpinCGeometricFullMode
              (primitiveSpinCGeometricZeroModeEmbedding label),
            complexDiagonalBasis_mem_domain
              PrimitiveSpinCGeometricFullMode
              (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
              (primitiveSpinCGeometricZeroModeEmbedding label)⟩ =
      (primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label : Complex) •
        lp.single 2
          (primitiveSpinCGeometricZeroModeEmbedding label)
          coefficient
    rw [complexDiagonalOperator_on_basis]
    change coefficient •
        ((primitiveSpinCGeometricSquaredEigenvalue period hPeriod
            (primitiveSpinCGeometricZeroModeEmbedding label) : Real) :
          Complex) •
          complexDiagonalBasis PrimitiveSpinCGeometricFullMode
            (primitiveSpinCGeometricZeroModeEmbedding label) =
      (primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label : Complex) •
        lp.single 2
          (primitiveSpinCGeometricZeroModeEmbedding label)
          coefficient
    rw [complexDiagonalBasis_eq_single]
    simp only [← lp.single_smul, smul_eq_mul, mul_one]
    congr 1
    change coefficient *
        (primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label : Complex) =
      (primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label : Complex) * coefficient
    ring
  exact LinearMap.congr_fun hMaps coefficients

/-- Finite real-linear span of the genuine global smooth zero-mode
sections. -/
abbrev PrimitiveSpinCGeometricFiniteZeroModeSpan :=
  LinearMap.range
    (primitiveSpinCGeometricFiniteZeroModeSynthesis period hPeriod)

/-- The injective global synthesis, viewed as coordinates on its range. -/
def primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv :
    PrimitiveSpinCGeometricFiniteZeroModeCoefficients ≃ₗ[Real]
      PrimitiveSpinCGeometricFiniteZeroModeSpan period hPeriod :=
  LinearEquiv.ofInjective
    (primitiveSpinCGeometricFiniteZeroModeSynthesis period hPeriod)
    (primitiveSpinCGeometricFiniteZeroModeSynthesis_injective
      period hPeriod)

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv_coe
    (coefficients : PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    ((primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv
          period hPeriod coefficients :
        PrimitiveSpinCGeometricFiniteZeroModeSpan period hPeriod) :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
      primitiveSpinCGeometricFiniteZeroModeSynthesis
        period hPeriod coefficients :=
  rfl

/-- The squared operator transported to the finite global smooth
zero-mode span. -/
def primitiveSpinCGeometricFiniteZeroModeSquaredOperator :
    PrimitiveSpinCGeometricFiniteZeroModeSpan period hPeriod →ₗ[Real]
      PrimitiveSpinCGeometricFiniteZeroModeSpan period hPeriod :=
  (primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv
      period hPeriod).toLinearMap.comp
    ((primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator
        period hPeriod).comp
      (primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv
        period hPeriod).symm.toLinearMap)

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeSquaredOperator_synthesis
    (coefficients : PrimitiveSpinCGeometricFiniteZeroModeCoefficients) :
    primitiveSpinCGeometricFiniteZeroModeSquaredOperator
        period hPeriod
        (primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv
          period hPeriod coefficients) =
      primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv
        period hPeriod
        (primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator
          period hPeriod coefficients) := by
  simp [primitiveSpinCGeometricFiniteZeroModeSquaredOperator]

/-- A single global geometric zero-mode vector in the finite span. -/
def primitiveSpinCGeometricFiniteZeroModeVector
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    PrimitiveSpinCGeometricFiniteZeroModeSpan period hPeriod :=
  primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv
    period hPeriod (Finsupp.single label coefficient)

@[simp]
theorem primitiveSpinCGeometricFiniteZeroModeVector_coe
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    ((primitiveSpinCGeometricFiniteZeroModeVector
          period hPeriod label coefficient :
        PrimitiveSpinCGeometricFiniteZeroModeSpan period hPeriod) :
      D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter) =
      primitiveSpinCGeometricZeroModeCoefficientLinearMap
        period hPeriod label coefficient := by
  rw [primitiveSpinCGeometricFiniteZeroModeVector,
    primitiveSpinCGeometricFiniteZeroModeSynthesisEquiv_coe,
    primitiveSpinCGeometricFiniteZeroModeSynthesis_single]

/-- Every explicit global zero-mode vector satisfies its exact squared
eigen-equation on the transported geometric operator. -/
theorem primitiveSpinCGeometricFiniteZeroModeVector_squaredEigen
    (label : PrimitiveSpinCGeometricZeroModeLabel)
    (coefficient : Complex) :
    primitiveSpinCGeometricFiniteZeroModeSquaredOperator
        period hPeriod
        (primitiveSpinCGeometricFiniteZeroModeVector
          period hPeriod label coefficient) =
      primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
          period hPeriod label •
        primitiveSpinCGeometricFiniteZeroModeVector
          period hPeriod label coefficient := by
  rw [primitiveSpinCGeometricFiniteZeroModeVector,
    primitiveSpinCGeometricFiniteZeroModeSquaredOperator_synthesis,
    primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperator_single,
    map_smul]

/-- Consolidated closure certificate for the complete zero-sphere tower:
global smooth independence, Hilbert completeness, maximal-domain inclusion,
diagonal intertwining and exact squared eigen-equations. -/
theorem primitiveSpinCGeometricZeroModeRealization_closed :
    Function.Injective
        (primitiveSpinCGeometricFiniteZeroModeSynthesis
          period hPeriod) ∧
      Function.Injective
        primitiveSpinCGeometricFiniteZeroModeL2Synthesis ∧
      DenseRange
        primitiveSpinCGeometricFiniteZeroModeCompletion ∧
      (∀ coefficients :
          PrimitiveSpinCGeometricFiniteZeroModeCoefficients,
        ((primitiveSpinCGeometricFiniteZeroModeH2Synthesis
              period hPeriod coefficients :
            (primitiveSpinCGeometricUnboundedSquared
              period hPeriod).domain) :
          PrimitiveSpinCGeometricL2) =
          primitiveSpinCGeometricFiniteZeroModeL2Synthesis
            coefficients) ∧
      (∀ coefficients :
          PrimitiveSpinCGeometricFiniteZeroModeCoefficients,
        primitiveSpinCGeometricFiniteZeroModeUnboundedSquared
            period hPeriod coefficients =
          primitiveSpinCGeometricFiniteZeroModeL2Synthesis
            (primitiveSpinCGeometricFiniteZeroModeSquaredCoefficientOperatorComplex
              period hPeriod coefficients)) ∧
      (∀ label : PrimitiveSpinCGeometricZeroModeLabel,
        ∀ coefficient : Complex,
          primitiveSpinCGeometricFiniteZeroModeSquaredOperator
              period hPeriod
              (primitiveSpinCGeometricFiniteZeroModeVector
                period hPeriod label coefficient) =
            primitiveSpinCGeometricFiniteZeroModeSquaredEigenvalue
                period hPeriod label •
              primitiveSpinCGeometricFiniteZeroModeVector
                period hPeriod label coefficient) :=
  ⟨primitiveSpinCGeometricFiniteZeroModeSynthesis_injective
      period hPeriod,
    primitiveSpinCGeometricFiniteZeroModeL2Synthesis_injective,
    primitiveSpinCGeometricFiniteZeroModeCompletion_denseRange,
    primitiveSpinCGeometricFiniteZeroModeH2Synthesis_coe
      period hPeriod,
    primitiveSpinCGeometricFiniteZeroModeUnboundedSquared_intertwines
      period hPeriod,
    primitiveSpinCGeometricFiniteZeroModeVector_squaredEigen
      period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCZeroModeDiagonalRealization4D
end JanusFormal
