import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalRealFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# Global spectral Hessian Fredholm block

The D9 gauge--ghost multiplier, both physical SpinC coefficient towers and
the multiplicity-aware D10 tower are assembled on one maximal diagonal
domain.  The differential symbols may grow without bound.  A finite D9
characteristic set and the already proved SpinC/D10 positive gaps imply that
the combined graph-norm operator is Fredholm.

The SpinC entry in this legacy assembly is the nonnegative squared operator
`D²`.  It is retained as elliptic control.  The first-order physical
Dirac-plus-mass Hessian used by the terminal realization is constructed in
`P0EFTJanusProgramPGlobalPhysicalSpectralHessianFredholm4D`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalSpectralHessianFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

/-- One mode type for the complete coefficient-level spectral Hessian. -/
abbrev ProgramPGlobalSpectralHessianMode
    (ι : Type*) (data : ProductThroatSpectralData) :=
  (ι × Fin 8) ⊕
    ((Sector × PrimitiveSpinCGeometricFullMode) ⊕
      ProgramPD10Mode4D data)

local instance programPGlobalSpectralHessianModeDecidableEq
    (ι : Type*) [DecidableEq ι] (data : ProductThroatSpectralData) :
    DecidableEq (ProgramPGlobalSpectralHessianMode ι data) :=
  Classical.decEq _

/-- Exact diagonal weight of the combined D9/SpinC/D10 block. -/
def programPGlobalSpectralHessianWeight
    {ι : Type*} (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (mode : ProgramPGlobalSpectralHessianMode ι data) : Real :=
  match mode with
  | .inl index => d9GaugeGhostUnboundedWeight covector index
  | .inr (.inl spinCMode) =>
      primitiveSpinCGeometricSquaredEigenvalue
        period hPeriod spinCMode.2
  | .inr (.inr d10Mode) =>
      productDiracEigenvalueSquared data d10Mode.separatedMode

@[simp]
theorem programPGlobalSpectralHessianWeight_d9
    {ι : Type*} (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) (index : ι × Fin 8) :
    programPGlobalSpectralHessianWeight
        period hPeriod covector data (.inl index) =
      d9GaugeGhostUnboundedWeight covector index :=
  rfl

@[simp]
theorem programPGlobalSpectralHessianWeight_spinC
    {ι : Type*} (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (sector : Sector) (mode : PrimitiveSpinCGeometricFullMode) :
    programPGlobalSpectralHessianWeight
        period hPeriod covector data (.inr (.inl (sector, mode))) =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode :=
  rfl

@[simp]
theorem programPGlobalSpectralHessianWeight_d10
    {ι : Type*} (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData)
    (mode : ProgramPD10Mode4D data) :
    programPGlobalSpectralHessianWeight
        period hPeriod covector data (.inr (.inr mode)) =
      productDiracEigenvalueSquared data mode.separatedMode :=
  rfl

/-- The only possible zero modes of the combined block are D9
characteristic modes. -/
def programPGlobalSpectralZeroModeEquiv
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    ComplexDiagonalZeroMode
        (ProgramPGlobalSpectralHessianMode ι data)
        (programPGlobalSpectralHessianWeight
          period hPeriod covector data) ≃
      ComplexDiagonalZeroMode (ι × Fin 8)
        (d9GaugeGhostUnboundedWeight covector) where
  toFun mode := by
    rcases mode with ⟨mode, hZero⟩
    rcases mode with index | mode
    · exact ⟨index, hZero⟩
    · rcases mode with spinCMode | d10Mode
      · exfalso
        have hPositive :
            0 <
              primitiveSpinCGeometricSquaredEigenvalue
                period hPeriod spinCMode.2 :=
          (primitiveSpinCGeometricSpectralGap_pos period hPeriod).trans_le
            (primitiveSpinCGeometricSpectralGap_le
              period hPeriod spinCMode.2)
        exact (ne_of_gt hPositive) hZero
      · exfalso
        have hPositive :
            0 <
              productDiracEigenvalueSquared
                data d10Mode.separatedMode :=
          (programPD10SpectralGap4D_pos data).trans_le
            (programPD10SpectralGap4D_le data d10Mode)
        exact (ne_of_gt hPositive) hZero
  invFun mode :=
    ⟨Sum.inl mode.1, mode.2⟩
  left_inv mode := by
    rcases mode with ⟨mode, hZero⟩
    rcases mode with index | mode
    · rfl
    · rcases mode with spinCMode | d10Mode
      · exfalso
        have hPositive :
            0 <
              primitiveSpinCGeometricSquaredEigenvalue
                period hPeriod spinCMode.2 :=
          (primitiveSpinCGeometricSpectralGap_pos period hPeriod).trans_le
            (primitiveSpinCGeometricSpectralGap_le
              period hPeriod spinCMode.2)
        exact (ne_of_gt hPositive) hZero
      · exfalso
        have hPositive :
            0 <
              productDiracEigenvalueSquared
                data d10Mode.separatedMode :=
          (programPD10SpectralGap4D_pos data).trans_le
            (programPD10SpectralGap4D_le data d10Mode)
        exact (ne_of_gt hPositive) hZero
  right_inv mode := by
    rfl

/-- Common positive lower gap away from the finite D9 characteristic set. -/
def programPGlobalSpectralHessianGap
    {ι : Type*} {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) : Real :=
  min d9Ellipticity.gap
    (min (primitiveSpinCGeometricSpectralGap period)
      (programPD10SpectralGap4D data))

theorem programPGlobalSpectralHessianGap_pos
    (hPeriod : period ≠ 0)
    {ι : Type*} {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    0 <
      programPGlobalSpectralHessianGap
        period d9Ellipticity data := by
  exact lt_min d9Ellipticity.gap_pos
    (lt_min
      (primitiveSpinCGeometricSpectralGap_pos period hPeriod)
      (programPD10SpectralGap4D_pos data))

/-- Ellipticity modulo the exact finite combined zero-mode space. -/
def programPGlobalSpectralHessianFiniteZeroGap
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    ComplexDiagonalFiniteZeroGap
      (ProgramPGlobalSpectralHessianMode ι data)
      (programPGlobalSpectralHessianWeight
        period hPeriod covector data) where
  gap :=
    programPGlobalSpectralHessianGap
      period d9Ellipticity data
  gap_pos :=
    programPGlobalSpectralHessianGap_pos
      period hPeriod d9Ellipticity data
  gap_le := by
    intro mode hNonzero
    rcases mode with index | mode
    · exact
        (min_le_left _ _).trans
          (d9Ellipticity.gap_le index.1 hNonzero)
    · rcases mode with spinCMode | d10Mode
      · change
          programPGlobalSpectralHessianGap
              period d9Ellipticity data ≤
            |primitiveSpinCGeometricSquaredEigenvalue
              period hPeriod spinCMode.2|
        rw [abs_of_nonneg
          (primitiveSpinCGeometricSquaredEigenvalue_nonnegative
            period hPeriod spinCMode.2)]
        exact
          (min_le_right _ _).trans
            ((min_le_left _ _).trans
              (primitiveSpinCGeometricSpectralGap_le
                period hPeriod spinCMode.2))
      · change
          programPGlobalSpectralHessianGap
              period d9Ellipticity data ≤
            |productDiracEigenvalueSquared
              data d10Mode.separatedMode|
        rw [abs_of_pos
          ((programPD10SpectralGap4D_pos data).trans_le
            (programPD10SpectralGap4D_le data d10Mode))]
        exact
          (min_le_right _ _).trans
            ((min_le_right _ _).trans
              (programPD10SpectralGap4D_le data d10Mode))
  zeroModeFinite := by
    letI : Finite
        {index : ι × Fin 8 //
          d9GaugeGhostUnboundedWeight covector index = 0} :=
      d9Ellipticity.characteristicFinite
    exact Finite.of_equiv _
      (programPGlobalSpectralZeroModeEquiv
        period hPeriod covector data).symm

/-- Ambient Hilbert space of the combined spectral Hessian. -/
abbrev ProgramPGlobalSpectralHessianHilbert
    (ι : Type*) (data : ProductThroatSpectralData) :=
  ComplexDiagonalHilbert (ProgramPGlobalSpectralHessianMode ι data)

local instance programPGlobalSpectralHessianHilbertRealInnerProductSpace
    (ι : Type*) (data : ProductThroatSpectralData) :
    InnerProductSpace Real
      (ProgramPGlobalSpectralHessianHilbert ι data) :=
  InnerProductSpace.complexToReal

local instance programPGlobalSpectralHessianHilbertRealLinearPMapStar
    (ι : Type*) (data : ProductThroatSpectralData) :
    Star (ProgramPGlobalSpectralHessianHilbert ι data →ₗ.[Real]
      ProgramPGlobalSpectralHessianHilbert ι data) :=
  LinearPMap.instStar

/-- Maximal domain of the combined unbounded spectral Hessian. -/
abbrev ProgramPGlobalSpectralHessianMaximalDomain
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :=
  complexDiagonalDomain
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- Complete unbounded D9/SpinC/D10 spectral Hessian. -/
abbrev programPGlobalSpectralHessianMaximalOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :=
  complexDiagonalOperator
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- The combined maximal domain regarded as a real submodule, matching the
real variational Hessian. -/
abbrev ProgramPGlobalSpectralHessianRealMaximalDomain
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :=
  ComplexDiagonalRealDomain
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- Underlying real realization of the complete unbounded spectral Hessian. -/
abbrev programPGlobalSpectralHessianRealMaximalOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :=
  complexDiagonalRealOperator
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

theorem programPGlobalSpectralHessianMaximalDomain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    Dense
      (ProgramPGlobalSpectralHessianMaximalDomain
        period hPeriod covector data :
        Set (ProgramPGlobalSpectralHessianHilbert ι data)) :=
  complexDiagonalDomain_dense
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

theorem programPGlobalSpectralHessianMaximalOperator_selfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    IsSelfAdjoint
      (programPGlobalSpectralHessianMaximalOperator
        period hPeriod covector data) :=
  complexDiagonalOperator_isSelfAdjoint
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

theorem programPGlobalSpectralHessianMaximalOperator_closed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    (programPGlobalSpectralHessianMaximalOperator
      period hPeriod covector data).IsClosed :=
  complexDiagonalOperator_isClosed
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- Closed graph domain of the combined unbounded spectral Hessian. -/
abbrev ProgramPGlobalSpectralHessianGraphDomain
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :=
  ComplexDiagonalGraphDomain
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- Bounded graph-norm realization of the complete spectral block. -/
abbrev programPGlobalSpectralHessianGraphOperator
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :=
  complexDiagonalGraphOperatorCLM
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- The assembled D9/SpinC/D10 graph operator is genuinely Fredholm. -/
theorem programPGlobalSpectralHessianGraphOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    IsClosed
        (LinearMap.range
          (programPGlobalSpectralHessianGraphOperator
            period hPeriod covector data).toLinearMap :
          Set (ProgramPGlobalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (programPGlobalSpectralHessianGraphOperator
            period hPeriod covector data).toLinearMap) ∧
      FiniteDimensional Complex
        (ProgramPGlobalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalSpectralHessianGraphOperator
              period hPeriod covector data).toLinearMap) :=
  complexDiagonalGraphOperator_fredholm
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)
    (programPGlobalSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity data)

/-- The same Fredholm conclusion holds directly for the densely defined
maximal spectral Hessian, not only for its bounded graph realization. -/
theorem programPGlobalSpectralHessianMaximalOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    IsClosed
        (LinearMap.range
          (programPGlobalSpectralHessianMaximalOperator
            period hPeriod covector data).toFun :
          Set (ProgramPGlobalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (programPGlobalSpectralHessianMaximalOperator
            period hPeriod covector data).toFun) ∧
      FiniteDimensional Complex
        (ProgramPGlobalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalSpectralHessianMaximalOperator
              period hPeriod covector data).toFun) :=
  complexDiagonalOperator_fredholm_of_finiteZeroGap
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)
    (programPGlobalSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity data)

/-- The real maximal domain is dense in the underlying real Hilbert space. -/
theorem programPGlobalSpectralHessianRealMaximalDomain_dense
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    Dense
      (ProgramPGlobalSpectralHessianRealMaximalDomain
        period hPeriod covector data :
        Set (ProgramPGlobalSpectralHessianHilbert ι data)) :=
  complexDiagonalRealDomain_dense
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- The coefficient Hessian is self-adjoint as a real unbounded operator. -/
theorem programPGlobalSpectralHessianRealMaximalOperator_selfAdjoint
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    IsSelfAdjoint
      (programPGlobalSpectralHessianRealMaximalOperator
        period hPeriod covector data) :=
  complexDiagonalRealOperator_isSelfAdjoint
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- The real maximal coefficient Hessian is closed. -/
theorem programPGlobalSpectralHessianRealMaximalOperator_closed
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (data : ProductThroatSpectralData) :
    (programPGlobalSpectralHessianRealMaximalOperator
      period hPeriod covector data).IsClosed :=
  complexDiagonalRealOperator_isClosed
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)

/-- Real Fredholm theorem for the assembled D9/SpinC/D10 maximal operator. -/
theorem programPGlobalSpectralHessianRealMaximalOperator_fredholm
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    IsClosed
        (LinearMap.range
          (programPGlobalSpectralHessianRealMaximalOperator
            period hPeriod covector data).toFun :
          Set (ProgramPGlobalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalSpectralHessianRealMaximalOperator
            period hPeriod covector data).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalSpectralHessianRealMaximalOperator
              period hPeriod covector data).toFun) :=
  complexDiagonalRealOperator_fredholm_of_finiteZeroGap
    (ProgramPGlobalSpectralHessianMode ι data)
    (programPGlobalSpectralHessianWeight
      period hPeriod covector data)
    (programPGlobalSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity data)

/-- Consolidated real Fredholm certificate matching the scalar field of the
physical variational chart. -/
structure ProgramPGlobalSpectralHessianRealFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) : Prop where
  domainDense :
    Dense
      (ProgramPGlobalSpectralHessianRealMaximalDomain
        period hPeriod covector data :
        Set (ProgramPGlobalSpectralHessianHilbert ι data))
  selfAdjoint :
    IsSelfAdjoint
      (programPGlobalSpectralHessianRealMaximalOperator
        period hPeriod covector data)
  closed :
    (programPGlobalSpectralHessianRealMaximalOperator
      period hPeriod covector data).IsClosed
  maximalFredholm :
    IsClosed
        (LinearMap.range
          (programPGlobalSpectralHessianRealMaximalOperator
            period hPeriod covector data).toFun :
          Set (ProgramPGlobalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPGlobalSpectralHessianRealMaximalOperator
            period hPeriod covector data).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalSpectralHessianRealMaximalOperator
              period hPeriod covector data).toFun)

def programPGlobalSpectralHessianRealFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    ProgramPGlobalSpectralHessianRealFredholmCertificate4D
      period hPeriod d9Ellipticity data where
  domainDense :=
    programPGlobalSpectralHessianRealMaximalDomain_dense
      period hPeriod covector data
  selfAdjoint :=
    programPGlobalSpectralHessianRealMaximalOperator_selfAdjoint
      period hPeriod covector data
  closed :=
    programPGlobalSpectralHessianRealMaximalOperator_closed
      period hPeriod covector data
  maximalFredholm :=
    programPGlobalSpectralHessianRealMaximalOperator_fredholm
      period hPeriod d9Ellipticity data

/-- Consolidated theorem carrying the genuine maximal and graph-norm
realizations of the assembled spectral block. -/
structure ProgramPGlobalSpectralHessianFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) : Prop where
  domainDense :
    Dense
      (ProgramPGlobalSpectralHessianMaximalDomain
        period hPeriod covector data :
        Set (ProgramPGlobalSpectralHessianHilbert ι data))
  selfAdjoint :
    IsSelfAdjoint
      (programPGlobalSpectralHessianMaximalOperator
        period hPeriod covector data)
  closed :
    (programPGlobalSpectralHessianMaximalOperator
      period hPeriod covector data).IsClosed
  maximalFredholm :
    IsClosed
        (LinearMap.range
          (programPGlobalSpectralHessianMaximalOperator
            period hPeriod covector data).toFun :
          Set (ProgramPGlobalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (programPGlobalSpectralHessianMaximalOperator
            period hPeriod covector data).toFun) ∧
      FiniteDimensional Complex
        (ProgramPGlobalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalSpectralHessianMaximalOperator
              period hPeriod covector data).toFun)
  graphFredholm :
    IsClosed
        (LinearMap.range
          (programPGlobalSpectralHessianGraphOperator
            period hPeriod covector data).toLinearMap :
          Set (ProgramPGlobalSpectralHessianHilbert ι data)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (programPGlobalSpectralHessianGraphOperator
            period hPeriod covector data).toLinearMap) ∧
      FiniteDimensional Complex
        (ProgramPGlobalSpectralHessianHilbert ι data ⧸
          LinearMap.range
            (programPGlobalSpectralHessianGraphOperator
              period hPeriod covector data).toLinearMap)

def programPGlobalSpectralHessianFredholmCertificate4D
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (d9Ellipticity :
      D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (data : ProductThroatSpectralData) :
    ProgramPGlobalSpectralHessianFredholmCertificate4D
      period hPeriod d9Ellipticity data where
  domainDense :=
    programPGlobalSpectralHessianMaximalDomain_dense
      period hPeriod covector data
  selfAdjoint :=
    programPGlobalSpectralHessianMaximalOperator_selfAdjoint
      period hPeriod covector data
  closed :=
    programPGlobalSpectralHessianMaximalOperator_closed
      period hPeriod covector data
  maximalFredholm :=
    programPGlobalSpectralHessianMaximalOperator_fredholm
      period hPeriod d9Ellipticity data
  graphFredholm :=
    programPGlobalSpectralHessianGraphOperator_fredholm
      period hPeriod d9Ellipticity data

end
end P0EFTJanusProgramPGlobalSpectralHessianFredholm4D
end JanusFormal
