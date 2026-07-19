import Mathlib.Analysis.InnerProductSpace.PiL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

/-!
# Finite temporal Fourier ghosts: the constant zero mode

Complex finite temporal Fourier fields give genuine real `U(1)^2` ghosts by
taking their real and imaginary parts.  This gate proves that realization is
injective and that its constant zero-mode range lies in the kernel of the
intrinsic exact-potential map `c ↦ dc`.

Only this kernel inclusion is proved.  The reverse inclusion, the resulting
finite temporal cohomology computation, and the derivative bridge between
`AddCircle.hasDerivAt_fourier` and the quotient-manifold `mvfderiv` remain
open.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

private abbrev sphereData :=
  reflectedSphereData period hPeriodPos.out.ne'

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period) :=
  reflectedSphereQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period) :=
  reflectedSphereQuotient_isManifold period hPeriodPos.out.ne'

/-- Real and imaginary parts identify one complex value with the real
two-component Lie algebra of `U(1)^2`. -/
def complexGaugeLieAlgebraEquiv :
    Complex ≃ₗᵢ[Real] GaugeLieAlgebra :=
  Complex.orthonormalBasisOneI.repr

@[simp]
theorem complexGaugeLieAlgebraEquiv_apply (value : Complex) :
    complexGaugeLieAlgebraEquiv value = ![value.re, value.im] :=
  Complex.orthonormalBasisOneI_repr_apply value

/-- Pointwise Re/Im realization of a genuine smooth complex quotient field as
a genuine smooth real `U(1)^2` ghost. -/
def complexSmoothFieldGaugeGhostLinearMap :
    SmoothQuotientField period hPeriodPos.out.ne' Complex →ₗ[Real]
      SmoothQuotientField period hPeriodPos.out.ne' GaugeLieAlgebra where
  toFun field :=
    { toFun := fun point => complexGaugeLieAlgebraEquiv (field point)
      contMDiff_toFun :=
        complexGaugeLieAlgebraEquiv.contDiff.contMDiff.comp
          field.contMDiff_toFun }
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriodPos.out.ne' GaugeLieAlgebra
    intro point
    exact complexGaugeLieAlgebraEquiv.map_add (first point) (second point)
  map_smul' scalar field := by
    apply SmoothQuotientField.ext period hPeriodPos.out.ne' GaugeLieAlgebra
    intro point
    exact complexGaugeLieAlgebraEquiv.map_smul scalar (field point)

theorem complexSmoothFieldGaugeGhostLinearMap_injective :
    Function.Injective
      (complexSmoothFieldGaugeGhostLinearMap period) := by
  intro first second hEqual
  apply SmoothQuotientField.ext period hPeriodPos.out.ne' Complex
  intro point
  apply complexGaugeLieAlgebraEquiv.injective
  have hValue := congrArg
    (fun ghost : SmoothQuotientField period hPeriodPos.out.ne' GaugeLieAlgebra =>
      ghost point) hEqual
  exact hValue

/-- Genuine finite temporal Fourier realization in the real `U(1)^2` ghost
bundle. -/
def finiteTemporalFourierGaugeGhostLinearMap :
    FiniteTemporalFourierCoefficients →ₗ[Real]
      SmoothQuotientField period hPeriodPos.out.ne' GaugeLieAlgebra :=
  (complexSmoothFieldGaugeGhostLinearMap period).comp
    (finiteTemporalFourierFieldLinearMap period)

theorem finiteTemporalFourierGaugeGhostLinearMap_injective :
    Function.Injective
      (finiteTemporalFourierGaugeGhostLinearMap period) := by
  intro first second hEqual
  apply finiteTemporalFourierFieldLinearMap_injective period
  apply complexSmoothFieldGaugeGhostLinearMap_injective period
  exact hEqual

/-- The coefficient supported at temporal frequency zero. -/
def temporalZeroModeCoefficientLinearMap :
    Complex →ₗ[Real] FiniteTemporalFourierCoefficients where
  toFun coefficient := Finsupp.single 0 coefficient
  map_add' first second := by
    ext mode
    by_cases hMode : (0 : Int) = mode <;>
      simp [Finsupp.single_apply, hMode]
  map_smul' scalar coefficient := by
    exact (Finsupp.smul_single scalar 0 coefficient).symm

/-- The realized zero mode is exactly the constant Re/Im ghost. -/
theorem finiteTemporalFourierGaugeGhostLinearMap_zeroMode
    (coefficient : Complex) :
    finiteTemporalFourierGaugeGhostLinearMap period
        (temporalZeroModeCoefficientLinearMap coefficient) =
      constantSmoothField period hPeriodPos.out.ne' GaugeLieAlgebra
        (complexGaugeLieAlgebraEquiv coefficient) := by
  apply SmoothQuotientField.ext period hPeriodPos.out.ne' GaugeLieAlgebra
  intro point
  obtain ⟨representative, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period) point
  change complexGaugeLieAlgebraEquiv
      (finiteTemporalFourierFieldLinearMap period
        (Finsupp.single 0 coefficient)
        (mappingTorusMk (sphereData period) representative)) =
    complexGaugeLieAlgebraEquiv coefficient
  apply congrArg complexGaugeLieAlgebraEquiv
  rw [finiteTemporalFourierFieldLinearMap_single]
  change coefficient * temporalComplexFourierQuotientField period 0
      (mappingTorusMk (sphereData period) representative) = coefficient
  rw [temporalComplexFourierQuotientField_mk, fourier_coe_apply]
  simp

/-- Every constant real `U(1)^2` ghost has zero intrinsic exact potential. -/
theorem exactGaugePotential_constantGaugeGhost_eq_zero
    (value : GaugeLieAlgebra) :
    exactGaugePotential period hPeriodPos.out.ne'
        (constantSmoothField period hPeriodPos.out.ne' GaugeLieAlgebra value) =
      0 := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change mvfderiv coverModelWithCorners
      (fun _ : EffectiveQuotient period => value component) point tangent = 0
  rw [mvfderiv_const]
  rfl

/-- Exact-potential map restricted to the genuine finite temporal ghost
realization. -/
def finiteTemporalFourierExactGaugeLinearMap :
    FiniteTemporalFourierCoefficients →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriodPos.out.ne' :=
  (abelianGaugeGenerator period hPeriodPos.out.ne').comp
    (finiteTemporalFourierGaugeGhostLinearMap period)

@[simp]
theorem finiteTemporalFourierExactGaugeLinearMap_zeroMode
    (coefficient : Complex) :
    finiteTemporalFourierExactGaugeLinearMap period
        (temporalZeroModeCoefficientLinearMap coefficient) = 0 := by
  change exactGaugePotential period hPeriodPos.out.ne'
      (finiteTemporalFourierGaugeGhostLinearMap period
        (temporalZeroModeCoefficientLinearMap coefficient)) = 0
  rw [finiteTemporalFourierGaugeGhostLinearMap_zeroMode]
  exact exactGaugePotential_constantGaugeGhost_eq_zero period _

/-- Proven half of the finite temporal kernel computation: every claimed
constant candidate is included here.  The converse inclusion is not asserted
without a quotient-manifold Fourier derivative bridge. -/
theorem temporalZeroMode_range_le_exactGauge_kernel :
    LinearMap.range temporalZeroModeCoefficientLinearMap ≤
      LinearMap.ker (finiteTemporalFourierExactGaugeLinearMap period) := by
  rintro coefficients ⟨coefficient, rfl⟩
  change finiteTemporalFourierExactGaugeLinearMap period
      (temporalZeroModeCoefficientLinearMap coefficient) = 0
  exact finiteTemporalFourierExactGaugeLinearMap_zeroMode period coefficient

end

end P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
end JanusFormal
