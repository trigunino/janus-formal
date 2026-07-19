import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

/-!
# Global abelian gauge H0 on D8

The kernel of the actual global abelian gauge differential is identified with
the constant `U(1)^2` Lie-algebra values, and hence with `Real × Real`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAbelianGaugeGlobalH04D

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
open P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The real-linear kernel of the actual intrinsic abelian gauge
differential on smooth global ghosts. -/
abbrev GlobalAbelianGaugeZeroMode :=
  LinearMap.ker (abelianGaugeGenerator period hPeriod)

/-- A Lie-algebra value regarded as a smooth constant ghost on D8. -/
def constantGhost (value : GaugeLieAlgebra) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const

@[simp]
theorem constantGhost_apply
    (value : GaugeLieAlgebra) (point : EffectiveQuotient period hPeriod) :
    constantGhost period hPeriod value point = value :=
  rfl

@[simp]
theorem exactGaugePotential_constantGhost
    (value : GaugeLieAlgebra) :
    exactGaugePotential period hPeriod (constantGhost period hPeriod value) = 0 := by
  exact (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
    (constantGhost period hPeriod value)).2 ⟨value, fun _ => rfl⟩

/-- Evaluation at one point is inverse to formation of a smooth constant
ghost on the genuine connected D8 quotient. -/
def globalAbelianGaugeZeroModeEquiv :
    GlobalAbelianGaugeZeroMode period hPeriod ≃ GaugeLieAlgebra where
  toFun ghost := ghost.1 (Classical.choice (effectiveQuotient_nonempty period hPeriod))
  invFun value :=
    ⟨constantGhost period hPeriod value,
      by
        change exactGaugePotential period hPeriod
          (constantGhost period hPeriod value) = 0
        exact exactGaugePotential_constantGhost period hPeriod value⟩
  left_inv ghost := by
    apply Subtype.ext
    apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
    intro point
    have hGhostZero :
        exactGaugePotential period hPeriod ghost.1 = 0 := by
      have hKernel := ghost.property
      change exactGaugePotential period hPeriod ghost.1 = 0 at hKernel
      exact hKernel
    obtain ⟨value, hValue⟩ :=
      (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod ghost.1).1
        hGhostZero
    exact (hValue (Classical.choice (effectiveQuotient_nonempty period hPeriod))).trans
      (hValue point).symm
  right_inv value := rfl

/-- The evaluation equivalence is real-linear on the genuine global kernel. -/
def globalAbelianGaugeZeroModeLinearEquiv :
    GlobalAbelianGaugeZeroMode period hPeriod ≃ₗ[Real] GaugeLieAlgebra where
  toEquiv := globalAbelianGaugeZeroModeEquiv period hPeriod
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Standard two real coordinates of the global abelian gauge zero modes. -/
def globalAbelianGaugeZeroModeRealPairEquiv :
    GlobalAbelianGaugeZeroMode period hPeriod ≃ Real × Real :=
  (globalAbelianGaugeZeroModeEquiv period hPeriod).trans
    ((EuclideanSpace.equiv (Fin 2) Real).toEquiv.trans
      (finTwoArrowEquiv Real))

/-- Real-linear standard coordinates of the global abelian gauge zero modes. -/
def globalAbelianGaugeZeroModeRealPairLinearEquiv :
    GlobalAbelianGaugeZeroMode period hPeriod ≃ₗ[Real] Real × Real :=
  (globalAbelianGaugeZeroModeLinearEquiv period hPeriod).trans
    ((EuclideanSpace.equiv (Fin 2) Real).toLinearEquiv.trans
      (LinearEquiv.finTwoArrow Real Real))

end

end P0EFTJanusMappingTorusAbelianGaugeGlobalH04D
end JanusFormal
