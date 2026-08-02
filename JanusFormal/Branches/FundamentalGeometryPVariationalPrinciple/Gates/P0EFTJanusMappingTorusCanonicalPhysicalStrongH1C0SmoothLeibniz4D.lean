import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

/-!
# Smooth Leibniz bridge for the canonical strong core

The existing manifold derivative already satisfies the scalar product rule.
This file transports it to the finite intrinsic frame, identifies the complete
smooth first jet of a product, and packages multiplication as a bilinear map
from the exact smooth fields into the canonical strong-core closure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Leibniz rule for every derivative in the existing finite smooth spanning
frame. -/
theorem frameDerivative_mul
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    frameDerivative period hPeriod Real frame
        (smoothScalarFieldMul period hPeriod first second) =
      fun point index =>
        first point *
            frameDerivative period hPeriod Real frame second point index +
          second point *
            frameDerivative period hPeriod Real frame first point index := by
  funext point index
  rw [frameDerivative_eq_mfderiv, frameDerivative_eq_mfderiv,
    frameDerivative_eq_mfderiv]
  have hDerivative := congrArg
    (fun derivative => derivative (frame.vectorAt point index))
    (mvfderiv_mul
      ((first.contMDiff_toFun.mdifferentiable (by simp)) point)
      ((second.contMDiff_toFun.mdifferentiable (by simp)) point))
  have hToFun :
      (smoothScalarFieldMul period hPeriod first second).toFun =
        first.toFun * second.toFun := by
    funext input
    rfl
  rw [hToFun]
  simpa only [smoothScalarFieldMul, smul_eq_mul, add_apply,
    smul_apply] using hDerivative

/-- Algebraic product of two scalar first jets. -/
def scalarFirstJetMul {Index : Type*}
    (first second : Real × (Index → Real)) :
    Real × (Index → Real) :=
  (first.1 * second.1,
    fun index => first.1 * second.2 index + second.1 * first.2 index)

/-- The existing smooth first jet preserves scalar multiplication with the
Leibniz jet product. -/
theorem smoothFirstJet_mul
    (frame : SmoothD8Frame period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    smoothFirstJet period hPeriod Real frame
        (smoothScalarFieldMul period hPeriod first second) =
      fun point => scalarFirstJetMul
        (smoothFirstJet period hPeriod Real frame first point)
        (smoothFirstJet period hPeriod Real frame second point) := by
  funext point
  apply Prod.ext
  · rfl
  · funext index
    exact congrFun (congrFun
      (frameDerivative_mul period hPeriod frame first second) point) index

/-- Product of two exact smooth fields, regarded in the canonical dense strong
core. -/
def smoothStrongH1C0CoreProduct
    (first second : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalScalarStrongH1C0Core period hPeriod :=
  smoothToCanonicalPhysicalScalarStrongH1C0Core
    period hPeriod (smoothScalarFieldMul period hPeriod first second)

/-- Multiplication on the exact smooth core is bilinear. -/
def smoothStrongH1C0CoreProductBilinear :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      SmoothQuotientField period hPeriod Real →ₗ[Real]
        CanonicalPhysicalScalarStrongH1C0Core period hPeriod :=
  LinearMap.mk₂ Real
    (smoothStrongH1C0CoreProduct period hPeriod)
    (by
      intro first second third
      have hMul :
          smoothScalarFieldMul period hPeriod (first + second) third =
            smoothScalarFieldMul period hPeriod first third +
              smoothScalarFieldMul period hPeriod second third := by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change (first point + second point) * third point =
          first point * third point + second point * third point
        ring
      unfold smoothStrongH1C0CoreProduct
      calc
        _ = smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
              (smoothScalarFieldMul period hPeriod first third +
                smoothScalarFieldMul period hPeriod second third) :=
          congrArg
            (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
            hMul
        _ = _ := (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod).map_add
            (smoothScalarFieldMul period hPeriod first third)
            (smoothScalarFieldMul period hPeriod second third))
    (by
      intro scalar first second
      have hMul :
          smoothScalarFieldMul period hPeriod (scalar • first) second =
            scalar • smoothScalarFieldMul period hPeriod first second := by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change (scalar * first point) * second point =
          scalar * (first point * second point)
        ring
      unfold smoothStrongH1C0CoreProduct
      calc
        _ = smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
              (scalar • smoothScalarFieldMul period hPeriod first second) :=
          congrArg
            (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
            hMul
        _ = _ := (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod).map_smul scalar
            (smoothScalarFieldMul period hPeriod first second))
    (by
      intro first second third
      have hMul :
          smoothScalarFieldMul period hPeriod first (second + third) =
            smoothScalarFieldMul period hPeriod first second +
              smoothScalarFieldMul period hPeriod first third := by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change first point * (second point + third point) =
          first point * second point + first point * third point
        ring
      unfold smoothStrongH1C0CoreProduct
      calc
        _ = smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
              (smoothScalarFieldMul period hPeriod first second +
                smoothScalarFieldMul period hPeriod first third) :=
          congrArg
            (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
            hMul
        _ = _ := (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod).map_add
            (smoothScalarFieldMul period hPeriod first second)
            (smoothScalarFieldMul period hPeriod first third))
    (by
      intro scalar first second
      have hMul :
          smoothScalarFieldMul period hPeriod first (scalar • second) =
            scalar • smoothScalarFieldMul period hPeriod first second := by
        apply SmoothQuotientField.ext period hPeriod Real
        intro point
        change first point * (scalar * second point) =
          scalar * (first point * second point)
        ring
      unfold smoothStrongH1C0CoreProduct
      calc
        _ = smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
              (scalar • smoothScalarFieldMul period hPeriod first second) :=
          congrArg
            (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
            hMul
        _ = _ := (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod).map_smul scalar
            (smoothScalarFieldMul period hPeriod first second))

@[simp]
theorem smoothStrongH1C0CoreProductBilinear_apply
    (first second : SmoothQuotientField period hPeriod Real) :
    smoothStrongH1C0CoreProductBilinear period hPeriod first second =
      smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod (smoothScalarFieldMul period hPeriod first second) :=
  rfl

theorem smoothStrongH1C0CoreProduct_continuous_projection
    (first second : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0CoreToContinuous period hPeriod
        (smoothStrongH1C0CoreProduct period hPeriod first second) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod first *
        smoothToCanonicalPhysicalContinuousScalar period hPeriod second := by
  apply ContinuousMap.ext
  intro point
  rfl

/-- Summary gate: the exact dense core is multiplicatively stable and its
first jet obeys the intrinsic Leibniz rule. -/
theorem canonical_physical_strong_h1_c0_smooth_leibniz_gate :
    (∀ (frame : SmoothD8Frame period hPeriod)
      (first second : SmoothQuotientField period hPeriod Real),
      smoothFirstJet period hPeriod Real frame
          (smoothScalarFieldMul period hPeriod first second) =
        fun point => scalarFirstJetMul
          (smoothFirstJet period hPeriod Real frame first point)
          (smoothFirstJet period hPeriod Real frame second point)) ∧
      (∀ first second : SmoothQuotientField period hPeriod Real,
        smoothStrongH1C0CoreProductBilinear period hPeriod first second =
          smoothToCanonicalPhysicalScalarStrongH1C0Core
            period hPeriod
              (smoothScalarFieldMul period hPeriod first second)) := by
  exact ⟨smoothFirstJet_mul period hPeriod,
    smoothStrongH1C0CoreProductBilinear_apply period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
end JanusFormal
