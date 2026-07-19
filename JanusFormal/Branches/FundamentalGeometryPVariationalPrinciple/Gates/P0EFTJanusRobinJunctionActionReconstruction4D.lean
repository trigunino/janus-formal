import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusRobinJunctionActionReconstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exact affine-quadratic reconstruction of the unchanged Robin action.  The
bulk traces produce the indispensable constant and linear terms. -/
theorem robinJunctionAction_reconstructed_from_euler_and_actualHessian
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction base : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        junction mu =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) mu +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) junction mu +
        (1 / 2 : Real) *
          robinJunctionActionMixedHessian period hPeriod kPlus kMinus bulkPlus
            bulkMinus base junction junction mu := by
  rw [robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
    kMinus bulkPlus bulkMinus base junction junction mu]
  have hBase : Integrable
      (robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
        (0 : SmoothThroatField period hPeriod Real)) mu :=
    (robinJunctionDensity_continuous period hPeriod kPlus kMinus bulkPlus
      bulkMinus (0 : SmoothThroatField period hPeriod Real)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFirst : Integrable
      (robinFirstVariationDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
        (0 : SmoothThroatField period hPeriod Real) junction) mu :=
    (robinFirstVariationDensity_continuous period hPeriod kPlus kMinus bulkPlus
      bulkMinus (0 : SmoothThroatField period hPeriod Real) junction).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hHessian : Integrable
      (robinHessianDensity period hPeriod kPlus kMinus junction junction) mu :=
    (robinHessianDensity_continuous period hPeriod kPlus kMinus junction
      junction).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold robinJunctionAction robinFirstVariation robinHessian
  calc
    (∫ point, robinJunctionDensity period hPeriod kPlus kMinus bulkPlus
        bulkMinus junction point ∂mu) =
        ∫ point,
          (robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
              (0 : SmoothThroatField period hPeriod Real) point +
            robinFirstVariationDensity period hPeriod kPlus kMinus bulkPlus
              bulkMinus (0 : SmoothThroatField period hPeriod Real) junction point) +
            (1 / 2 : Real) * robinHessianDensity period hPeriod kPlus kMinus
              junction junction point ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        have hZero :
            (0 : SmoothThroatField period hPeriod Real) point = 0 := rfl
        have hResidual :
            junctionResidual period hPeriod kPlus kMinus bulkPlus bulkMinus
                (0 : SmoothThroatField period hPeriod Real) point =
              -(kPlus * bulkPlus
                  (fixedThroatQuotientInclusion period hPeriod point)) -
                kMinus * bulkMinus
                  (fixedThroatQuotientInclusion period hPeriod point) := by
          change kPlus * (0 - _) + kMinus * (0 - _) = _
          ring_nf
          rfl
        simp [robinJunctionDensity, robinFirstVariationDensity,
          robinHessianDensity, hZero, hResidual]
        ring)
    _ = (∫ point,
          robinJunctionDensity period hPeriod kPlus kMinus bulkPlus bulkMinus
              (0 : SmoothThroatField period hPeriod Real) point +
            robinFirstVariationDensity period hPeriod kPlus kMinus bulkPlus
              bulkMinus (0 : SmoothThroatField period hPeriod Real) junction point ∂mu) +
        ∫ point, (1 / 2 : Real) *
          robinHessianDensity period hPeriod kPlus kMinus junction junction point ∂mu :=
      integral_add (hBase.add hFirst) (hHessian.const_mul (1 / 2 : Real))
    _ = _ := by
      rw [integral_add hBase hFirst, integral_const_mul]

/-- Exact quadratic Taylor formula along an affine junction curve, stated
only with the genuine Robin action, Euler pairing, and Hessian. -/
theorem robinJunctionAction_affine_exact_taylor
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (junction direction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (t : Real) :
    robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
        (junctionAffineCurve period hPeriod junction direction t) mu =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction mu +
        t * robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          junction direction mu +
        (t ^ 2 / 2) * robinHessian period hPeriod kPlus kMinus direction
          direction mu := by
  have hCurve := robinJunctionAction_affine period hPeriod kPlus kMinus
    bulkPlus bulkMinus junction direction mu t
  have hUnit := robinJunctionAction_affine period hPeriod kPlus kMinus
    bulkPlus bulkMinus (0 : SmoothThroatField period hPeriod Real) direction mu 1
  have hReconstruct :=
    robinJunctionAction_reconstructed_from_euler_and_actualHessian period hPeriod
      kPlus kMinus bulkPlus bulkMinus direction direction mu
  rw [robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
    kMinus bulkPlus bulkMinus direction direction direction mu] at hReconstruct
  rw [show junctionAffineCurve period hPeriod
      (0 : SmoothThroatField period hPeriod Real) direction 1 = direction by
    ext point
    simp [junctionAffineCurve]] at hUnit
  nlinarith

end

end P0EFTJanusRobinJunctionActionReconstruction4D
end JanusFormal
