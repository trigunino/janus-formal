import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

/-!
# Actual LL third-order jet product vector-bundle core

The three smooth constant-fiber third-jet cores for the auxiliary metric,
measure and LL field assemble into their exact nested product.  Its domains
are those of the existing LL second-jet product, and its coordinate changes
are the componentwise algebraic transports already constructed at order
three.

This gate constructs only the smooth product core.  Third-jet extraction and
sections of the LL fields are left to later gates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

/-- Smooth product core of the three actual LL third-jet components. -/
def actualLLThirdOrderJetProductVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualLLThirdOrderJetFiber
      (ActualLLThirdOrderJetBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (vectorBundleCoreProd
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber))
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real)))
    (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := LLFieldFiber))

/-- The LL third-order product uses exactly the LL second-order product
domains. -/
@[simp]
theorem actualLLThirdOrderJetProductVectorBundleCore_baseSet
    (index : ActualLLThirdOrderJetBundleIndex period hPeriod) :
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod).baseSet
        index =
      (actualLLSecondOrderJetProductVectorBundleCore period hPeriod).baseSet
        index :=
  rfl

/-- The product-core coordinate change is the previously constructed
componentwise LL third-order transport. -/
@[simp]
theorem actualLLThirdOrderJetProductVectorBundleCore_coordChange_apply
    (first second : ActualLLThirdOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (jet : ActualLLThirdOrderJetFiber) :
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod).coordChange
        first second current jet =
      actualLLThirdOrderJetProductCoordChange period hPeriod
        first second current jet :=
  rfl

/-- Product-core transport commutes with componentwise truncation to the
existing LL second-order product core. -/
@[simp]
theorem actualLLThirdOrderJetProductVectorBundleCore_coordChange_truncate
    (first second : ActualLLThirdOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (actualLLThirdOrderJetProductVectorBundleCore
          period hPeriod).baseSet first ∩
        (actualLLThirdOrderJetProductVectorBundleCore
          period hPeriod).baseSet second)
    (jet : ActualLLThirdOrderJetFiber) :
    actualLLThirdOrderJetProductTruncate
        ((actualLLThirdOrderJetProductVectorBundleCore period hPeriod).coordChange
          first second current jet) =
      (actualLLSecondOrderJetProductVectorBundleCore period hPeriod).coordChange
        first second current (actualLLThirdOrderJetProductTruncate jet) := by
  rw [actualLLThirdOrderJetProductVectorBundleCore_coordChange_apply]
  exact actualLLThirdOrderJetProductCoordChange_truncate_apply_of_mem
    period hPeriod first second current
      (by simpa only [actualLLThirdOrderJetProductVectorBundleCore_baseSet]
        using hCurrent) jet

/-- The LL third-order product core has smooth coordinate changes. -/
theorem actualLLThirdOrderJetProductVectorBundleCore_isContMDiff :
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI :
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := LLMetricFiber)
  letI :
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := Real)
  letI :
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLFieldFiber)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := LLFieldFiber)
  letI :
      (vectorBundleCoreProd
        (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
          period hPeriod (Fiber := LLMetricFiber))
        (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
          period hPeriod (Fiber := Real))).IsContMDiff
            throatCoverModelWithCorners ∞ :=
    vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber))
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real))
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (vectorBundleCoreProd
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber))
      (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real)))
    (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := LLFieldFiber))

end
end P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D
end JanusFormal
