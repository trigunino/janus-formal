import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D

/-!
# Compatibility of the doubled D9 connection with Clifford action

The globally descended Clifford generators preserve genuine smooth doubled
spinor sections.  Both the flat-cover derivative and its global covariant
descent intertwine this action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
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

/-- Continuous-linear form of one descended Clifford generator. -/
def d9DoubledMatterFiberCliffordGammaCLM
    (direction : Fin 3) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  LinearMap.toContinuousLinearMap
    (d9DoubledMatterFiberCliffordGamma direction)

@[simp] theorem d9DoubledMatterFiberCliffordGammaCLM_apply
    (direction : Fin 3) (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberCliffordGammaCLM direction matter =
      d9DoubledMatterFiberCliffordGamma direction matter :=
  rfl

/-- Pointwise Clifford action preserves the genuine smooth doubled section
space, including the two opposite quarter-root deck laws. -/
def d9DoubledMatterSpinorCliffordLift
    (choice : NormalRootChoice) (direction : Fin 3)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice where
  first :=
    { toFun := fun anchor =>
        (d9DoubledMatterFiberCliffordGamma direction (lift anchor)).1
      contMDiff_toFun := by
        have hCoordinate : ContDiff Real ∞
            (fun matter : D9DoubledMatterFiber =>
              (d9DoubledMatterFiberCliffordGammaCLM
                direction matter).1) :=
          contDiff_fst.comp
            (d9DoubledMatterFiberCliffordGammaCLM direction).contDiff
        exact hCoordinate.contMDiff.comp lift.contMDiff_toFun
      deck_equivariant := by
        intro winding anchor
        rw [SmoothThroatDoubledMatterSpinorLift.deck_monodromy,
          throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have hCompatibility := congrArg Prod.fst
          (d9DoubledMatterFiberCliffordGamma_monodromy choice direction
            winding (lift anchor))
        simpa [d9DoubledMatterSpinorMonodromy] using hCompatibility }
  second :=
    { toFun := fun anchor =>
        (d9DoubledMatterFiberCliffordGamma direction (lift anchor)).2
      contMDiff_toFun := by
        have hCoordinate : ContDiff Real ∞
            (fun matter : D9DoubledMatterFiber =>
              (d9DoubledMatterFiberCliffordGammaCLM
                direction matter).2) :=
          contDiff_snd.comp
            (d9DoubledMatterFiberCliffordGammaCLM direction).contDiff
        exact hCoordinate.contMDiff.comp lift.contMDiff_toFun
      deck_equivariant := by
        intro winding anchor
        rw [SmoothThroatDoubledMatterSpinorLift.deck_monodromy,
          throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have hCompatibility := congrArg Prod.snd
          (d9DoubledMatterFiberCliffordGamma_monodromy choice direction
            winding (lift anchor))
        simpa [d9DoubledMatterSpinorMonodromy] using hCompatibility }

@[simp] theorem d9DoubledMatterSpinorCliffordLift_apply
    (choice : NormalRootChoice) (direction : Fin 3)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (anchor : ThroatCover period hPeriod) :
    d9DoubledMatterSpinorCliffordLift
        period hPeriod choice direction lift anchor =
      d9DoubledMatterFiberCliffordGamma direction (lift anchor) :=
  rfl

/-- The flat-cover derivative intertwines every descended Clifford
generator. -/
theorem d9DoubledMatterSpinorFlatCoverDerivative_clifford
    (choice : NormalRootChoice) (direction : Fin 3)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9DoubledMatterSpinorFlatCoverDerivative period hPeriod choice
        (d9DoubledMatterSpinorCliffordLift
          period hPeriod choice direction lift) point =
      (d9DoubledMatterFiberCliffordGammaCLM direction).comp
        (d9DoubledMatterSpinorFlatCoverDerivative
          period hPeriod choice lift point) := by
  have hLift : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) lift point :=
    lift.contMDiff_toFun.mdifferentiableAt (by simp)
  have hGamma : MDifferentiableAt
      𝓘(Real, D9DoubledMatterFiber)
      𝓘(Real, D9DoubledMatterFiber)
      (d9DoubledMatterFiberCliffordGammaCLM direction) (lift point) :=
    (d9DoubledMatterFiberCliffordGammaCLM direction)
      |>.differentiableAt.mdifferentiableAt
  change mfderiv throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      ((d9DoubledMatterFiberCliffordGammaCLM direction) ∘ lift)
      point = _
  rw [mfderiv_comp point hGamma hLift]
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

/-- The global covariant derivative on the actual D9 bundle has the same
Clifford compatibility. -/
theorem d9DoubledMatterSpinorGlobalCovariantDerivative_clifford
    (choice : NormalRootChoice) (direction : Fin 3)
    (lift : SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9DoubledMatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
        (d9DoubledMatterSpinorSectionFiber period hPeriod choice
          (d9DoubledMatterSpinorCliffordLift
            period hPeriod choice direction lift)) base =
      (d9DoubledMatterFiberCliffordGammaCLM direction).comp
        (d9DoubledMatterSpinorGlobalCovariantDerivativeAt
          period hPeriod choice
          (d9DoubledMatterSpinorSectionFiber
            period hPeriod choice lift) base) := by
  rw [
    d9DoubledMatterSpinorGlobalCovariantDerivative_descended_flatCover
      period hPeriod choice
      (d9DoubledMatterSpinorCliffordLift
        period hPeriod choice direction lift) base,
    d9DoubledMatterSpinorGlobalCovariantDerivative_descended_flatCover
      period hPeriod choice lift base,
    d9DoubledMatterSpinorFlatCoverDerivative_clifford]
  exact ContinuousLinearMap.comp_assoc _ _ _

structure ProgramPD9MatterSpinorDoubledCliffordConnectionCompatibilityCertificate4D where
  choice : NormalRootChoice
  direction : Fin 3
  spinorSection :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  smoothCliffordSection :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  smoothCliffordSectionCanonical :
    smoothCliffordSection =
      d9DoubledMatterSpinorCliffordLift
        period hPeriod choice direction spinorSection
  globalCompatibility : ∀ base,
    d9DoubledMatterSpinorGlobalCovariantDerivativeAt period hPeriod choice
        (d9DoubledMatterSpinorSectionFiber period hPeriod choice
          smoothCliffordSection) base =
      (d9DoubledMatterFiberCliffordGammaCLM direction).comp
        (d9DoubledMatterSpinorGlobalCovariantDerivativeAt
          period hPeriod choice
          (d9DoubledMatterSpinorSectionFiber
            period hPeriod choice spinorSection) base)

def programPD9MatterSpinorDoubledCliffordConnectionCompatibilityCertificate4D :
    ProgramPD9MatterSpinorDoubledCliffordConnectionCompatibilityCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  direction := 0
  spinorSection := zeroSmoothThroatDoubledMatterSpinorLift
    period hPeriod .positiveQuarter
  smoothCliffordSection :=
    d9DoubledMatterSpinorCliffordLift period hPeriod
      .positiveQuarter 0
      (zeroSmoothThroatDoubledMatterSpinorLift
        period hPeriod .positiveQuarter)
  smoothCliffordSectionCanonical := rfl
  globalCompatibility :=
    d9DoubledMatterSpinorGlobalCovariantDerivative_clifford
      period hPeriod .positiveQuarter 0
      (zeroSmoothThroatDoubledMatterSpinorLift
        period hPeriod .positiveQuarter)

theorem
    programPD9MatterSpinorDoubledCliffordConnectionCompatibilityCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledCliffordConnectionCompatibilityCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledCliffordConnectionCompatibilityCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
end JanusFormal
