import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphFaithfulness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalRobinL2Injection4D

/-!
# Faithful canonical L2 coordinates for the physical diffeomorphism ghost

The intrinsic finite generating frame gives smooth scalar coefficients for a
genuine tangent-bundle ghost.  Their canonical throat `L²` classes form a
faithful finite Hilbert coordinate.  No global tangent trivialization and no
local Faddeev--Popov PDE are asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2Faithfulness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open MeasureTheory
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusCanonicalRobinL2Injection4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldGhostFrameL2 :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GhostFrame :=
  finiteSmoothThroatGeneratingFrame period hPeriod

private abbrev GhostMeasure :=
  intrinsicCanonicalThroatVolumeMeasure period hPeriod

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure (GhostMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- Finite Hilbert sum of the canonical scalar `L²` coefficient spaces. -/
abbrev PhysicalGhostFiniteFrameL2 :=
  PiLp 2 (fun _ : Fin (GhostFrame period hPeriod).count =>
    ThroatScalarL2 period hPeriod (GhostMeasure period hPeriod))

/-- The canonical smooth-scalar inclusion, recorded as a linear map. -/
def smoothThroatFieldCanonicalL2LinearMap :
    SmoothThroatField period hPeriod Real →ₗ[Real]
      ThroatScalarL2 period hPeriod (GhostMeasure period hPeriod) where
  toFun := smoothThroatFieldToL2 period hPeriod (GhostMeasure period hPeriod)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [smoothThroatFieldToL2_ae period hPeriod (GhostMeasure period hPeriod)
        (first + second),
       smoothThroatFieldToL2_ae period hPeriod (GhostMeasure period hPeriod)
        first,
       smoothThroatFieldToL2_ae period hPeriod (GhostMeasure period hPeriod)
        second,
       Lp.coeFn_add
        (smoothThroatFieldToL2 period hPeriod (GhostMeasure period hPeriod)
          first)
        (smoothThroatFieldToL2 period hPeriod (GhostMeasure period hPeriod)
          second)]
      with point hSum hFirst hSecond hAdd
    simp only [Pi.add_apply] at hAdd
    rw [hSum, hAdd, hFirst, hSecond]
    rfl
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [smoothThroatFieldToL2_ae period hPeriod (GhostMeasure period hPeriod)
        (scalar • field),
       smoothThroatFieldToL2_ae period hPeriod (GhostMeasure period hPeriod)
        field,
       Lp.coeFn_smul scalar
        (smoothThroatFieldToL2 period hPeriod (GhostMeasure period hPeriod)
          field)]
      with point hScaled hField hSmul
    simp only [Pi.smul_apply, smul_eq_mul] at hSmul
    rw [hScaled]
    simp only [RingHom.id_apply]
    rw [hSmul, hField]
    rfl

/-- One intrinsic finite-frame coefficient is linear in the tangent ghost. -/
def physicalGhostFiniteFrameCoefficientLinearMap
    (index : Fin (GhostFrame period hPeriod).count) :
    CInfinityThroatGhost period hPeriod →ₗ[Real]
      SmoothThroatField period hPeriod Real where
  toFun ghost :=
    intrinsicThroatFiniteFrameCoefficient period hPeriod
      (GhostFrame period hPeriod) ghost index
  map_add' first second := by
    apply SmoothThroatField.ext period hPeriod Real
    intro point
    change
      intrinsicThroatFiniteFrameCoefficientAt period hPeriod
          (GhostFrame period hPeriod) point index (first point + second point) =
        intrinsicThroatFiniteFrameCoefficientAt period hPeriod
            (GhostFrame period hPeriod) point index (first point) +
          intrinsicThroatFiniteFrameCoefficientAt period hPeriod
            (GhostFrame period hPeriod) point index (second point)
    exact (intrinsicThroatFiniteFrameCoefficientAt period hPeriod
      (GhostFrame period hPeriod) point index).map_add (first point) (second point)
  map_smul' scalar ghost := by
    apply SmoothThroatField.ext period hPeriod Real
    intro point
    change
      intrinsicThroatFiniteFrameCoefficientAt period hPeriod
          (GhostFrame period hPeriod) point index (scalar • ghost point) =
        scalar • intrinsicThroatFiniteFrameCoefficientAt period hPeriod
          (GhostFrame period hPeriod) point index (ghost point)
    exact (intrinsicThroatFiniteFrameCoefficientAt period hPeriod
      (GhostFrame period hPeriod) point index).map_smul scalar (ghost point)

/-- Genuine finite `L²` coordinate of a smooth physical throat ghost. -/
def physicalGhostFiniteFrameL2LinearMap :
    CInfinityThroatGhost period hPeriod →ₗ[Real]
      PhysicalGhostFiniteFrameL2 period hPeriod where
  toFun ghost := WithLp.toLp 2 fun index =>
    smoothThroatFieldCanonicalL2LinearMap period hPeriod
      (physicalGhostFiniteFrameCoefficientLinearMap period hPeriod index ghost)
  map_add' first second := by
    apply PiLp.ext
    intro index
    simp
  map_smul' scalar ghost := by
    apply PiLp.ext
    intro index
    simp

/-- The finite intrinsic `L²` coordinate loses no smooth tangent ghost. -/
theorem physicalGhostFiniteFrameL2LinearMap_injective :
    Function.Injective (physicalGhostFiniteFrameL2LinearMap period hPeriod) := by
  intro first second hEqual
  have hCoefficient : ∀ index : Fin (GhostFrame period hPeriod).count,
      intrinsicThroatFiniteFrameCoefficient period hPeriod
          (GhostFrame period hPeriod) first index =
        intrinsicThroatFiniteFrameCoefficient period hPeriod
          (GhostFrame period hPeriod) second index := by
    intro index
    apply smoothThroatFieldToCanonicalL2_injective period hPeriod
    have hCoordinate := congrArg
      (fun coordinate : PhysicalGhostFiniteFrameL2 period hPeriod =>
        coordinate index) hEqual
    change
      smoothThroatFieldToL2 period hPeriod (GhostMeasure period hPeriod)
          (intrinsicThroatFiniteFrameCoefficient period hPeriod
            (GhostFrame period hPeriod) first index) =
        smoothThroatFieldToL2 period hPeriod (GhostMeasure period hPeriod)
          (intrinsicThroatFiniteFrameCoefficient period hPeriod
            (GhostFrame period hPeriod) second index) at hCoordinate
    exact hCoordinate
  apply ContMDiffSection.ext
  intro point
  calc
    first point =
        ∑ index : Fin (GhostFrame period hPeriod).count,
          intrinsicThroatFiniteFrameCoefficient period hPeriod
              (GhostFrame period hPeriod) first index point •
            (GhostFrame period hPeriod).vectorAt point index :=
      intrinsicThroatFiniteFrame_reconstructs period hPeriod
        (GhostFrame period hPeriod) first point
    _ = ∑ index : Fin (GhostFrame period hPeriod).count,
          intrinsicThroatFiniteFrameCoefficient period hPeriod
              (GhostFrame period hPeriod) second index point •
            (GhostFrame period hPeriod).vectorAt point index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hCoefficient index]
    _ = second point :=
      (intrinsicThroatFiniteFrame_reconstructs period hPeriod
        (GhostFrame period hPeriod) second point).symm

/-- Gate 260: the physical diffeomorphism ghost has a faithful canonical
finite-frame `L²` coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_l2_faithfulness_gate :
    Function.Injective (physicalGhostFiniteFrameL2LinearMap period hPeriod) :=
  physicalGhostFiniteFrameL2LinearMap_injective period hPeriod

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2Faithfulness4D
end JanusFormal
