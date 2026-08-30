import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrange4D

/-!
# Nine-block decomposition of the global Euler--Lagrange operator

The Fréchet derivative of the exact assembled action is the sum of the
derivatives of its nine physical action blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D

universe u

/-- Sum of the Euler one-forms of the nine exact action blocks. -/
def fullCoupledEulerBlockSum
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    (blocks : FullCoupledActionBlocks Configuration) :
    EulerOneForm Configuration :=
  fun configuration =>
    ((((((((actionGradient blocks.candidateA configuration +
      actionGradient blocks.matter configuration) +
      actionGradient blocks.robin configuration) +
      actionGradient blocks.ll configuration) +
      actionGradient blocks.einsteinHilbertPlus configuration) +
      actionGradient blocks.einsteinHilbertMinus configuration) +
      actionGradient blocks.maxwellPlus configuration) +
      actionGradient blocks.maxwellMinus configuration) +
      actionGradient blocks.finiteBV configuration)

/-- Pointwise decomposition of the Euler covector of a `C²` nine-block action. -/
theorem fullCoupledAction_gradient_apply_eq_blockSum
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    (blocks : FullCoupledActionBlocks Configuration)
    (configuration : Configuration)
    (hC2 : FullCoupledC2At blocks configuration) :
    actionGradient (fullCoupledAction blocks) configuration =
      fullCoupledEulerBlockSum blocks configuration := by
  have h := hC2
  have hCandidateA := h.candidateA.differentiableAt (by norm_num)
  have hMatter := h.matter.differentiableAt (by norm_num)
  have hRobin := h.robin.differentiableAt (by norm_num)
  have hLL := h.ll.differentiableAt (by norm_num)
  have hEHPlus := h.einsteinHilbertPlus.differentiableAt (by norm_num)
  have hEHMinus := h.einsteinHilbertMinus.differentiableAt (by norm_num)
  have hMaxwellPlus := h.maxwellPlus.differentiableAt (by norm_num)
  have hMaxwellMinus := h.maxwellMinus.differentiableAt (by norm_num)
  have hFiniteBV := h.finiteBV.differentiableAt (by norm_num)
  unfold actionGradient fullCoupledAction fullCoupledEulerBlockSum
  change fderiv Real
      ((((((((blocks.candidateA + blocks.matter) + blocks.robin) +
        blocks.ll) + blocks.einsteinHilbertPlus) +
        blocks.einsteinHilbertMinus) + blocks.maxwellPlus) +
        blocks.maxwellMinus) + blocks.finiteBV) configuration =
    ((((((((fderiv Real blocks.candidateA configuration +
      fderiv Real blocks.matter configuration) +
      fderiv Real blocks.robin configuration) +
      fderiv Real blocks.ll configuration) +
      fderiv Real blocks.einsteinHilbertPlus configuration) +
      fderiv Real blocks.einsteinHilbertMinus configuration) +
      fderiv Real blocks.maxwellPlus configuration) +
      fderiv Real blocks.maxwellMinus configuration) +
      fderiv Real blocks.finiteBV configuration)
  rw [fderiv_add
      (((((((hCandidateA.add hMatter).add hRobin).add hLL).add hEHPlus).add
        hEHMinus).add hMaxwellPlus).add hMaxwellMinus) hFiniteBV,
    fderiv_add
      ((((((hCandidateA.add hMatter).add hRobin).add hLL).add hEHPlus).add
        hEHMinus).add hMaxwellPlus) hMaxwellMinus,
    fderiv_add
      (((((hCandidateA.add hMatter).add hRobin).add hLL).add hEHPlus).add
        hEHMinus) hMaxwellPlus,
    fderiv_add
      ((((hCandidateA.add hMatter).add hRobin).add hLL).add hEHPlus) hEHMinus,
    fderiv_add
      (((hCandidateA.add hMatter).add hRobin).add hLL) hEHPlus,
    fderiv_add ((hCandidateA.add hMatter).add hRobin) hLL,
    fderiv_add (hCandidateA.add hMatter) hRobin,
    fderiv_add hCandidateA hMatter]

/-- The Euler one-form of a globally `C²` nine-block action decomposes exactly
into the sum of the nine block Euler one-forms. -/
theorem fullCoupledAction_gradient_eq_blockSum
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    (blocks : FullCoupledActionBlocks Configuration)
    (hC2 : ∀ configuration, FullCoupledC2At blocks configuration) :
    actionGradient (fullCoupledAction blocks) =
      fullCoupledEulerBlockSum blocks := by
  funext configuration
  exact fullCoupledAction_gradient_apply_eq_blockSum
    blocks configuration (hC2 configuration)

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- The exact global Euler--Lagrange operator is componentwise the sum of the
nine exact action-block Euler one-forms. -/
theorem globalEulerLagrangeOperator_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    globalEulerLagrangeOperator period hPeriod chart =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod chart.family measure) := by
  unfold globalEulerLagrangeOperator
  rw [globalCandidateAActionPullback_eq_blocks period hPeriod chart]
  exact fullCoupledAction_gradient_eq_blockSum _ chart.blocksC2

/-- Directional form of the nine-component global Euler decomposition. -/
theorem globalEulerLagrangeOperator_blockSum_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration direction : chart.Configuration) :
    globalEulerLagrangeOperator period hPeriod chart configuration direction =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod chart.family measure)
        configuration direction := by
  rw [globalEulerLagrangeOperator_eq_blockSum period hPeriod chart]

end
end P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
end JanusFormal
