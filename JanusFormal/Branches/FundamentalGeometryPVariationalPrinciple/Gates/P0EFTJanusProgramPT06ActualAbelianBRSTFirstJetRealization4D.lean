import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeTrivializationReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D

/-!
# Centered actual Abelian BRST bridge through first physical jet order

For one component of an actual global Abelian ghost, the centered throat
representative of `d c` is the Frechet derivative of the centered
representative of the restricted scalar ghost.  Consequently its value and
first derivative are exactly the first and second slots of the actual scalar
second jet.

This is only the centered Abelian bridge for one ordinary real-valued component
through physical order one.  It does not identify moving-chart actions, a
Grassmann/graded carrier, the nonlinear diffeomorphism BRST operator, or the
full physical BV carrier.  Physical order two would differentiate once more
and therefore requires a T02-compatible scalar-ghost J3 extraction, which is
not yet available.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualAbelianBRSTFirstJetRealization4D

set_option autoImplicit false
noncomputable section

open Set Filter Function
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeTrivializationReconstruction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D

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

/-- One scalar component of the actual global ghost, restricted to the
physical throat. -/
def programPT06ActualAbelianGhostThroatScalar
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) : SmoothThroatField period hPeriod Real :=
  throatTrace period hPeriod Real
    (ghostComponent period hPeriod ghost component)

/-- The intrinsic throat restriction of the actual global exact potential is
the differential of the restricted scalar ghost. -/
theorem restrictExactGaugePotentialToThroat_eq_ghostThroatDifferential
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (point : EffectiveThroat period hPeriod) :
    (restrictAbelianGaugePotentialToThroat period hPeriod
        (exactGaugePotential period hPeriod ghost)).toFun component point =
      mvfderiv throatCoverModelWithCorners
        (programPT06ActualAbelianGhostThroatScalar period hPeriod ghost
          component).toFun point := by
  apply ContinuousLinearMap.ext
  intro tangent
  simp only [programPT06ActualAbelianGhostThroatScalar,
    restrictAbelianGaugePotentialToThroat, throatGaugePullbackValue,
    exactGaugePotential]
  unfold mvfderiv
  rw [throatTrace_mfderiv]
  rfl

/-- In the centered tangent frame and the same centered base chart, the
actual representative of `d c` agrees as a germ with the Frechet derivative
of the scalar ghost representative. -/
theorem throatExactGaugeCenteredChart_eventuallyEq_scalarFDeriv
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    throatGaugeCovectorCenteredChart period hPeriod
        (restrictAbelianGaugePotentialToThroat period hPeriod
          (exactGaugePotential period hPeriod ghost))
        component anchor anchor =ᶠ[𝓝
          (extChartAt throatCoverModelWithCorners anchor anchor)]
      fun coordinate =>
        fderiv Real
          (throatSmoothFieldChartRepresentative period hPeriod
            (programPT06ActualAbelianGhostThroatScalar period hPeriod ghost
              component) anchor)
          coordinate := by
  let chart := extChartAt throatCoverModelWithCorners anchor
  let scalarField :=
    programPT06ActualAbelianGhostThroatScalar period hPeriod ghost component
  have hCenterTarget : chart anchor ∈ chart.target :=
    chart.map_source (mem_extChartAt_source anchor)
  filter_upwards [extChartAt_target_mem_nhds' hCenterTarget] with coordinate
      hCoordinate
  let current := chart.symm coordinate
  have hCurrentSource : current ∈ chart.source :=
    chart.map_target hCoordinate
  have hCurrentFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet := by
    change current ∈ (chartAt ThroatCoverModel anchor).source
    simpa only [chart, extChartAt_source] using hCurrentSource
  have hRight : chart current = coordinate :=
    chart.right_inv hCoordinate
  have hOuter : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Real) scalarField.toFun current :=
    scalarField.contMDiff_toFun.mdifferentiableAt (by simp)
  have hInner : MDifferentiableAt 𝓘(Real, ThroatCoverCoordinates)
      throatCoverModelWithCorners chart.symm coordinate := by
    exact
      ((contMDiffOn_extChartAt_symm
          (I := throatCoverModelWithCorners) (n := ∞) anchor).contMDiffAt
        (extChartAt_target_mem_nhds' hCoordinate)).mdifferentiableAt (by simp)
  have hChain := mfderiv_comp coordinate hOuter hInner
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext value
    simp
  calc
    throatGaugeCovectorCenteredChart period hPeriod
        (restrictAbelianGaugePotentialToThroat period hPeriod
          (exactGaugePotential period hPeriod ghost))
        component anchor anchor coordinate =
      throatGaugeCovectorCoordinates period hPeriod
        (restrictAbelianGaugePotentialToThroat period hPeriod
          (exactGaugePotential period hPeriod ghost))
        component anchor current := by
          rfl
    _ = ((restrictAbelianGaugePotentialToThroat period hPeriod
          (exactGaugePotential period hPeriod ghost)).toFun component current).comp
        (((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
              Real current hCurrentFrame).symm :
          ThroatCoverCoordinates →L[Real]
            ThroatTangentFiber period hPeriod current) :=
      throatGaugeCovectorCoordinates_eq_trivializedPullback period hPeriod
        _ component anchor current hCurrentFrame
    _ = (mvfderiv throatCoverModelWithCorners
          scalarField.toFun current).comp
        (((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
              Real current hCurrentFrame).symm :
          ThroatCoverCoordinates →L[Real]
            ThroatTangentFiber period hPeriod current) := by
      rw [restrictExactGaugePotentialToThroat_eq_ghostThroatDifferential]
    _ = (fderiv Real (scalarField.toFun ∘ chart.symm) coordinate :
        ThroatCoverCoordinates →L[Real] Real) := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq',
        TangentBundle.symmL_trivializationAt hCurrentFrame, hRight,
        hRange, mfderivWithin_univ]
      simp only [current, chart] at hChain ⊢
      apply ContinuousLinearMap.ext
      intro tangent
      have hChainAt := congrArg
        (fun derivative => derivative tangent) hChain
      unfold mvfderiv
      rw [mfderiv_eq_fderiv] at hChainAt
      exact hChainAt.symm
    _ = (fderiv Real
        (throatSmoothFieldChartRepresentative period hPeriod scalarField
          anchor) coordinate : ThroatCoverCoordinates →L[Real] Real) := by
      rfl

/-- Centered actual scalar second jet of one global Abelian ghost component. -/
def programPT06ActualAbelianGhostComponentSecondJet
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet ThroatCoverCoordinates Real :=
  throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
    (programPT06ActualAbelianGhostThroatScalar period hPeriod ghost component)
    anchor anchor

/-- Centered actual gauge second jet of the BRST image `d c`. -/
def programPT06ActualAbelianBRSTGaugeComponentSecondJet
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) :=
  actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
    (restrictAbelianGaugePotentialToThroat period hPeriod
      (exactGaugePotential period hPeriod ghost)) component
    (throatGaugeSecondOrderJetBundleIndexAt period hPeriod anchor) anchor

/-- The value of the actual BRST gauge jet is the first-derivative slot of
the actual scalar ghost jet. -/
theorem programPT06ActualAbelianBRSTGaugeComponentSecondJet_value
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    (programPT06ActualAbelianBRSTGaugeComponentSecondJet period hPeriod ghost
        component anchor).value =
      (programPT06ActualAbelianGhostComponentSecondJet period hPeriod ghost
        component anchor).firstDerivative := by
  have hGerm :=
    throatExactGaugeCenteredChart_eventuallyEq_scalarFDeriv period hPeriod
      ghost component anchor
  have hAtCenter := hGerm.eq_of_nhds
  simp only [programPT06ActualAbelianBRSTGaugeComponentSecondJet,
    actualThroatGaugeSecondOrderJetLocalRepresentative,
    dif_pos (mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt period hPeriod
      anchor), throatGaugeCovectorSecondOrderJetInBaseChartAt_value,
    programPT06ActualAbelianGhostComponentSecondJet,
    throatSmoothFieldSecondOrderJetLocalRepresentative,
    dif_pos (mem_extChartAt_source anchor),
    throatSmoothFieldSecondOrderJetInChartAt_firstDerivative]
  simpa only [throatGaugeSecondOrderJetBundleIndexAt,
    throatGaugeCovectorCenteredChart, extChartAt_to_inv] using hAtCenter

/-- The first derivative of the actual BRST gauge jet is the second-derivative
slot of the actual scalar ghost jet. -/
theorem programPT06ActualAbelianBRSTGaugeComponentSecondJet_firstDerivative
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    (programPT06ActualAbelianBRSTGaugeComponentSecondJet period hPeriod ghost
        component anchor).firstDerivative =
      (programPT06ActualAbelianGhostComponentSecondJet period hPeriod ghost
        component anchor).secondDerivative := by
  have hGerm :=
    throatExactGaugeCenteredChart_eventuallyEq_scalarFDeriv period hPeriod
      ghost component anchor
  have hDerivative := hGerm.fderiv_eq (𝕜 := Real)
  simp only [programPT06ActualAbelianBRSTGaugeComponentSecondJet,
    actualThroatGaugeSecondOrderJetLocalRepresentative,
    dif_pos (mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt period hPeriod
      anchor), throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative,
    programPT06ActualAbelianGhostComponentSecondJet,
    throatSmoothFieldSecondOrderJetLocalRepresentative,
    dif_pos (mem_extChartAt_source anchor),
    throatSmoothFieldSecondOrderJetInChartAt_secondDerivative]
  simpa only [throatGaugeSecondOrderJetBundleIndexAt] using hDerivative

end
end P0EFTJanusProgramPT06ActualAbelianBRSTFirstJetRealization4D
end JanusFormal
