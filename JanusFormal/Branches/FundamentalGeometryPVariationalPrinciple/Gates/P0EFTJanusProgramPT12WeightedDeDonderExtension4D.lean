import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderActualCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianBosonReducedAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderComponentBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedDeDonderClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapAdjoint4D

/-! Self-adjoint weighted de Donder block on the metric and B Hilbert components. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderExtension4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
open P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D
open P0EFTJanusProgramPT12WeightedDeDonderSmooth4D
open P0EFTJanusProgramPT12WeightedDeDonderClosed4D
open P0EFTJanusProgramPT12RectangularOffDiagonal4D
open P0EFTJanusProgramPT12RectangularSelfAdjoint4D
open P0EFTJanusProgramPT12IsometricPMapTransport4D
open P0EFTJanusProgramPT12IsometricPMapAdjoint4D

private theorem selfAdjointExtension_le_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (minimal extension : H →ₗ.[Real] H) (hDense : Dense (minimal.domain : Set H))
    (hSelf : IsSelfAdjoint extension) (hLe : minimal ≤ extension) :
    extension ≤ minimal.adjoint := by
  have hSym := LinearPMap.adjoint_isFormalAdjoint (T := extension) hSelf.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hSelf] at hSym
  apply LinearPMap.IsFormalAdjoint.le_adjoint hDense
  intro first second
  have hValue : minimal first = extension ⟨first.val, hLe.1 first.property⟩ := hLe.2 rfl
  rw [hValue]
  exact hSym ⟨first.val, hLe.1 first.property⟩ second

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
local instance metricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismMetricProjection period hPeriod (metric .plus)).range

local instance auxiliaryInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2).range

local instance bosonInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismBosonProjection period hPeriod (metric .plus)).range

local instance componentPairInnerProductSpace :
    InnerProductSpace Real (MetricBAuxiliaryPairL2 period hPeriod (metric .plus)) :=
  @WithLp.instProdInnerProductSpace Real
    (DiffeomorphismMetricL2 period hPeriod (metric .plus))
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 2)
    _ _ (metricInnerProductSpace period hPeriod metric)
    _ (auxiliaryInnerProductSpace period hPeriod metric)
local instance componentBlockStar :
    Star (MetricBAuxiliaryPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      MetricBAuxiliaryPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := MetricBAuxiliaryPairL2 period hPeriod (metric .plus))

local instance actualBosonBlockStar :
    Star (DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
open P0EFTJanusProgramPT12WeightedDeDonderClosed4D

open P0EFTJanusProgramPT12WeightedDeDonderComponentBlock4D

open P0EFTJanusProgramPT12WeightedDeDonderBlock4D
open P0EFTJanusProgramPT12WeightedDeDonderActualCore4D
open P0EFTJanusProgramPT12BosonBoundedMass4D
open P0EFTJanusProgramPT12BosonDeDonderCore4D
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
open P0EFTJanusProgramPT12HessianBosonReduced4D
open P0EFTJanusProgramPT12HessianBosonReducedCore4D
open P0EFTJanusProgramPT12HessianBosonReducedAdjoint4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

local instance bosonContinuousStar : Star (DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →L[Real] DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) :=
  ⟨ContinuousLinearMap.adjoint (𝕜 := Real) (E := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) (F := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))⟩

attribute [local irreducible] weightedDeDonderActualBosonBlock bosonBoundedMass hessianBosonReduced

/-- The actual metric–B realization, with the original bounded auxiliary mass restored. -/
def weightedDeDonderBosonHessian : DiffeomorphismBosonPairL2 period hPeriod (metric .plus) →ₗ.[Real] DiffeomorphismBosonPairL2 period hPeriod (metric .plus) :=
  boundedPerturbation (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings) (bosonBoundedMass period hPeriod reference metric couplings)

theorem weightedDeDonderBosonHessian_selfAdjoint :
    IsSelfAdjoint (weightedDeDonderBosonHessian period hPeriod reference metric couplings) :=
  @boundedPerturbation_selfAdjoint (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) _ (bosonInnerProductSpace period hPeriod metric) _
    (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings) (bosonBoundedMass period hPeriod reference metric couplings)
    (weightedDeDonderActualBosonBlock_selfAdjoint period hPeriod reference metric couplings) (bosonBoundedMass_selfAdjoint period hPeriod reference metric couplings)

theorem weightedDeDonderBosonHessian_domain :
    (weightedDeDonderBosonHessian period hPeriod reference metric couplings).domain =
      (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings).domain :=
  @boundedPerturbation_domain (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) _ (bosonInnerProductSpace period hPeriod metric)
    (weightedDeDonderActualBosonBlock period hPeriod reference metric couplings) (bosonBoundedMass period hPeriod reference metric couplings)

theorem weightedDeDonderBosonHessian_isClosed :
    (weightedDeDonderBosonHessian period hPeriod reference metric couplings).IsClosed :=
  @IsSelfAdjoint.isClosed Real (DiffeomorphismBosonPairL2 period hPeriod (metric .plus))
    _ _ (bosonInnerProductSpace period hPeriod metric) _
    (weightedDeDonderBosonHessian period hPeriod reference metric couplings)
    (weightedDeDonderBosonHessian_selfAdjoint period hPeriod reference metric couplings)

theorem weightedDeDonderBosonHessian_smooth_graph (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismBosonPairSmooth period hPeriod (metric .plus) field,
     hessianBosonReducedSmoothOutput period hPeriod reference metric couplings field) ∈
      (weightedDeDonderBosonHessian period hPeriod reference metric couplings).graph := by
  rw [weightedDeDonderBosonHessian, boundedPerturbation_mem_graph_iff]
  exact weightedDeDonderActualBosonBlock_reduced_smooth_graph period hPeriod reference metric couplings field

theorem hessianBosonReduced_le_weightedDeDonderBosonHessian :
    hessianBosonReduced period hPeriod reference metric couplings ≤ weightedDeDonderBosonHessian period hPeriod reference metric couplings := by
  rw [hessianBosonReduced_eq_closedFeature]
  exact closedFeatureOperator_minimal
    (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (H := DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) _ _
    (hessianBosonReduced_feature_single period hPeriod reference metric couplings)
    (weightedDeDonderBosonHessian period hPeriod reference metric couplings)
    (weightedDeDonderBosonHessian_isClosed period hPeriod reference metric couplings)
    (weightedDeDonderBosonHessian_smooth_graph period hPeriod reference metric couplings)

theorem weightedDeDonderBosonHessian_le_reducedAdjoint :
    weightedDeDonderBosonHessian period hPeriod reference metric couplings ≤ hessianBosonReducedAdjoint period hPeriod reference metric couplings :=
  @selfAdjointExtension_le_adjoint (DiffeomorphismBosonPairL2 period hPeriod (metric .plus)) _ (bosonInnerProductSpace period hPeriod metric) _
    (hessianBosonReduced period hPeriod reference metric couplings) (weightedDeDonderBosonHessian period hPeriod reference metric couplings)
    (hessianBosonReduced_denseDomain period hPeriod reference metric couplings)
    (weightedDeDonderBosonHessian_selfAdjoint period hPeriod reference metric couplings)
    (hessianBosonReduced_le_weightedDeDonderBosonHessian period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12WeightedDeDonderExtension4D


