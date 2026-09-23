import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPActualCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12HessianGhostReducedAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPComponentBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapAdjoint4D

/-! Concrete self-adjoint extension between the reduced minimal and maximal ghost Hessians. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedFPExtension4D
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
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D
open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
open P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
open P0EFTJanusProgramPT12WeightedFPSmooth4D
open P0EFTJanusProgramPT12WeightedFPClosed4D
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
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

local instance componentInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismTripletL2 period hPeriod (metric .plus) 0 0).range

local instance ghostPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod (metric .plus))
    (diffeomorphismGhostProjection period hPeriod (metric .plus)).range

local instance componentPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus)) :=
  @WithLp.instProdInnerProductSpace Real
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ _ (componentInnerProductSpace period hPeriod metric)
    _ (componentInnerProductSpace period hPeriod metric)
local instance componentBlockStar :
    Star (DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus))

local instance actualGhostBlockStar :
    Star (DiffeomorphismGhostPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) :=
  LinearPMap.instStar (𝕜 := Real)
    (E := DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
open P0EFTJanusProgramPT12WeightedFPComponentBlock4D

open P0EFTJanusProgramPT12WeightedFPBlock4D
open P0EFTJanusProgramPT12WeightedFPActualCore4D
open P0EFTJanusProgramPT12HessianGhostReduced4D
open P0EFTJanusProgramPT12HessianGhostReducedCore4D
open P0EFTJanusProgramPT12HessianGhostReducedAdjoint4D
open P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

attribute [local irreducible] weightedFPActualGhostBlock hessianGhostReduced

theorem weightedFPActualGhostBlock_isClosed :
    (weightedFPActualGhostBlock period hPeriod reference metric couplings).IsClosed :=
  (weightedFPActualGhostBlock_selfAdjoint period hPeriod reference metric couplings).isClosed

theorem hessianGhostReduced_le_weightedFPBlock :
    hessianGhostReduced period hPeriod reference metric couplings ≤
      weightedFPActualGhostBlock period hPeriod reference metric couplings := by
  rw [hessianGhostReduced_eq_closedFeature]
  exact closedFeatureOperator_minimal
    (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod)
    (H := DiffeomorphismGhostPairL2 period hPeriod (metric .plus)) _ _
    (hessianGhostReduced_feature_single period hPeriod reference metric couplings)
    (weightedFPActualGhostBlock period hPeriod reference metric couplings)
    (weightedFPActualGhostBlock_isClosed period hPeriod reference metric couplings)
    (weightedFPActualGhostBlock_reduced_smooth_graph period hPeriod reference metric couplings)

theorem weightedFPBlock_le_hessianGhostReducedAdjoint :
    weightedFPActualGhostBlock period hPeriod reference metric couplings ≤
      hessianGhostReducedAdjoint period hPeriod reference metric couplings :=
  @selfAdjointExtension_le_adjoint
    (DiffeomorphismGhostPairL2 period hPeriod (metric .plus))
    _ (ghostPairInnerProductSpace period hPeriod metric) _
    (hessianGhostReduced period hPeriod reference metric couplings)
    (weightedFPActualGhostBlock period hPeriod reference metric couplings)
    (hessianGhostReduced_denseDomain period hPeriod reference metric couplings)
    (weightedFPActualGhostBlock_selfAdjoint period hPeriod reference metric couplings)
    (hessianGhostReduced_le_weightedFPBlock period hPeriod reference metric couplings)

end
end JanusFormal.P0EFTJanusProgramPT12WeightedFPExtension4D