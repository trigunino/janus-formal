import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12WeightedFPClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapAdjoint4D

namespace JanusFormal.P0EFTJanusProgramPT12WeightedFPComponentBlock4D
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
open P0EFTJanusProgramPT12ClosedDoubleAdjoint4D
noncomputable section
private theorem reversedBlock_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (operator : H →ₗ.[Real] H) (hClosed : operator.IsClosed)
    (hDense : Dense (operator.domain : Set H)) (hAdjDense : Dense (operator.adjoint.domain : Set H)) :
    IsSelfAdjoint (offDiagonalOperator operator.adjoint operator) := by
  rw [LinearPMap.isSelfAdjoint_def,
    offDiagonalOperator_adjoint operator.adjoint operator hAdjDense hDense,
    closedOperator_adjoint_adjoint operator hClosed hDense hAdjDense]

end
end JanusFormal.P0EFTJanusProgramPT12WeightedFPComponentBlock4D

/-! Canonical weighted FP block in the actual ghost Hilbert spaces. -/
namespace JanusFormal.P0EFTJanusProgramPT12WeightedFPComponentBlock4D
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
attribute [local irreducible] weightedFPMinimal

def weightedFPComponentBlock :
    DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus) :=
  offDiagonalOperator (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (weightedFPAdjoint period hPeriod reference metric couplings)
    (weightedFPMinimal period hPeriod reference metric couplings)

theorem weightedFPComponentBlock_selfAdjoint :
    IsSelfAdjoint (weightedFPComponentBlock period hPeriod reference metric couplings) :=
  @reversedBlock_selfAdjoint (DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    _ (componentInnerProductSpace period hPeriod metric) _
    (weightedFPMinimal period hPeriod reference metric couplings)
    (weightedFPMinimal_isClosed period hPeriod reference metric couplings)
    (weightedFPMinimal_denseDomain period hPeriod reference metric couplings)
    (weightedFPAdjoint_denseDomain period hPeriod reference metric couplings)

attribute [local irreducible] weightedFPAdjoint weightedFPComponentBlock offDiagonalOperator

theorem weightedFPComponentBlock_domain_iff
    (field : DiffeomorphismGhostComponentPairL2 period hPeriod (metric .plus)) :
    field ∈ (weightedFPComponentBlock period hPeriod reference metric couplings).domain ↔
      field.fst ∈ (weightedFPMinimal period hPeriod reference metric couplings).domain ∧
      field.snd ∈ (weightedFPAdjoint period hPeriod reference metric couplings).domain :=
by
  unfold weightedFPComponentBlock
  exact offDiagonalOperator_domain_iff (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)
    (weightedFPAdjoint period hPeriod reference metric couplings)
    (weightedFPMinimal period hPeriod reference metric couplings) field

theorem weightedFPComponentBlock_smooth_graph
    (ghost antighost : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (WithLp.toLp 2
      (diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 ghost,
       diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 antighost),
     WithLp.toLp 2
      (weightedFPTransposeSmooth period hPeriod reference metric couplings antighost,
       weightedFPSmooth period hPeriod reference metric couplings ghost)) ∈
      (weightedFPComponentBlock period hPeriod reference metric couplings).graph := by
  rw [weightedFPComponentBlock, offDiagonalOperator_mem_graph_iff (H := DiffeomorphismTripletComponentL2 period hPeriod (metric .plus) 0)]
  constructor
  · have h := (weightedFPAdjoint period hPeriod reference metric couplings).mem_graph
      ⟨diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 antighost,
        weightedFPAdjoint_smooth_mem period hPeriod reference metric couplings antighost⟩
    rw [weightedFPAdjoint_smooth_apply] at h
    exact h
  · have h := (weightedFPMinimal period hPeriod reference metric couplings).mem_graph
      ⟨diffeomorphismTripletComponentSmooth period hPeriod (metric .plus) 0 ghost,
        weightedFPMinimal_smooth_mem period hPeriod reference metric couplings ghost⟩
    rw [weightedFPMinimal_smooth_apply] at h
    exact h
end
end JanusFormal.P0EFTJanusProgramPT12WeightedFPComponentBlock4D
