import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiClosedSymmetry4D

/-! Closed Hilbert quotient of the literal three-slot LL Jacobi operator.
At zero flux the inactive auxiliary/measure directions are removed, with
exact domain transport and pairing. No finite residual kernel is assumed. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal LinearPMap InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiClosedSymmetry4D
open P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

abbrev ReducedLLFieldL2 :=
  Lp LLFieldFiber (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

def fullLLFieldReadout : FullLLHilbert period hPeriod →L[Real] ReducedLLFieldL2 period hPeriod :=
  WithLp.sndL 2 Real _ _

def fullLLAuxMeasureNullSpace : Submodule Real (FullLLHilbert period hPeriod) :=
  (fullLLFieldReadout period hPeriod).ker

instance fullLLAuxMeasureNullSpace_isClosed :
    IsClosed (fullLLAuxMeasureNullSpace period hPeriod : Set (FullLLHilbert period hPeriod)) :=
  ContinuousLinearMap.isClosed_ker _

abbrev FullLLReducedHilbert := FullLLHilbert period hPeriod ⧸ fullLLAuxMeasureNullSpace period hPeriod

/-- The quotient retains exactly the LL field L² coordinate. -/
def fullLLReducedHilbertEquiv :
    FullLLReducedHilbert period hPeriod ≃ₗ[Real] ReducedLLFieldL2 period hPeriod :=
  (fullLLFieldReadout period hPeriod).toLinearMap.quotKerEquivOfSurjective
    (fun field => ⟨WithLp.toLp 2 (0, field), rfl⟩)

theorem fullLLReducedHilbertEquiv_mk (vector : FullLLHilbert period hPeriod) :
    fullLLReducedHilbertEquiv period hPeriod
      ((fullLLAuxMeasureNullSpace period hPeriod).mkQ vector) =
      fullLLFieldReadout period hPeriod vector := rfl

theorem fullLLReducedHilbert_pureAuxMeasure_zero
    (aux : Lp LLMetricFiber (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (measure : Lp Real (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    (fullLLAuxMeasureNullSpace period hPeriod).mkQ
      (pureAuxMeasureHilbert period hPeriod aux measure) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rfl

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration)

def fullLLReducedHilbertCore : GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
    FullLLReducedHilbert period hPeriod :=
  (fullLLAuxMeasureNullSpace period hPeriod).mkQ.comp
    (fullLLSmoothToHilbertLinearMap period hPeriod analysis)

theorem fullLLReducedHilbertCore_readout (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullLLReducedHilbertEquiv period hPeriod
      (fullLLReducedHilbertCore period hPeriod analysis direction) =
      llSmoothToL2 period hPeriod direction.2.toTest := rfl

include data in
theorem fullLLReducedHilbertCore_denseRange :
    DenseRange (fullLLReducedHilbertCore period hPeriod analysis) := by
  have hDense : DenseRange (fullLLSmoothToHilbertLinearMap period hPeriod analysis) :=
    fullLLJacobiSmoothPMap_denseDomain period hPeriod data analysis
  exact (fullLLAuxMeasureNullSpace period hPeriod).mkQ_surjective.denseRange.comp
    hDense (fullLLAuxMeasureNullSpace period hPeriod).mkQL.continuous

variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

include hZero in
theorem fullLLAuxMeasureNullSpace_graph_zero (vector : FullLLHilbert period hPeriod)
    (hVector : vector ∈ fullLLAuxMeasureNullSpace period hPeriod) :
    (vector, (0 : FullLLHilbert period hPeriod)) ∈
      (fullLLJacobiClosedPMap period hPeriod data analysis).graph := by
  have hField : WithLp.snd vector = 0 := hVector
  have hValue : pureAuxMeasureHilbert period hPeriod
      (WithLp.fst (WithLp.fst vector)) (WithLp.snd (WithLp.fst vector)) = vector := by
    change WithLp.toLp 2 (WithLp.toLp 2
      (WithLp.fst (WithLp.fst vector), WithLp.snd (WithLp.fst vector)), 0) = vector
    rw [← hField]
    rfl
  obtain ⟨hDomain, hOutput⟩ := fullLLJacobiClosedPMap_pureAuxMeasureL2_zeroFlux
    period hPeriod data analysis hZero
      (WithLp.fst (WithLp.fst vector)) (WithLp.snd (WithLp.fst vector))
  exact (fullLLJacobiClosedPMap period hPeriod data analysis).mem_graph_iff.mpr
    ⟨⟨_, hDomain⟩, hValue, hOutput⟩

def fullLLReducedJacobi : FullLLReducedHilbert period hPeriod →ₗ.[Real]
    FullLLReducedHilbert period hPeriod :=
  quotientPMap (fullLLJacobiClosedPMap period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace period hPeriod)

theorem fullLLReducedJacobi_isClosed : (fullLLReducedJacobi period hPeriod data analysis).IsClosed :=
  quotientPMap_isClosed _ _ (fullLLJacobiClosedPMap_isClosed period hPeriod data analysis)

theorem fullLLReducedJacobi_symmetric :
    (fullLLReducedJacobi period hPeriod data analysis).IsFormalAdjoint
      (fullLLReducedJacobi period hPeriod data analysis) :=
  quotientPMap_symmetric _ _ (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)

include hZero in
theorem fullLLReducedJacobi_graph_project
    (vector : (fullLLJacobiClosedPMap period hPeriod data analysis).domain) :
    ((fullLLAuxMeasureNullSpace period hPeriod).mkQ (vector : FullLLHilbert period hPeriod),
      (fullLLAuxMeasureNullSpace period hPeriod).mkQ
        (fullLLJacobiClosedPMap period hPeriod data analysis vector)) ∈
      (fullLLReducedJacobi period hPeriod data analysis).graph :=
  quotientPMap_graph_project _ _ (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero) vector

include hZero in
theorem fullLLReducedJacobi_domain :
    (fullLLReducedJacobi period hPeriod data analysis).domain =
      (fullLLJacobiClosedPMap period hPeriod data analysis).domain.map
        (fullLLAuxMeasureNullSpace period hPeriod).mkQ :=
  quotientPMap_domain _ _ (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero)

include hZero in
theorem fullLLReducedJacobi_denseDomain :
    Dense ((fullLLReducedJacobi period hPeriod data analysis).domain :
      Set (FullLLReducedHilbert period hPeriod)) := by
  apply quotientPMap_denseDomain _ _
    (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero)
  exact (fullLLJacobiSmoothPMap_denseDomain period hPeriod data analysis).mono
    (fullLLJacobiSmoothPMap_le_closed period hPeriod data analysis).1

include hZero in
theorem fullLLReducedJacobi_pairing
    (vector : (fullLLJacobiClosedPMap period hPeriod data analysis).domain)
    (test : FullLLHilbert period hPeriod)
    (hDomain : (fullLLAuxMeasureNullSpace period hPeriod).mkQ (vector : FullLLHilbert period hPeriod) ∈
      (fullLLReducedJacobi period hPeriod data analysis).domain) :
    inner Real ((fullLLReducedJacobi period hPeriod data analysis)
      ⟨(fullLLAuxMeasureNullSpace period hPeriod).mkQ (vector : FullLLHilbert period hPeriod), hDomain⟩)
      ((fullLLAuxMeasureNullSpace period hPeriod).mkQ test) =
      inner Real (fullLLJacobiClosedPMap period hPeriod data analysis vector) test :=
  quotientPMap_pairing _ _ (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero) vector test hDomain

include hZero in
theorem fullLLReducedJacobi_zero_iff
    (vector : (fullLLJacobiClosedPMap period hPeriod data analysis).domain)
    (hDomain : (fullLLAuxMeasureNullSpace period hPeriod).mkQ (vector : FullLLHilbert period hPeriod) ∈
      (fullLLReducedJacobi period hPeriod data analysis).domain) :
    (fullLLReducedJacobi period hPeriod data analysis)
      ⟨(fullLLAuxMeasureNullSpace period hPeriod).mkQ (vector : FullLLHilbert period hPeriod), hDomain⟩ = 0 ↔
      fullLLJacobiClosedPMap period hPeriod data analysis vector = 0 :=
  quotientPMap_zero_iff _ _ (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero) vector hDomain

end
end P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D
end JanusFormal
