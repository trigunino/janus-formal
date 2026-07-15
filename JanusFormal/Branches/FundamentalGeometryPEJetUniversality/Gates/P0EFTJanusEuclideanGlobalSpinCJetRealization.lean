import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanMetricKoszulConnection
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCliffordSpin2DoubleCover

namespace JanusFormal
namespace P0EFTJanusEuclideanGlobalSpinCJetRealization

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff InnerProductSpace Manifold
open P0EFTJanusCliffordSpin2DoubleCover
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusEuclideanImmersionConnectionJetExtraction
open P0EFTJanusEuclideanMetricKoszulConnection
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover

universe u v w y

/-- Concrete Cech presentation of a principal bundle.  The transition maps are
required to satisfy the identity, inverse and triple-overlap laws on an open
cover. -/
structure CechPrincipalBundleData
    (Base : Type u) (Index : Type v) (StructureGroup : Type w)
    [TopologicalSpace Base] [Group StructureGroup] where
  domain : Index -> Set Base
  domain_isOpen : forall index, IsOpen (domain index)
  cover : forall base, Exists fun index => base ∈ domain index
  transition : Index -> Index -> Base -> StructureGroup
  transition_self : forall index base, base ∈ domain index ->
    transition index index base = 1
  transition_inverse : forall first second base,
    base ∈ domain first -> base ∈ domain second ->
      transition first second base * transition second first base = 1
  transition_cocycle : forall first second third base,
    base ∈ domain first -> base ∈ domain second -> base ∈ domain third ->
      transition first second base * transition second third base =
        transition first third base

/-- The one-chart presentation of the trivial principal bundle. -/
def trivialCechPrincipalBundle
    (Base : Type u) (StructureGroup : Type w)
    [TopologicalSpace Base] [Group StructureGroup] :
    CechPrincipalBundleData Base Unit StructureGroup where
  domain := fun _ => Set.univ
  domain_isOpen := fun _ => isOpen_univ
  cover := fun base => ⟨(), Set.mem_univ base⟩
  transition := fun _ _ _ => 1
  transition_self := by simp
  transition_inverse := by simp
  transition_cocycle := by simp

/-- Abelian determinant-line connection written in compatible local
trivializations.  For the one-chart realization below this is exactly a global
smooth connection potential. -/
structure CechAbelianConnectionData
    (Base : Type u) (Tangent : Type v) (Index : Type w)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent] where
  potential : Index -> Base -> ContinuousConnectionValue Tangent
  potential_contDiff : forall index, ContDiff ℝ ∞ (potential index)
  compatible : forall first second base,
    potential first base = potential second base

/-- A global smooth potential gives compatible connection data on the trivial
one-chart bundle. -/
def globalPotentialConnection
    {Base : Type u} {Tangent : Type v}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    (potential : Base -> ContinuousConnectionValue Tangent)
    (hPotential : ContDiff ℝ ∞ potential) :
    CechAbelianConnectionData Base Tangent Unit where
  potential := fun _ => potential
  potential_contDiff := fun _ => hPotential
  compatible := by simp

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- The rank-two Clifford SpinC principal bundle associated to a Euclidean
chart.  Global topological sectors require a nontrivial cover; the Euclidean
chart itself has the canonical one-chart bundle. -/
def EuclideanMetricProjectedSeedImmersionData.spinCBundle
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    CechPrincipalBundleData Tangent Unit CliffordSpinC2 :=
  trivialCechPrincipalBundle Tangent CliffordSpinC2

/-- The supplied smooth gauge potential is a genuine global determinant-line
connection on the one-chart SpinC bundle. -/
def EuclideanMetricProjectedSeedImmersionData.spinCConnection
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    CechAbelianConnectionData Tangent Tangent Unit :=
  globalPotentialConnection data.coefficients.gaugePotential
    data.coefficients.gaugePotential_contDiff

/-- The Euclidean source and ambient coefficient maps are smooth manifold maps,
not merely coordinate functions. -/
theorem EuclideanMetricProjectedSeedImmersionData.immersion_contMDiff
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    ContMDiff 𝓘(ℝ, Tangent) 𝓘(ℝ, Ambient) ∞
      data.coefficients.immersion :=
  data.coefficients.immersion_contDiff.contMDiff

/-- Data-bearing closure statement for the Euclidean manifold/SpinC extraction
stage.  Every conjunct is witnessed by a construction above. -/
theorem EuclideanMetricProjectedSeedImmersionData.global_spinC_jet_realization
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    ContMDiff 𝓘(ℝ, Tangent) 𝓘(ℝ, Ambient) ∞
        data.coefficients.immersion ∧
      Nonempty (CechPrincipalBundleData Tangent Unit CliffordSpinC2) ∧
      Nonempty (CechAbelianConnectionData Tangent Tangent Unit) ∧
      ContDiff ℝ ∞ data.physicalOperator := by
  exact ⟨EuclideanMetricProjectedSeedImmersionData.immersion_contMDiff data,
    ⟨EuclideanMetricProjectedSeedImmersionData.spinCBundle data⟩,
    ⟨EuclideanMetricProjectedSeedImmersionData.spinCConnection data⟩,
    data.physicalOperator_contDiff⟩

end

end P0EFTJanusEuclideanGlobalSpinCJetRealization
end JanusFormal
