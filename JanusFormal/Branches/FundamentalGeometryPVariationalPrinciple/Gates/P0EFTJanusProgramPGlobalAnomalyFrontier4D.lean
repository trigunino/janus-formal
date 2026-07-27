import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalQuillenFrontier4D
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusProgramPD7Z4SpectralAnomalyBridge
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusPTPairedAnomalyCancellation

/-!
# Exact frontier of the global anomaly problem

PT-opposite additive classes cancel identically.  On the physical separated
Z4 spectrum, the local subtraction converges, PT-renormalized logarithms
agree, mode phases cancel and the explicit opposite inflow cancels.  On the
complete multiplicity-aware D10 spectrum, the absolutely summable chiral heat
trace and every finite-cutoff net converge to zero.

This is not `ANOMALY-GLOBAL-01`: these results do not construct the anomaly
class and its gauge-equivariant trivialization for the full geometric Janus
Fredholm family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAnomalyFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open P0EFTJanusProgramPD7Z4SpectralAnomalyBridge
open P0EFTJanusPTPairedAnomalyCancellation

/-- Every anomaly statement currently proved without importing the missing
global Fredholm-family bridge. -/
structure ProgramPGlobalAnomalyFrontierCertificate4D
    (data : ProductThroatSpectralData) where
  abstractPTCancellation :
    ∀ {A : Type*} [AddCommGroup A] (anomaly : A),
      totalAnomaly (ptConjugatePair anomaly) = 0
  physicalZ4Spectrum :
    PhysicalZ4SpectralAnomalyCertificate data
  continuumD10Cancellation :
    ∀ (time : HeatTime) (chirality : RootChiralityAssignment),
      programPD10InfiniteChiralHeatTrace data time chirality = 0
  continuumD10CutoffConvergence :
    ∀ (time : HeatTime) (chirality : RootChiralityAssignment),
      Filter.Tendsto
        (programPD10FiniteChiralHeatTrace data time chirality)
        Filter.atTop (nhds 0)

noncomputable def programPGlobalAnomalyFrontierCertificate4D
    (data : ProductThroatSpectralData) :
    ProgramPGlobalAnomalyFrontierCertificate4D data where
  abstractPTCancellation :=
    pt_conjugate_pair_cancels
  physicalZ4Spectrum :=
    physicalZ4SpectralAnomalyCertificate data
  continuumD10Cancellation :=
    programPD10InfiniteChiralHeatTrace_eq_zero data
  continuumD10CutoffConvergence :=
    programPD10FiniteChiralHeatTrace_tendsto_zero data

theorem global_anomaly_frontier_gate
    (data : ProductThroatSpectralData) :
    Nonempty (ProgramPGlobalAnomalyFrontierCertificate4D data) :=
  ⟨programPGlobalAnomalyFrontierCertificate4D data⟩

/-- Class cancellation alone cannot be promoted silently to a scalar
partition function: a determinant-gerbe trivialization is an independent
typed obligation. -/
theorem global_anomaly_missing_trivialization_blocks_scalar_partition
    (status : PTPairedPartitionStatus)
    (hMissing : ¬ status.determinantGerbeTrivializationConstructed) :
    ¬ scalarPartitionFunctionClosed status :=
  missing_trivialization_blocks_scalar_partition status hMissing

end
end P0EFTJanusProgramPGlobalAnomalyFrontier4D
end JanusFormal
