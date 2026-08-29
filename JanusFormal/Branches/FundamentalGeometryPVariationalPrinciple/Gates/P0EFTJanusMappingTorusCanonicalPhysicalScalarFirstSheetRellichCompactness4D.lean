import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGreenCoreRegularityFactorization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

/-!
# Physical scalar Rellich factorization

The graph-elliptic estimate extends the smooth physical `H¹` realization to the
completed maximal Euler graph.  The completed ambient inclusion then factors as

`maximal graph -> physical H¹ -> physical bulk L²`.

Hence one Rellich theorem for the canonical physical `H¹` space makes the
maximal graph inclusion compact, makes every completed Lagrangian boundary
domain inclusion compact, and converts any coercive-surjective reference shift
into a compact resolvent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarGreenCoreRegularityFactorization4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

local instance physicalH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarH1 period hPeriod) :=
  canonicalPhysicalScalarH1CompleteSpace period hPeriod

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Physical `H¹` regularity factorization supplied by the graph-elliptic
estimate. -/
def physicalH1RegularityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (elliptic : green.GraphEllipticEstimate period hPeriod) :
    CanonicalScalarGreenCoreRegularityData
      (Regularity := CanonicalPhysicalScalarH1 period hPeriod) green.core where
  regularityCore := smoothToCanonicalPhysicalScalarH1 period hPeriod
  regularityInclusion := canonicalPhysicalScalarH1ToBulkL2 period hPeriod
  inclusion_agrees :=
    canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth period hPeriod
  constant := elliptic.constant
  nonnegative := elliptic.nonnegative
  bound := elliptic.bound

/-- Continuous physical `H¹` representative of every completed maximal graph
vector. -/
def completedPhysicalH1
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (elliptic : green.GraphEllipticEstimate period hPeriod) :
    CanonicalScalarGreenCoreGraphSpace green.core →L[Real]
      CanonicalPhysicalScalarH1 period hPeriod :=
  (green.physicalH1RegularityData period hPeriod elliptic).completedRegularity

/-- The maximal graph inclusion factors through physical `H¹`. -/
theorem physicalH1_factorization
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (elliptic : green.GraphEllipticEstimate period hPeriod)
    (field : CanonicalScalarGreenCoreGraphSpace green.core) :
    canonicalPhysicalScalarH1ToBulkL2 period hPeriod
        (green.completedPhysicalH1 period hPeriod elliptic field) =
      canonicalScalarGreenCoreGraphInclusion green.core field :=
  (green.physicalH1RegularityData period hPeriod elliptic)
    |>.regularityInclusion_completedRegularity field

/-- Exact remaining Rellich proposition for the physical scalar `H¹` space. -/
def PhysicalH1RellichCompactness : Prop :=
  IsCompactOperator
    (canonicalPhysicalScalarH1ToBulkL2 period hPeriod)

/-- Rellich compactness makes the completed maximal graph inclusion compact. -/
theorem maximalGraphInclusion_compact
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (elliptic : green.GraphEllipticEstimate period hPeriod)
    (rellich : PhysicalH1RellichCompactness period hPeriod) :
    IsCompactOperator
      (canonicalScalarGreenCoreGraphInclusion green.core) :=
  (green.physicalH1RegularityData period hPeriod elliptic)
    |>.graphInclusion_compact rellich

/-- Rellich compactness makes every completed physical Lagrangian-domain
inclusion compact. -/
theorem lagrangianInclusion_compact
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (rellich : PhysicalH1RellichCompactness period hPeriod) :
    IsCompactOperator
      ((inputs.triple period hPeriod green).lagrangianInclusion condition) :=
  (green.physicalH1RegularityData period hPeriod inputs.elliptic)
    |>.lagrangianInclusion_compact
      (inputs.triple period hPeriod green) condition rellich

/-- Coercivity plus physical Rellich compactness gives the direct compact
resolvent package. -/
def coerciveCompactEmbeddingAt
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (spectralParameter : Real)
    (coercive : (inputs.triple period hPeriod green).LagrangianCoerciveSurjectiveAt
      condition spectralParameter)
    (rellich : PhysicalH1RellichCompactness period hPeriod) :
    (inputs.triple period hPeriod green).LagrangianCoerciveCompactEmbeddingAt
      condition spectralParameter where
  coercive := coercive
  compact_inclusion := green.lagrangianInclusion_compact
    period hPeriod inputs condition rellich

/-- Direct compact physical resolvent generated from coercivity and Rellich. -/
noncomputable def compactResolventAt
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (spectralParameter : Real)
    (coercive : (inputs.triple period hPeriod green).LagrangianCoerciveSurjectiveAt
      condition spectralParameter)
    (rellich : PhysicalH1RellichCompactness period hPeriod) :
    (inputs.triple period hPeriod green).LagrangianCompactResolventAt
      condition spectralParameter :=
  (green.coerciveCompactEmbeddingAt period hPeriod inputs condition
    spectralParameter coercive rellich).compactResolvent
      (inputs.triple period hPeriod green) condition spectralParameter

/-- Physical Rellich factorization certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (rellich : PhysicalH1RellichCompactness period hPeriod) :
    IsCompactOperator
        (canonicalScalarGreenCoreGraphInclusion green.core) ∧
      IsCompactOperator
        ((inputs.triple period hPeriod green).lagrangianInclusion condition) :=
  ⟨green.maximalGraphInclusion_compact
      period hPeriod inputs.elliptic rellich,
    green.lagrangianInclusion_compact
      period hPeriod inputs condition rellich⟩

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
end JanusFormal
