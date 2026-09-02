import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D

/-!
# Identity-centred C² matrix-root branch

This specializes the existing local C² root theorem to the constant identity
matrix.  Its domain is a concrete open neighbourhood of zero and its output
squares exactly to `I + variation`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D.canonicalMatrixNormedAddCommGroup

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D.canonicalMatrixNormedSpace

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Constant identity matrix as a genuine smooth matrix field. -/
def c2IdentityRootField :
    SmoothQuotientField period hPeriod Matrix4 :=
  constantSmoothField period hPeriod Matrix4 1

@[simp]
theorem c2IdentityRootField_apply
    (point : EffectiveQuotient period hPeriod) :
    c2IdentityRootField period hPeriod point = (1 : Matrix4) :=
  rfl

/-- The Sylvester derivative at the identity is multiplication by two and is
therefore bijective at every base point. -/
theorem c2IdentityRootField_regular :
    ∀ point, Function.Bijective
      (canonicalSylvesterOperator (c2IdentityRootField period hPeriod point)) := by
  intro point
  change Function.Bijective (canonicalSylvesterOperator (1 : Matrix4))
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨fun target : Matrix4 => (1 / 2 : Real) • target, ?_, ?_⟩
  · intro variation
    change (1 / 2 : Real) • (1 * variation + variation * 1) = variation
    ext row column
    simp
    ring
  · intro variation
    change 1 * ((1 / 2 : Real) • variation) +
      (1 / 2 : Real) • variation * 1 = variation
    ext row column
    simp
    ring

/-- The general smooth-field lift of the constant identity is exactly the
canonical identity in the C² matrix algebra. -/
theorem smoothMatrixFieldToC2_identityRoot :
    smoothMatrixFieldToC2 period hPeriod
        (c2IdentityRootField period hPeriod) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  unfold smoothMatrixFieldToC2 c2FiniteMatrixIdentity
  apply congrArg (smoothFiniteMatrixToC2 period hPeriod 4)
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp [smoothMatrixFieldCoefficients, c2IdentityRootField,
    smoothFiniteMatrixIdentity, constantSmoothField, Matrix.one_apply]

/-- Open zero-centred domain of the identity C² root branch. -/
def c2IdentityRootPerturbationDomain :
    Set (C2Matrix period hPeriod) :=
  c2MatrixRootPerturbationDomain period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod)

theorem c2IdentityRootPerturbationDomain_isOpen :
    IsOpen (c2IdentityRootPerturbationDomain period hPeriod) :=
  c2MatrixRootPerturbationDomain_isOpen period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod)

theorem zero_mem_c2IdentityRootPerturbationDomain :
    (0 : C2Matrix period hPeriod) ∈
      c2IdentityRootPerturbationDomain period hPeriod :=
  zero_mem_c2MatrixRootPerturbationDomain period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod)

/-- Identity-centred root branch. -/
def c2IdentityRootBranch :
    C2Matrix period hPeriod → C2Matrix period hPeriod :=
  c2MatrixRootPerturbationBranch period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod)

theorem c2IdentityRootBranch_contDiffOn :
    ContDiffOn Real 2 (c2IdentityRootBranch period hPeriod)
      (c2IdentityRootPerturbationDomain period hPeriod) :=
  c2MatrixRootPerturbationBranch_contDiffOn period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod)

/-- Exact square identity `root² = I + variation`. -/
theorem c2IdentityRootBranch_square
    {variation : C2Matrix period hPeriod}
    (hVariation : variation ∈
      c2IdentityRootPerturbationDomain period hPeriod) :
    c2FiniteMatrixSquare period hPeriod 4
        (c2IdentityRootBranch period hPeriod variation) =
      c2FiniteMatrixIdentity period hPeriod 4 + variation := by
  have hSquare := c2MatrixRootPerturbationBranch_square
    (period := period) (hPeriod := hPeriod) hVariation
  rw [smoothMatrixFieldToC2_identityRoot] at hSquare
  simpa [c2IdentityRootBranch, c2FiniteMatrixSquare,
    c2FiniteMatrixProduct_identity_left] using hSquare

@[simp]
theorem c2IdentityRootBranch_zero :
    c2IdentityRootBranch period hPeriod 0 =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  change c2MatrixLocalRootBranch period hPeriod
      (c2IdentityRootField period hPeriod)
      (c2IdentityRootField_regular period hPeriod)
      (c2FiniteMatrixSquare period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod
          (c2IdentityRootField period hPeriod)) + 0) = _
  rw [add_zero, c2MatrixLocalRootBranch_at_center,
    smoothMatrixFieldToC2_identityRoot]

/-- Gate marker: a concrete open C² neighbourhood of zero carries a smooth
identity-centred root whose square is exactly `I + variation`. -/
theorem canonical_physical_c2_identity_root_branch_gate :
    IsOpen (c2IdentityRootPerturbationDomain period hPeriod) ∧
      (0 : C2Matrix period hPeriod) ∈
        c2IdentityRootPerturbationDomain period hPeriod ∧
      ContDiffOn Real 2 (c2IdentityRootBranch period hPeriod)
        (c2IdentityRootPerturbationDomain period hPeriod) ∧
      ∀ variation, variation ∈
          c2IdentityRootPerturbationDomain period hPeriod →
        c2FiniteMatrixSquare period hPeriod 4
            (c2IdentityRootBranch period hPeriod variation) =
          c2FiniteMatrixIdentity period hPeriod 4 + variation :=
  ⟨c2IdentityRootPerturbationDomain_isOpen period hPeriod,
    zero_mem_c2IdentityRootPerturbationDomain period hPeriod,
    c2IdentityRootBranch_contDiffOn period hPeriod,
    fun _ hVariation => c2IdentityRootBranch_square period hPeriod hVariation⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
end JanusFormal
