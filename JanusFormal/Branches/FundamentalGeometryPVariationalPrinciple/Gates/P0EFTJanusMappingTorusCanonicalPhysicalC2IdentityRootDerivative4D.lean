import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D

/-! # Exact inverse-Sylvester derivative of the C² identity root -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
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

theorem c2MatrixLocalRootBranch_mem_sylvesterRegularRootSet
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    c2MatrixLocalRootBranch period hPeriod root hRegular nearby ∈
      c2MatrixSylvesterRegularRootSet period hPeriod := by
  have hSource :=
    (c2MatrixLocalSquareChart period hPeriod root hRegular).map_target hNearby
  rw [c2MatrixLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  exact hSource.2

private theorem c2MatrixLocalRootSylvesterEquiv_exists
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    ∃ equiv : C2Matrix period hPeriod ≃L[Real] C2Matrix period hPeriod,
      (equiv : C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod) =
        c2FiniteMatrixSylvester period hPeriod 4
          (c2MatrixLocalRootBranch period hPeriod root hRegular nearby) := by
  have hMem := c2MatrixLocalRootBranch_mem_sylvesterRegularRootSet
    period hPeriod root hRegular nearby hNearby
  change ∃ equiv : C2Matrix period hPeriod ≃L[Real] C2Matrix period hPeriod,
    (equiv : C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod) =
      c2MatrixSylvesterFamily period hPeriod
        (c2MatrixLocalRootBranch period hPeriod root hRegular nearby) at hMem
  simpa only [c2MatrixSylvesterFamily_apply] using hMem

/-- The bounded Sylvester equivalence at the root selected over `nearby`. -/
def c2MatrixLocalRootSylvesterEquiv
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    C2Matrix period hPeriod ≃L[Real] C2Matrix period hPeriod :=
  Classical.choose
    (c2MatrixLocalRootSylvesterEquiv_exists period hPeriod root hRegular
      nearby hNearby)

theorem c2MatrixLocalRootSylvesterEquiv_forward_eq
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    (c2MatrixLocalRootSylvesterEquiv period hPeriod root hRegular nearby
        hNearby : C2Matrix period hPeriod →L[Real]
          C2Matrix period hPeriod) =
      c2FiniteMatrixSylvester period hPeriod 4
        (c2MatrixLocalRootBranch period hPeriod root hRegular nearby) :=
  Classical.choose_spec
    (c2MatrixLocalRootSylvesterEquiv_exists period hPeriod root hRegular
      nearby hNearby)

/-- Exact inverse-Sylvester derivative of the local root branch. -/
def c2MatrixLocalRootDerivative
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  (c2MatrixLocalRootSylvesterEquiv period hPeriod root hRegular nearby
    hNearby).symm

theorem c2MatrixLocalRootBranch_hasFDerivAt
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (nearby : C2Matrix period hPeriod)
    (hNearby : nearby ∈ c2MatrixLocalRootTarget
      period hPeriod root hRegular) :
    HasFDerivAt
      (c2MatrixLocalRootBranch period hPeriod root hRegular)
      (c2MatrixLocalRootDerivative period hPeriod root hRegular nearby hNearby)
      nearby := by
  let selected :=
    c2MatrixLocalRootBranch period hPeriod root hRegular nearby
  let equiv :=
    c2MatrixLocalRootSylvesterEquiv period hPeriod root hRegular nearby hNearby
  have hForward : HasFDerivAt
      (c2MatrixLocalSquareChart period hPeriod root hRegular)
      (equiv : C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod)
      selected := by
    exact (c2FiniteMatrixSquare_hasFDerivAt period hPeriod 4 selected)
      |>.congr_fderiv
        (c2MatrixLocalRootSylvesterEquiv_forward_eq period hPeriod root
          hRegular nearby hNearby).symm
  exact (c2MatrixLocalSquareChart period hPeriod root hRegular)
    |>.hasFDerivAt_symm hNearby hForward

/-- Derivative of the translated, zero-centred root branch. -/
def c2MatrixRootPerturbationDerivative
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈ c2MatrixRootPerturbationDomain
      period hPeriod root hRegular) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  c2MatrixLocalRootDerivative period hPeriod root hRegular
    (c2FiniteMatrixSquare period hPeriod 4
      (smoothMatrixFieldToC2 period hPeriod root) + variation) hVariation

theorem c2MatrixRootPerturbationBranch_hasFDerivAt
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈ c2MatrixRootPerturbationDomain
      period hPeriod root hRegular) :
    HasFDerivAt
      (c2MatrixRootPerturbationBranch period hPeriod root hRegular)
      (c2MatrixRootPerturbationDerivative period hPeriod root hRegular
        variation hVariation) variation := by
  have hOuter := c2MatrixLocalRootBranch_hasFDerivAt period hPeriod root
    hRegular
    (c2FiniteMatrixSquare period hPeriod 4
      (smoothMatrixFieldToC2 period hPeriod root) + variation) hVariation
  have hInner : HasFDerivAt
      (fun current : C2Matrix period hPeriod =>
        c2FiniteMatrixSquare period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root) + current)
      (ContinuousLinearMap.id Real (C2Matrix period hPeriod)) variation := by
    have hId : HasFDerivAt
        (fun current : C2Matrix period hPeriod => current)
        (ContinuousLinearMap.id Real (C2Matrix period hPeriod)) variation :=
      (ContinuousLinearMap.id Real
        (C2Matrix period hPeriod)).hasFDerivAt
    simpa using
      (hasFDerivAt_const (x := variation)
        (c := c2FiniteMatrixSquare period hPeriod 4
          (smoothMatrixFieldToC2 period hPeriod root))).add
        hId
  simpa [c2MatrixRootPerturbationBranch,
    c2MatrixRootPerturbationDerivative] using
      hOuter.comp variation hInner

theorem c2MatrixRootPerturbationDerivative_sylvester
    (root : SmoothQuotientField period hPeriod Matrix4)
    (hRegular : ∀ point, Function.Bijective
      (canonicalSylvesterOperator (root point)))
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈ c2MatrixRootPerturbationDomain
      period hPeriod root hRegular)
    (direction : C2Matrix period hPeriod) :
    c2FiniteMatrixSylvester period hPeriod 4
        (c2MatrixRootPerturbationBranch period hPeriod root hRegular variation)
        (c2MatrixRootPerturbationDerivative period hPeriod root hRegular
          variation hVariation direction) =
      direction := by
  let nearby := c2FiniteMatrixSquare period hPeriod 4
    (smoothMatrixFieldToC2 period hPeriod root) + variation
  let equiv := c2MatrixLocalRootSylvesterEquiv period hPeriod root hRegular
    nearby hVariation
  change c2FiniteMatrixSylvester period hPeriod 4
      (c2MatrixLocalRootBranch period hPeriod root hRegular nearby)
      (equiv.symm direction) = direction
  rw [← c2MatrixLocalRootSylvesterEquiv_forward_eq period hPeriod root
    hRegular nearby hVariation]
  exact equiv.apply_symm_apply direction

/-- Exact derivative of the identity-centred root used by the paired
interaction action. -/
def c2IdentityRootDerivative
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootPerturbationDomain period hPeriod) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  c2MatrixRootPerturbationDerivative period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod) variation hVariation

theorem c2IdentityRootBranch_hasFDerivAt
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootPerturbationDomain period hPeriod) :
    HasFDerivAt (c2IdentityRootBranch period hPeriod)
      (c2IdentityRootDerivative period hPeriod variation hVariation)
      variation :=
  c2MatrixRootPerturbationBranch_hasFDerivAt period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod) variation hVariation

theorem c2IdentityRootDerivative_sylvester
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootPerturbationDomain period hPeriod)
    (direction : C2Matrix period hPeriod) :
    c2FiniteMatrixSylvester period hPeriod 4
        (c2IdentityRootBranch period hPeriod variation)
        (c2IdentityRootDerivative period hPeriod variation hVariation
          direction) = direction :=
  c2MatrixRootPerturbationDerivative_sylvester period hPeriod
    (c2IdentityRootField period hPeriod)
    (c2IdentityRootField_regular period hPeriod) variation hVariation direction

/-- Gate marker: the actual C² identity-root branch has the inverse-Sylvester
Fréchet derivative used by the interaction block. -/
theorem canonical_physical_c2_identity_root_derivative_gate
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootPerturbationDomain period hPeriod) :
    HasFDerivAt (c2IdentityRootBranch period hPeriod)
        (c2IdentityRootDerivative period hPeriod variation hVariation)
        variation ∧
      ∀ direction,
        c2FiniteMatrixSylvester period hPeriod 4
            (c2IdentityRootBranch period hPeriod variation)
            (c2IdentityRootDerivative period hPeriod variation hVariation
              direction) = direction :=
  ⟨c2IdentityRootBranch_hasFDerivAt period hPeriod variation hVariation,
    c2IdentityRootDerivative_sylvester period hPeriod variation hVariation⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
end JanusFormal
