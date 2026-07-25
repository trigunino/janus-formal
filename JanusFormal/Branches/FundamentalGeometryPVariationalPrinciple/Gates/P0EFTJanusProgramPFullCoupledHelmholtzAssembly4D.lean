import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActionClassification4D

/-!
# Full coupled Noether/PT/Helmholtz assembly

This gate performs the formal assembly for the nine Program-P action blocks:
Candidate A, matter, Robin, LL, two Einstein--Hilbert blocks, two Maxwell
blocks and finite BV.  Once these concrete blocks are represented on one
common normed configuration chart and are `C²`, their sum has the genuine
nonlinear Helmholtz symmetry.  PT or gauge invariance also assembles
componentwise.

The theorem does not manufacture the common Frechet chart from unrelated
one-parameter variation records.  That geometric identification is the exact
remaining bridge for the present concrete full action API.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusConvexHelmholtzReconstruction

universe u

/-- Nine scalar functional blocks on one common configuration chart. -/
structure FullCoupledActionBlocks
    (Configuration : Type u) where
  candidateA : Configuration → ℝ
  matter : Configuration → ℝ
  robin : Configuration → ℝ
  ll : Configuration → ℝ
  einsteinHilbertPlus : Configuration → ℝ
  einsteinHilbertMinus : Configuration → ℝ
  maxwellPlus : Configuration → ℝ
  maxwellMinus : Configuration → ℝ
  finiteBV : Configuration → ℝ

/-- The actual summed functional. -/
def fullCoupledAction
    {Configuration : Type u}
    (blocks : FullCoupledActionBlocks Configuration)
    (configuration : Configuration) : ℝ :=
  ((((((((blocks.candidateA configuration +
    blocks.matter configuration) +
    blocks.robin configuration) +
    blocks.ll configuration) +
    blocks.einsteinHilbertPlus configuration) +
    blocks.einsteinHilbertMinus configuration) +
    blocks.maxwellPlus configuration) +
    blocks.maxwellMinus configuration) +
    blocks.finiteBV configuration)

/-- Genuine `C²` data for every block on the same chart. -/
structure FullCoupledC2At
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (blocks : FullCoupledActionBlocks Configuration)
    (configuration : Configuration) : Prop where
  candidateA : ContDiffAt ℝ 2 blocks.candidateA configuration
  matter : ContDiffAt ℝ 2 blocks.matter configuration
  robin : ContDiffAt ℝ 2 blocks.robin configuration
  ll : ContDiffAt ℝ 2 blocks.ll configuration
  einsteinHilbertPlus :
    ContDiffAt ℝ 2 blocks.einsteinHilbertPlus configuration
  einsteinHilbertMinus :
    ContDiffAt ℝ 2 blocks.einsteinHilbertMinus configuration
  maxwellPlus : ContDiffAt ℝ 2 blocks.maxwellPlus configuration
  maxwellMinus : ContDiffAt ℝ 2 blocks.maxwellMinus configuration
  finiteBV : ContDiffAt ℝ 2 blocks.finiteBV configuration

/-- Smoothness of the complete action is a theorem, not an extra field. -/
theorem fullCoupledAction_contDiffAt
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (blocks : FullCoupledActionBlocks Configuration)
    (configuration : Configuration)
    (hC2 : FullCoupledC2At blocks configuration) :
    ContDiffAt ℝ 2 (fullCoupledAction blocks) configuration := by
  exact ((((((((hC2.candidateA.add hC2.matter).add hC2.robin).add
    hC2.ll).add hC2.einsteinHilbertPlus).add
    hC2.einsteinHilbertMinus).add hC2.maxwellPlus).add
    hC2.maxwellMinus).add hC2.finiteBV)

/-- Full nonlinear Helmholtz reciprocity for the actual summed action. -/
theorem fullCoupledAction_helmholtz
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (blocks : FullCoupledActionBlocks Configuration)
    (configuration : Configuration)
    (hC2 : FullCoupledC2At blocks configuration) :
    HelmholtzJacobianAt
      (actionGradient (fullCoupledAction blocks)) configuration :=
  action_gradient_helmholtz_at
    (fullCoupledAction blocks) configuration
      (fullCoupledAction_contDiffAt blocks configuration hC2)

/-- Invariance of all nine blocks under one transformation. -/
structure FullCoupledInvariantUnder
    {Configuration Transformation : Type*}
    (blocks : FullCoupledActionBlocks Configuration)
    (transform : Transformation → Configuration → Configuration) : Prop where
  candidateA : ∀ symmetry configuration,
    blocks.candidateA (transform symmetry configuration) =
      blocks.candidateA configuration
  matter : ∀ symmetry configuration,
    blocks.matter (transform symmetry configuration) =
      blocks.matter configuration
  robin : ∀ symmetry configuration,
    blocks.robin (transform symmetry configuration) =
      blocks.robin configuration
  ll : ∀ symmetry configuration,
    blocks.ll (transform symmetry configuration) =
      blocks.ll configuration
  einsteinHilbertPlus : ∀ symmetry configuration,
    blocks.einsteinHilbertPlus (transform symmetry configuration) =
      blocks.einsteinHilbertPlus configuration
  einsteinHilbertMinus : ∀ symmetry configuration,
    blocks.einsteinHilbertMinus (transform symmetry configuration) =
      blocks.einsteinHilbertMinus configuration
  maxwellPlus : ∀ symmetry configuration,
    blocks.maxwellPlus (transform symmetry configuration) =
      blocks.maxwellPlus configuration
  maxwellMinus : ∀ symmetry configuration,
    blocks.maxwellMinus (transform symmetry configuration) =
      blocks.maxwellMinus configuration
  finiteBV : ∀ symmetry configuration,
    blocks.finiteBV (transform symmetry configuration) =
      blocks.finiteBV configuration

/-- Gauge or PT invariance assembles exactly from the component laws. -/
theorem fullCoupledAction_invariant
    {Configuration Transformation : Type*}
    (blocks : FullCoupledActionBlocks Configuration)
    (transform : Transformation → Configuration → Configuration)
    (hInvariant : FullCoupledInvariantUnder blocks transform)
    (symmetry : Transformation)
    (configuration : Configuration) :
    fullCoupledAction blocks (transform symmetry configuration) =
      fullCoupledAction blocks configuration := by
  simp only [fullCoupledAction]
  rw [hInvariant.candidateA, hInvariant.matter, hInvariant.robin,
    hInvariant.ll, hInvariant.einsteinHilbertPlus,
    hInvariant.einsteinHilbertMinus, hInvariant.maxwellPlus,
    hInvariant.maxwellMinus, hInvariant.finiteBV]

/-- Exact interface still needed to identify the current concrete
one-parameter action API with the common Frechet action above.  Its fields are
equalities and regularity statements, not unnamed truth flags. -/
structure ConcreteFullActionFrechetBridge
    (ConcreteConfiguration : Type*)
    (ConcreteVariation : Type*)
    (concreteActionCurve :
      ConcreteConfiguration → ConcreteVariation → ℝ → ℝ) where
  Configuration : Type*
  normedAddCommGroup : NormedAddCommGroup Configuration
  normedSpace : NormedSpace ℝ Configuration
  encodeConfiguration : ConcreteConfiguration → Configuration
  encodeVariation : ConcreteVariation → Configuration
  blocks : FullCoupledActionBlocks Configuration
  affineCurve :
    ConcreteConfiguration → ConcreteVariation → ℝ → Configuration
  affineCurve_zero : ∀ configuration variation,
    affineCurve configuration variation 0 =
      encodeConfiguration configuration
  curve_agreement : ∀ configuration variation parameter,
    fullCoupledAction blocks
        (affineCurve configuration variation parameter) =
      concreteActionCurve configuration variation parameter
  blocks_c2 : ∀ configuration,
    @FullCoupledC2At Configuration normedAddCommGroup normedSpace
      blocks (encodeConfiguration configuration)

end

end P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
end JanusFormal
