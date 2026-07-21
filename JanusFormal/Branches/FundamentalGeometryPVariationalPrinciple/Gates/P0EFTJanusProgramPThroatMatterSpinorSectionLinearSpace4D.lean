import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D

/-! # Linear space of smooth throat matter-spinor sections -/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase := MappingTorus (fixedEquatorData period hPeriod)
private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

theorem throatAmbientPinCMatterCoordChange_add
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : ThroatBase period hPeriod) (left right : MatterFiber) :
    throatAmbientPinCMatterCoordChange period hPeriod choice
        first second base (left + right) =
      throatAmbientPinCMatterCoordChange period hPeriod choice
          first second base left +
        throatAmbientPinCMatterCoordChange period hPeriod choice
          first second base right := by
  unfold throatAmbientPinCMatterCoordChange
    canonicalAmbientPinCMatterCoordChange
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, map_add]
  unfold canonicalAmbientPinCHalfSpinorCoordChange
    canonicalAmbientPinCSpinorCoordChange
  rw [show ambientHalfSpinorEmbed
        (matterFiberHalfSpinorLinearEquiv left +
          matterFiberHalfSpinorLinearEquiv right) =
      ambientHalfSpinorEmbed (matterFiberHalfSpinorLinearEquiv left) +
        ambientHalfSpinorEmbed (matterFiberHalfSpinorLinearEquiv right) by
      exact ambientHalfSpinorEmbedLinear.map_add _ _,
    Matrix.mulVec_add]
  change ambientHalfSpinorProjectLinear (_ + _) =
    ambientHalfSpinorProjectLinear _ + ambientHalfSpinorProjectLinear _
  rw [map_add]

theorem throatAmbientPinCMatterCoordChange_neg
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : ThroatBase period hPeriod) (matter : MatterFiber) :
    throatAmbientPinCMatterCoordChange period hPeriod choice
        first second base (-matter) =
      -throatAmbientPinCMatterCoordChange period hPeriod choice
        first second base matter := by
  have hAdd := throatAmbientPinCMatterCoordChange_add period hPeriod choice
    first second base (-matter) matter
  rw [neg_add_cancel,
    P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D.throatAmbientPinCMatterCoordChange_zero]
    at hAdd
  exact eq_neg_of_add_eq_zero_left hAdd.symm

theorem throatAmbientPinCMatterCoordChange_smul
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : ThroatBase period hPeriod) (scalar : Real)
    (matter : MatterFiber) :
    throatAmbientPinCMatterCoordChange period hPeriod choice
        first second base (scalar • matter) =
      scalar • throatAmbientPinCMatterCoordChange period hPeriod choice
        first second base matter := by
  unfold throatAmbientPinCMatterCoordChange
    canonicalAmbientPinCMatterCoordChange
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, map_smul]
  unfold canonicalAmbientPinCHalfSpinorCoordChange
    canonicalAmbientPinCSpinorCoordChange
  rw [show ambientHalfSpinorEmbed
        (scalar • matterFiberHalfSpinorLinearEquiv matter) =
      scalar • ambientHalfSpinorEmbed
        (matterFiberHalfSpinorLinearEquiv matter) by
      funext index
      fin_cases index <;> simp [ambientHalfSpinorEmbed],
    Matrix.mulVec_smul]
  change ambientHalfSpinorProjectLinear (scalar • _) =
    scalar • ambientHalfSpinorProjectLinear _
  exact ambientHalfSpinorProjectLinear.map_smul_of_tower scalar _

instance (choice : NormalRootChoice) :
    Add (SmoothThroatMatterSpinorLift period hPeriod choice) where
  add first second :=
    { toFun := fun anchor => first anchor + second anchor
      contMDiff_toFun :=
        first.contMDiff_toFun.add second.contMDiff_toFun
      deck_equivariant := by
        intro winding anchor
        rw [first.deck_equivariant, second.deck_equivariant,
          ← throatAmbientPinCMatterCoordChange_add] }

instance (choice : NormalRootChoice) :
    Neg (SmoothThroatMatterSpinorLift period hPeriod choice) where
  neg field :=
    { toFun := fun anchor => -field anchor
      contMDiff_toFun := field.contMDiff_toFun.neg
      deck_equivariant := by
        intro winding anchor
        rw [field.deck_equivariant,
          ← throatAmbientPinCMatterCoordChange_neg] }

instance (choice : NormalRootChoice) :
    AddCommGroup (SmoothThroatMatterSpinorLift period hPeriod choice) where
  add_assoc := by intro first second third; ext anchor; exact add_assoc _ _ _
  zero_add := by intro field; ext anchor; exact zero_add _
  add_zero := by intro field; ext anchor; exact add_zero _
  nsmul := nsmulRec
  add_comm := by intro first second; ext anchor; exact add_comm _ _
  neg_add_cancel := by intro field; ext anchor; exact neg_add_cancel _
  sub_eq_add_neg := by intro first second; ext anchor; exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance (choice : NormalRootChoice) :
    SMul Real (SmoothThroatMatterSpinorLift period hPeriod choice) where
  smul scalar field :=
    { toFun := fun anchor => scalar • field anchor
      contMDiff_toFun := by
        have hScalar : ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
            (fun _ : ThroatCover period hPeriod => scalar) := contMDiff_const
        exact hScalar.smul field.contMDiff_toFun
      deck_equivariant := by
        intro winding anchor
        rw [field.deck_equivariant,
          ← throatAmbientPinCMatterCoordChange_smul] }

instance (choice : NormalRootChoice) :
    Module Real (SmoothThroatMatterSpinorLift period hPeriod choice) where
  one_smul := by
    intro field
    apply SmoothThroatMatterSpinorLift.ext
    intro anchor
    change (1 : Real) • field anchor = field anchor
    exact one_smul Real _
  mul_smul := by
    intro first second field
    apply SmoothThroatMatterSpinorLift.ext
    intro anchor
    change (first * second) • field anchor = first • second • field anchor
    exact mul_smul _ _ _
  smul_add := by
    intro scalar first second
    apply SmoothThroatMatterSpinorLift.ext
    intro anchor
    change scalar • (first anchor + second anchor) =
      scalar • first anchor + scalar • second anchor
    exact smul_add _ _ _
  smul_zero := by
    intro scalar
    apply SmoothThroatMatterSpinorLift.ext
    intro anchor
    change scalar • (0 : MatterFiber) = 0
    exact smul_zero _
  add_smul := by
    intro first second field
    apply SmoothThroatMatterSpinorLift.ext
    intro anchor
    change (first + second) • field anchor =
      first • field anchor + second • field anchor
    exact add_smul _ _ _
  zero_smul := by
    intro field
    apply SmoothThroatMatterSpinorLift.ext
    intro anchor
    change (0 : Real) • field anchor = 0
    exact zero_smul Real _

structure ProgramPThroatMatterSpinorSectionLinearSpaceCertificate4D where
  choice : NormalRootChoice
  sectionModule : Module Real
    (SmoothThroatMatterSpinorLift period hPeriod choice)

def programPThroatMatterSpinorSectionLinearSpaceCertificate4D :
    ProgramPThroatMatterSpinorSectionLinearSpaceCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  sectionModule := inferInstance

theorem programPThroatMatterSpinorSectionLinearSpaceCertificate4D_nonempty :
    Nonempty (ProgramPThroatMatterSpinorSectionLinearSpaceCertificate4D
      period hPeriod) :=
  ⟨programPThroatMatterSpinorSectionLinearSpaceCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D
end JanusFormal
