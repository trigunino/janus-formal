import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D

/-!
# Global typed nonminimal field space

This gate installs distinct global smooth field types for both Abelian
Candidate-A sectors and for the diffeomorphism ghost, antighost and
Nakanishi--Lautrup sectors.  It also
globalizes the universal nonminimal differential

`s c = 0`, `s cbar = B`, `s B = 0`

and proves its square is zero.  It deliberately does not define `s A` or
`s g`: the former is supplied by the paired Abelian gate, while the latter
still requires the global de Donder gauge-fixed chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-! ## Abelian nonminimal fields -/

@[ext]
structure GlobalAbelianGhostField where
  field : SmoothQuotientField period hPeriod GaugeLieAlgebra

@[ext]
structure GlobalAbelianAntighostField where
  field : SmoothQuotientField period hPeriod GaugeLieAlgebra

@[ext]
structure GlobalAbelianNakanishiLautrupField where
  field : SmoothQuotientField period hPeriod GaugeLieAlgebra

def globalAbelianGhostFieldEquiv :
    GlobalAbelianGhostField period hPeriod ≃
      SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun field := field.field
  invFun field := ⟨field⟩
  left_inv field := by cases field; rfl
  right_inv _ := rfl

instance globalAbelianGhostFieldAddCommGroup :
    AddCommGroup (GlobalAbelianGhostField period hPeriod) :=
  Equiv.addCommGroup
    (globalAbelianGhostFieldEquiv period hPeriod)

instance globalAbelianGhostFieldModule :
    Module Real (GlobalAbelianGhostField period hPeriod) :=
  Equiv.module Real
    (globalAbelianGhostFieldEquiv period hPeriod)

def globalAbelianAntighostFieldEquiv :
    GlobalAbelianAntighostField period hPeriod ≃
      SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun field := field.field
  invFun field := ⟨field⟩
  left_inv field := by cases field; rfl
  right_inv _ := rfl

instance globalAbelianAntighostFieldAddCommGroup :
    AddCommGroup (GlobalAbelianAntighostField period hPeriod) :=
  Equiv.addCommGroup
    (globalAbelianAntighostFieldEquiv period hPeriod)

instance globalAbelianAntighostFieldModule :
    Module Real (GlobalAbelianAntighostField period hPeriod) :=
  Equiv.module Real
    (globalAbelianAntighostFieldEquiv period hPeriod)

def globalAbelianNakanishiLautrupFieldEquiv :
    GlobalAbelianNakanishiLautrupField period hPeriod ≃
      SmoothQuotientField period hPeriod GaugeLieAlgebra where
  toFun field := field.field
  invFun field := ⟨field⟩
  left_inv field := by cases field; rfl
  right_inv _ := rfl

instance globalAbelianNakanishiLautrupFieldAddCommGroup :
    AddCommGroup
      (GlobalAbelianNakanishiLautrupField period hPeriod) :=
  Equiv.addCommGroup
    (globalAbelianNakanishiLautrupFieldEquiv period hPeriod)

instance globalAbelianNakanishiLautrupFieldModule :
    Module Real
      (GlobalAbelianNakanishiLautrupField period hPeriod) :=
  Equiv.module Real
    (globalAbelianNakanishiLautrupFieldEquiv period hPeriod)

def zeroGlobalAbelianGhostField :
    GlobalAbelianGhostField period hPeriod :=
  ⟨0⟩

def zeroGlobalAbelianAntighostField :
    GlobalAbelianAntighostField period hPeriod :=
  ⟨0⟩

def zeroGlobalAbelianNakanishiLautrupField :
    GlobalAbelianNakanishiLautrupField period hPeriod :=
  ⟨0⟩

@[ext]
structure GlobalAbelianNonminimalFields where
  ghost : GlobalAbelianGhostField period hPeriod
  antighost : GlobalAbelianAntighostField period hPeriod
  nakanishiLautrup :
    GlobalAbelianNakanishiLautrupField period hPeriod

def globalAbelianNonminimalFieldsEquiv :
    GlobalAbelianNonminimalFields period hPeriod ≃
      GlobalAbelianGhostField period hPeriod ×
        (GlobalAbelianAntighostField period hPeriod ×
          GlobalAbelianNakanishiLautrupField period hPeriod) where
  toFun state :=
    (state.ghost, (state.antighost, state.nakanishiLautrup))
  invFun state :=
    ⟨state.1, state.2.1, state.2.2⟩
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

instance globalAbelianNonminimalFieldsAddCommGroup :
    AddCommGroup (GlobalAbelianNonminimalFields period hPeriod) :=
  Equiv.addCommGroup
    (globalAbelianNonminimalFieldsEquiv period hPeriod)

instance globalAbelianNonminimalFieldsModule :
    Module Real (GlobalAbelianNonminimalFields period hPeriod) :=
  Equiv.module Real
    (globalAbelianNonminimalFieldsEquiv period hPeriod)

def zeroGlobalAbelianNonminimalFields :
    GlobalAbelianNonminimalFields period hPeriod where
  ghost := zeroGlobalAbelianGhostField period hPeriod
  antighost := zeroGlobalAbelianAntighostField period hPeriod
  nakanishiLautrup :=
    zeroGlobalAbelianNakanishiLautrupField period hPeriod

def globalAbelianNonminimalBRST
    (state : GlobalAbelianNonminimalFields period hPeriod) :
    GlobalAbelianNonminimalFields period hPeriod where
  ghost := zeroGlobalAbelianGhostField period hPeriod
  antighost := ⟨state.nakanishiLautrup.field⟩
  nakanishiLautrup :=
    zeroGlobalAbelianNakanishiLautrupField period hPeriod

theorem globalAbelianNonminimalBRST_square_zero
    (state : GlobalAbelianNonminimalFields period hPeriod) :
    globalAbelianNonminimalBRST period hPeriod
        (globalAbelianNonminimalBRST period hPeriod state) =
      zeroGlobalAbelianNonminimalFields period hPeriod :=
  rfl

/-! ## Diffeomorphism nonminimal fields -/

@[ext]
structure GlobalDiffeomorphismGhostField where
  field : SmoothTangentField period hPeriod

@[ext]
structure GlobalDiffeomorphismAntighostField where
  field : SmoothTangentField period hPeriod

@[ext]
structure GlobalDiffeomorphismNakanishiLautrupField where
  field : SmoothTangentField period hPeriod

def globalDiffeomorphismGhostFieldEquiv :
    GlobalDiffeomorphismGhostField period hPeriod ≃
      SmoothTangentField period hPeriod where
  toFun field := field.field
  invFun field := ⟨field⟩
  left_inv field := by cases field; rfl
  right_inv _ := rfl

instance globalDiffeomorphismGhostFieldAddCommGroup :
    AddCommGroup
      (GlobalDiffeomorphismGhostField period hPeriod) :=
  Equiv.addCommGroup
    (globalDiffeomorphismGhostFieldEquiv period hPeriod)

instance globalDiffeomorphismGhostFieldModule :
    Module Real
      (GlobalDiffeomorphismGhostField period hPeriod) :=
  Equiv.module Real
    (globalDiffeomorphismGhostFieldEquiv period hPeriod)

def globalDiffeomorphismAntighostFieldEquiv :
    GlobalDiffeomorphismAntighostField period hPeriod ≃
      SmoothTangentField period hPeriod where
  toFun field := field.field
  invFun field := ⟨field⟩
  left_inv field := by cases field; rfl
  right_inv _ := rfl

instance globalDiffeomorphismAntighostFieldAddCommGroup :
    AddCommGroup
      (GlobalDiffeomorphismAntighostField period hPeriod) :=
  Equiv.addCommGroup
    (globalDiffeomorphismAntighostFieldEquiv period hPeriod)

instance globalDiffeomorphismAntighostFieldModule :
    Module Real
      (GlobalDiffeomorphismAntighostField period hPeriod) :=
  Equiv.module Real
    (globalDiffeomorphismAntighostFieldEquiv period hPeriod)

def globalDiffeomorphismNakanishiLautrupFieldEquiv :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod ≃
      SmoothTangentField period hPeriod where
  toFun field := field.field
  invFun field := ⟨field⟩
  left_inv field := by cases field; rfl
  right_inv _ := rfl

instance globalDiffeomorphismNakanishiLautrupFieldAddCommGroup :
    AddCommGroup
      (GlobalDiffeomorphismNakanishiLautrupField period hPeriod) :=
  Equiv.addCommGroup
    (globalDiffeomorphismNakanishiLautrupFieldEquiv period hPeriod)

instance globalDiffeomorphismNakanishiLautrupFieldModule :
    Module Real
      (GlobalDiffeomorphismNakanishiLautrupField period hPeriod) :=
  Equiv.module Real
    (globalDiffeomorphismNakanishiLautrupFieldEquiv period hPeriod)

private def zeroGlobalSmoothTangentField :
    SmoothTangentField period hPeriod where
  toFun := fun _ => 0
  contMDiff_toFun := Bundle.contMDiff_zeroSection Real _

def zeroGlobalDiffeomorphismGhostField :
    GlobalDiffeomorphismGhostField period hPeriod :=
  ⟨zeroGlobalSmoothTangentField period hPeriod⟩

def zeroGlobalDiffeomorphismAntighostField :
    GlobalDiffeomorphismAntighostField period hPeriod :=
  ⟨zeroGlobalSmoothTangentField period hPeriod⟩

def zeroGlobalDiffeomorphismNakanishiLautrupField :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod :=
  ⟨zeroGlobalSmoothTangentField period hPeriod⟩

@[ext]
structure GlobalDiffeomorphismNonminimalFields where
  ghost : GlobalDiffeomorphismGhostField period hPeriod
  antighost : GlobalDiffeomorphismAntighostField period hPeriod
  nakanishiLautrup :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod

def globalDiffeomorphismNonminimalFieldsEquiv :
    GlobalDiffeomorphismNonminimalFields period hPeriod ≃
      GlobalDiffeomorphismGhostField period hPeriod ×
        (GlobalDiffeomorphismAntighostField period hPeriod ×
          GlobalDiffeomorphismNakanishiLautrupField period hPeriod) where
  toFun state :=
    (state.ghost, (state.antighost, state.nakanishiLautrup))
  invFun state :=
    ⟨state.1, state.2.1, state.2.2⟩
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

instance globalDiffeomorphismNonminimalFieldsAddCommGroup :
    AddCommGroup
      (GlobalDiffeomorphismNonminimalFields period hPeriod) :=
  Equiv.addCommGroup
    (globalDiffeomorphismNonminimalFieldsEquiv period hPeriod)

instance globalDiffeomorphismNonminimalFieldsModule :
    Module Real
      (GlobalDiffeomorphismNonminimalFields period hPeriod) :=
  Equiv.module Real
    (globalDiffeomorphismNonminimalFieldsEquiv period hPeriod)

def zeroGlobalDiffeomorphismNonminimalFields :
    GlobalDiffeomorphismNonminimalFields period hPeriod where
  ghost := zeroGlobalDiffeomorphismGhostField period hPeriod
  antighost := zeroGlobalDiffeomorphismAntighostField period hPeriod
  nakanishiLautrup :=
    zeroGlobalDiffeomorphismNakanishiLautrupField period hPeriod

def globalDiffeomorphismNonminimalBRST
    (state : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    GlobalDiffeomorphismNonminimalFields period hPeriod where
  ghost := zeroGlobalDiffeomorphismGhostField period hPeriod
  antighost := ⟨state.nakanishiLautrup.field⟩
  nakanishiLautrup :=
    zeroGlobalDiffeomorphismNakanishiLautrupField period hPeriod

theorem globalDiffeomorphismNonminimalBRST_square_zero
    (state : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalDiffeomorphismNonminimalBRST period hPeriod
        (globalDiffeomorphismNonminimalBRST period hPeriod state) =
      zeroGlobalDiffeomorphismNonminimalFields period hPeriod :=
  rfl

/-! ## Combined global extension -/

@[ext]
structure GlobalTypedNonminimalFields where
  abelian :
    Sector → GlobalAbelianNonminimalFields period hPeriod
  diffeomorphism :
    GlobalDiffeomorphismNonminimalFields period hPeriod

def globalTypedNonminimalFieldsEquiv :
    GlobalTypedNonminimalFields period hPeriod ≃
      (Sector → GlobalAbelianNonminimalFields period hPeriod) ×
        GlobalDiffeomorphismNonminimalFields period hPeriod where
  toFun state := (state.abelian, state.diffeomorphism)
  invFun state := ⟨state.1, state.2⟩
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

instance globalTypedNonminimalFieldsAddCommGroup :
    AddCommGroup (GlobalTypedNonminimalFields period hPeriod) :=
  Equiv.addCommGroup
    (globalTypedNonminimalFieldsEquiv period hPeriod)

instance globalTypedNonminimalFieldsModule :
    Module Real (GlobalTypedNonminimalFields period hPeriod) :=
  Equiv.module Real
    (globalTypedNonminimalFieldsEquiv period hPeriod)

def zeroGlobalTypedNonminimalFields :
    GlobalTypedNonminimalFields period hPeriod where
  abelian := fun _ =>
    zeroGlobalAbelianNonminimalFields period hPeriod
  diffeomorphism :=
    zeroGlobalDiffeomorphismNonminimalFields period hPeriod

def globalTypedNonminimalBRST
    (state : GlobalTypedNonminimalFields period hPeriod) :
    GlobalTypedNonminimalFields period hPeriod where
  abelian := fun sector =>
    globalAbelianNonminimalBRST period hPeriod (state.abelian sector)
  diffeomorphism :=
    globalDiffeomorphismNonminimalBRST
      period hPeriod state.diffeomorphism

theorem globalTypedNonminimalBRST_square_zero
    (state : GlobalTypedNonminimalFields period hPeriod) :
    globalTypedNonminimalBRST period hPeriod
        (globalTypedNonminimalBRST period hPeriod state) =
      zeroGlobalTypedNonminimalFields period hPeriod :=
  rfl

/-- The two outer-sector Abelian ghosts, in the exact paired type already
used by the physical gauge complex. -/
def GlobalTypedNonminimalFields.abelianGhostPair
    (state : GlobalTypedNonminimalFields period hPeriod) :
    PhysicalPairedGaugeGhost period hPeriod :=
  (state.abelian .plus |>.ghost.field,
    state.abelian .minus |>.ghost.field)

/-- The independent paired Abelian antighosts. -/
def GlobalTypedNonminimalFields.abelianAntighostPair
    (state : GlobalTypedNonminimalFields period hPeriod) :
    PhysicalPairedGaugeGhost period hPeriod :=
  (state.abelian .plus |>.antighost.field,
    state.abelian .minus |>.antighost.field)

/-- The independent paired Abelian Nakanishi--Lautrup fields. -/
def GlobalTypedNonminimalFields.abelianNakanishiLautrupPair
    (state : GlobalTypedNonminimalFields period hPeriod) :
    PhysicalPairedGaugeGhost period hPeriod :=
  (state.abelian .plus |>.nakanishiLautrup.field,
    state.abelian .minus |>.nakanishiLautrup.field)

@[simp]
theorem globalTypedNonminimalBRST_abelianGhostPair
    (state : GlobalTypedNonminimalFields period hPeriod) :
    (globalTypedNonminimalBRST period hPeriod state).abelianGhostPair
        period hPeriod =
      0 :=
  rfl

@[simp]
theorem globalTypedNonminimalBRST_abelianAntighostPair
    (state : GlobalTypedNonminimalFields period hPeriod) :
    (globalTypedNonminimalBRST period hPeriod state).abelianAntighostPair
        period hPeriod =
      state.abelianNakanishiLautrupPair period hPeriod :=
  rfl

@[simp]
theorem globalTypedNonminimalBRST_abelianNakanishiLautrupPair
    (state : GlobalTypedNonminimalFields period hPeriod) :
    (globalTypedNonminimalBRST period hPeriod state).abelianNakanishiLautrupPair
        period hPeriod =
      0 :=
  rfl

/-- Honest global gauge-fixed field extension.  The covariant physical
configuration is retained verbatim and the nine nonminimal species are added
as distinct smooth fields. -/
@[ext]
structure GlobalGaugeFixedFieldConfiguration where
  physical : GlobalFieldConfiguration period hPeriod
  nonminimal : GlobalTypedNonminimalFields period hPeriod

/-- Obsolete coefficient ghost/auxiliary directions retained by the legacy
physical packet. -/
abbrev GlobalLegacyNonminimalDirection :=
  (SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber) ×
    (SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber)

/-- Projection onto the obsolete coefficient ghost/auxiliary directions. -/
def globalPhysicalLegacyNonminimalProjectionLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      GlobalLegacyNonminimalDirection period hPeriod where
  toFun := fun variation =>
    (variation.completeVariation.independent.ghosts,
      variation.completeVariation.independent.auxiliaries)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Minimal physical tangent with the duplicate legacy nonminimal directions
held fixed. -/
abbrev GlobalMinimalPhysicalFieldTangent
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  LinearMap.ker
    (globalPhysicalLegacyNonminimalProjectionLinearMap
      period hPeriod configuration)

/-- The corrected tangent is a genuine linear subspace of the previous
D10-free physical tangent. -/
def globalMinimalPhysicalTangentInclusionLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.ker
    (globalPhysicalLegacyNonminimalProjectionLinearMap
      period hPeriod configuration)).subtype

theorem globalMinimalPhysicalTangentInclusion_injective
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Function.Injective
      (globalMinimalPhysicalTangentInclusionLinearMap
        period hPeriod configuration) :=
  Subtype.val_injective

@[simp]
theorem GlobalMinimalPhysicalFieldTangent.legacyGhosts_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation :
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    variation.1.completeVariation.independent.ghosts = 0 := by
  have h :
      (variation.1.completeVariation.independent.ghosts,
        variation.1.completeVariation.independent.auxiliaries) =
        (0 : GlobalLegacyNonminimalDirection period hPeriod) :=
    variation.2
  exact congrArg Prod.fst h

@[simp]
theorem GlobalMinimalPhysicalFieldTangent.legacyAuxiliaries_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation :
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    variation.1.completeVariation.independent.auxiliaries = 0 := by
  have h :
      (variation.1.completeVariation.independent.ghosts,
        variation.1.completeVariation.independent.auxiliaries) =
        (0 : GlobalLegacyNonminimalDirection period hPeriod) :=
    variation.2
  exact congrArg Prod.snd h

/-- D10-free physical tangent enlarged by the nine typed nonminimal smooth
directions, without duplicating the legacy ghost/auxiliary packet.  No
analytic norm is asserted at this field-space stage. -/
abbrev GlobalGaugeFixedPhysicalFieldTangent
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical ×
    GlobalTypedNonminimalFields period hPeriod

/-- Linear projection back to the nonduplicated D10-free physical tangent. -/
def globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration.physical :=
  LinearMap.fst Real
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (GlobalTypedNonminimalFields period hPeriod)

/-- Linear projection to the nine typed nonminimal directions. -/
def globalGaugeFixedPhysicalTangentNonminimalProjectionLinearMap
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      GlobalTypedNonminimalFields period hPeriod :=
  LinearMap.snd Real
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (GlobalTypedNonminimalFields period hPeriod)

/-- Canonical linear inclusion of the physical tangent with zero nonminimal
variation. -/
def globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration.physical →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  LinearMap.inl Real
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (GlobalTypedNonminimalFields period hPeriod)

@[simp]
theorem globalGaugeFixedPhysicalTangentPhysicalProjection_inclusion
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (direction :
      GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration.physical) :
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
        period hPeriod configuration
        (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
          period hPeriod configuration direction) =
      direction :=
  rfl

theorem globalGaugeFixedPhysicalTangentPhysicalInclusion_injective
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
      (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
        period hPeriod configuration) :=
  Function.LeftInverse.injective
    (globalGaugeFixedPhysicalTangentPhysicalProjection_inclusion
      period hPeriod configuration)

def zeroGlobalGaugeFixedPhysicalFieldTangent
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalGaugeFixedPhysicalFieldTangent
      period hPeriod configuration :=
  (0, zeroGlobalTypedNonminimalFields period hPeriod)

theorem globalGaugeFixedPhysicalFieldTangent_nonempty
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Nonempty
      (GlobalGaugeFixedPhysicalFieldTangent
        period hPeriod configuration) :=
  ⟨zeroGlobalGaugeFixedPhysicalFieldTangent
    period hPeriod configuration⟩

def globalGaugeFixedFieldConfigurationPhysicalProjection
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalFieldConfiguration period hPeriod :=
  configuration.physical

def globalFieldConfigurationZeroNonminimalInclusion
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalGaugeFixedFieldConfiguration period hPeriod where
  physical := configuration
  nonminimal := zeroGlobalTypedNonminimalFields period hPeriod

@[simp]
theorem globalGaugeFixedFieldConfigurationPhysicalProjection_zeroInclusion
    (configuration : GlobalFieldConfiguration period hPeriod) :
    globalGaugeFixedFieldConfigurationPhysicalProjection period hPeriod
        (globalFieldConfigurationZeroNonminimalInclusion
          period hPeriod configuration) =
      configuration :=
  rfl

theorem globalFieldConfigurationZeroNonminimalInclusion_injective :
    Function.Injective
      (globalFieldConfigurationZeroNonminimalInclusion period hPeriod) :=
  Function.LeftInverse.injective
    (globalGaugeFixedFieldConfigurationPhysicalProjection_zeroInclusion
      period hPeriod)

def zeroGlobalGaugeFixedFieldConfiguration
    (geometry : GlobalCandidateAGeometry period hPeriod) :
    GlobalGaugeFixedFieldConfiguration period hPeriod :=
  globalFieldConfigurationZeroNonminimalInclusion period hPeriod
    (zeroGlobalFieldConfiguration period hPeriod geometry)

theorem globalGaugeFixedFieldConfiguration_nonempty
    (geometry : GlobalCandidateAGeometry period hPeriod) :
    Nonempty (GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  ⟨zeroGlobalGaugeFixedFieldConfiguration period hPeriod geometry⟩

end
end P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
end JanusFormal
