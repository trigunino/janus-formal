import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D

/-!
# Global Clifford action on primitive SpinC sections

The fixed doubled Clifford generators commute with both ingredients of every
primitive SpinC transition: the normal-root monodromy and the monopole phase.
They therefore act on genuine smooth sections of the actual primitive bundle,
not only on local coordinates or the cover model.

This gate constructs that global section action and records its exact local
value. It introduces no new bundle, trivialization or field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCCliffordSection4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Clifford multiplication commutes with the complete primitive SpinC
coordinate change. -/
theorem d9PrimitiveSpinCCoordChange_clifford
    (choice : NormalRootChoice)
    (direction : Fin 3)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCCoordChange period hPeriod choice first second base
        (d9DoubledMatterFiberCliffordGamma direction matter) =
      d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCCoordChange period hPeriod choice first second base
          matter) := by
  unfold d9PrimitiveSpinCCoordChange
  rw [d9DoubledMatterFiberCliffordGamma_monodromy,
    d9PrimitiveSpinCPhaseAction_clifford]

/-- Apply one fixed Clifford generator to every local representative. -/
def d9PrimitiveSpinCCliffordLocalGaugeFamily
    (choice : NormalRootChoice) (direction : Fin 3)
    (family : SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index base :=
    d9DoubledMatterFiberCliffordGamma direction
      (family.localValue index base)
  contMDiffOn_localValue index :=
    (d9DoubledMatterFiberCliffordGammaCLM direction).contDiff.contMDiff
      |>.comp_contMDiffOn (family.contMDiffOn_localValue index)
  coordChange_localValue first second base hBase := by
    rw [d9PrimitiveSpinCCoordChange_clifford,
      family.coordChange_localValue first second base hBase]

/-- Genuine global Clifford transform of a primitive smooth section. -/
def d9PrimitiveSpinCCliffordSection
    (choice : NormalRootChoice) (direction : Fin 3)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice :=
  (d9PrimitiveSpinCCliffordLocalGaugeFamily period hPeriod choice direction
    (d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice
      state)).toSmoothSection period hPeriod choice

/-- Local gauge recovery after Clifford multiplication is exactly Clifford
multiplication of the recovered original gauge. -/
theorem d9PrimitiveSpinCCliffordSection_localValue
    (choice : NormalRootChoice) (direction : Fin 3)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice
        (d9PrimitiveSpinCCliffordSection period hPeriod choice direction state)
        index base =
      d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice state
          index base) := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily period hPeriod choice state
  let transformed :=
    d9PrimitiveSpinCCliffordLocalGaugeFamily period hPeriod choice direction
      family
  change
    ((d9PrimitiveSpinCVectorBundleCore period hPeriod choice).localTriv index
      (primitiveSpinCBundleSection period hPeriod choice transformed base)).2 =
      transformed.localValue index base
  exact primitiveSpinCBundleSection_localTriv
    period hPeriod choice transformed index base hBase

@[simp]
theorem d9PrimitiveSpinCCliffordSection_apply
    (choice : NormalRootChoice) (direction : Fin 3)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCCliffordSection period hPeriod choice direction state base =
      d9DoubledMatterFiberCliffordGamma direction (state base) := by
  let index :=
    (d9PrimitiveSpinCVectorBundleCore period hPeriod choice).indexAt base
  have hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    (d9PrimitiveSpinCVectorBundleCore period hPeriod choice).mem_baseSet_at base
  change
    (d9PrimitiveSpinCVectorBundleCore period hPeriod choice).coordChange
        index index base
        (d9DoubledMatterFiberCliffordGamma direction (state base)) =
      d9DoubledMatterFiberCliffordGamma direction (state base)
  exact
    (d9PrimitiveSpinCVectorBundleCore period hPeriod choice).coordChange_self
      index base hBase _

/-- Clifford multiplication is real-linear on genuine smooth sections. -/
def d9PrimitiveSpinCCliffordSectionLinearMap
    (choice : NormalRootChoice) (direction : Fin 3) :
    D9PrimitiveSpinCSmoothSection period hPeriod choice →ₗ[Real]
      D9PrimitiveSpinCSmoothSection period hPeriod choice where
  toFun := d9PrimitiveSpinCCliffordSection period hPeriod choice direction
  map_add' first second := by
    ext base
    simp [map_add]
  map_smul' scalar state := by
    ext base
    simp [map_smul]

/-- Public certificate for global Clifford action on the primitive bundle. -/
structure ProgramPPrimitiveSpinCCliffordSectionCertificate4D : Prop where
  localAction : ∀ choice direction state index base,
    base ∈ d9PrimitiveSpinCBaseSet period hPeriod index →
    d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice
        (d9PrimitiveSpinCCliffordSection period hPeriod choice direction state)
        index base =
      d9DoubledMatterFiberCliffordGamma direction
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice state
          index base)

/-- Existing transition covariance supplies the certificate unconditionally. -/
def programPPrimitiveSpinCCliffordSectionCertificate4D :
    ProgramPPrimitiveSpinCCliffordSectionCertificate4D period hPeriod where
  localAction := d9PrimitiveSpinCCliffordSection_localValue period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCCliffordSection4D
end JanusFormal
