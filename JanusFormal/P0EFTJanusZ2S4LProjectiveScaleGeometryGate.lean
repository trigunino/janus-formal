namespace JanusFormal
namespace P0EFTJanusZ2S4LProjectiveScaleGeometryGate

set_option autoImplicit false

structure S4LProjectiveScaleGeometry where
  s4CoverWithRadiusL : Prop
  rp4AntipodalQuotientWithSameL : Prop
  sigmaTubularResolution : Prop
  twoFoldCoverPreserved : Prop
  LDimensionful : Prop
  globalRegularityFixesL : Prop
  boundaryChargeFixesL : Prop
  areaFluxFixesL : Prop
  holonomySpectralFixesL : Prop

def faithfulJanusGeometry (g : S4LProjectiveScaleGeometry) : Prop :=
  g.s4CoverWithRadiusL /\
  g.rp4AntipodalQuotientWithSameL /\
  g.sigmaTubularResolution /\
  g.twoFoldCoverPreserved /\
  g.LDimensionful

def LFixedByCurrentRoutes (g : S4LProjectiveScaleGeometry) : Prop :=
  g.globalRegularityFixesL \/
  g.boundaryChargeFixesL \/
  g.areaFluxFixesL \/
  g.holonomySpectralFixesL

def alphaNoFitReady (g : S4LProjectiveScaleGeometry) : Prop :=
  faithfulJanusGeometry g /\ LFixedByCurrentRoutes g

theorem topology_alone_does_not_fix_dimensionful_L
    (g : S4LProjectiveScaleGeometry)
    (_h : faithfulJanusGeometry g)
    (hNotFixed : Not (LFixedByCurrentRoutes g)) :
    Not (alphaNoFitReady g) := by
  intro h
  exact hNotFixed h.2

theorem if_no_route_fixes_L_then_L_is_state_sector
    (g : S4LProjectiveScaleGeometry)
    (hNoReg : Not g.globalRegularityFixesL)
    (hNoCharge : Not g.boundaryChargeFixesL)
    (hNoArea : Not g.areaFluxFixesL)
    (hNoSpec : Not g.holonomySpectralFixesL) :
    Not (LFixedByCurrentRoutes g) := by
  intro h
  cases h with
  | inl hReg => exact hNoReg hReg
  | inr hRest =>
      cases hRest with
      | inl hCharge => exact hNoCharge hCharge
      | inr hRest2 =>
          cases hRest2 with
          | inl hArea => exact hNoArea hArea
          | inr hSpec => exact hNoSpec hSpec

end P0EFTJanusZ2S4LProjectiveScaleGeometryGate
end JanusFormal
