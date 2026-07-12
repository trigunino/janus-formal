import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusZ4DiracAlphaLock
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusBimetricZ4MassRadiusLock
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusSeparatedCentralInternalZ4

namespace JanusFormal
namespace P0EFTJanusSeparatedChargeStabilizerSynthesis

set_option autoImplicit false

open P0EFTJanusZ4DiracAlphaLock
open P0EFTJanusBimetricZ4MassRadiusLock
open P0EFTJanusSeparatedCentralInternalZ4

/--
Two-sector D7 synthesis:

* the central Pin-Z4 fermionic sector controls eta, the primitive Dirac gap and
  the LL charge/radius lock;
* an independent internal-Z4 bosonic sector controls the nonlocal determinant
  minimum.

Only the geometric throat length is identified between the two sectors.
-/
structure SeparatedChargeStabilizerSynthesis where
  chargeSector : PairedZ4DiracChargeLock
  stabilizerSector : OneFiveMassRadiusLock
  sameGeometricLength :
    stabilizerSector.geometricLength =
      chargeSector.gapData.geometricLength

/-- Both sectors then use the same positive Janus radius. -/
theorem separated_sectors_have_same_alpha_length
    (s : SeparatedChargeStabilizerSynthesis) :
    s.stabilizerSector.alphaSquaredLength =
      s.chargeSector.alphaSquaredLength := by
  rw [s.stabilizerSector.alphaEqualsGeometry,
    z4_dirac_lock_forces_alpha_equals_geometry s.chargeSector]
  exact s.sameGeometricLength

/-- The central Pin-Z4 sector retains the one-eighth charge coefficient. -/
theorem separated_central_sector_charge_coefficient
    (s : SeparatedChargeStabilizerSynthesis) :
    s.chargeSector.llChargeUnit =
      s.chargeSector.sphereFirstSquaredGap / 8 :=
  ll_charge_is_one_eighth_sphere_gap s.chargeSector

/-- The central sector also retains the exact radius lock. -/
theorem separated_central_sector_radius_lock
    (s : SeparatedChargeStabilizerSynthesis) :
    s.chargeSector.alphaSquaredLength =
      s.chargeSector.gapData.geometricLength :=
  z4_dirac_lock_forces_alpha_equals_geometry s.chargeSector

/-- The independent stabilizer mass obeys the one-to-five mass-radius target on the same alpha. -/
theorem separated_internal_stabilizer_mass_target
    (s : SeparatedChargeStabilizerSynthesis) :
    2 * Real.pi ^ 2 *
        (s.stabilizerSector.physicalMass *
          s.chargeSector.alphaSquaredLength) ^ 2 =
      (Real.log 3) ^ 2 := by
  have hTarget := one_five_physical_mass_alpha_target s.stabilizerSector
  rw [separated_sectors_have_same_alpha_length s] at hTarget
  exact hTarget

/--
Identifying the stabilizer mass with the central Dirac gap would force the
additional transcendental constraint `log(3)^2 = pi^2/4`.  The two masses are
therefore not interchangeable by the existing algebra.
-/
theorem identifying_stabilizer_mass_with_charge_gap_forces_constraint
    (s : SeparatedChargeStabilizerSynthesis)
    (hMassIdentification :
      s.stabilizerSector.physicalMass ^ 2 =
        s.chargeSector.gapData.gapSquared) :
    (Real.log 3) ^ 2 = Real.pi ^ 2 / 4 := by
  have hTarget := separated_internal_stabilizer_mass_target s
  have hChargeAlpha :=
    z4_dirac_lock_forces_alpha_equals_geometry s.chargeSector
  rw [hChargeAlpha] at hTarget
  have hMassProduct :
      (s.stabilizerSector.physicalMass *
        s.chargeSector.gapData.geometricLength) ^ 2 =
      s.chargeSector.gapData.gapSquared *
        s.chargeSector.gapData.geometricLength ^ 2 := by
    rw [mul_pow, hMassIdentification]
  rw [hMassProduct] at hTarget
  have hGap :=
    P0EFTJanusZ4HolonomyEtaGap.quarter_gap_under_spectral_isotropy
      s.chargeSector.gapData
  nlinarith [hTarget, hGap]

/-- Complete relational output of the separated two-sector architecture. -/
theorem separated_two_sector_matrix
    (s : SeparatedChargeStabilizerSynthesis) :
    (s.chargeSector.llChargeUnit =
      s.chargeSector.sphereFirstSquaredGap / 8) /\
    (s.chargeSector.alphaSquaredLength =
      s.chargeSector.gapData.geometricLength) /\
    (s.stabilizerSector.alphaSquaredLength =
      s.chargeSector.alphaSquaredLength) /\
    (2 * Real.pi ^ 2 *
        (s.stabilizerSector.physicalMass *
          s.chargeSector.alphaSquaredLength) ^ 2 =
      (Real.log 3) ^ 2) := by
  exact ⟨separated_central_sector_charge_coefficient s,
    separated_central_sector_radius_lock s,
    separated_sectors_have_same_alpha_length s,
    separated_internal_stabilizer_mass_target s⟩

/--
The remaining physical burden is now sharply separated: derive the central Pin
operator and its charge law, derive an independent internal bosonic Z4 and its
stabilizing mass, and prove that both sectors share the same throat geometry
without identifying their bundles, statistics or determinant masses.
-/
structure SeparatedTwoSectorPhysicalStatus where
  centralPinDiracSectorConstructed : Prop
  centralEtaAndChargeLawDerived : Prop
  independentInternalBosonicZ4Constructed : Prop
  internalBosonicDeterminantDerived : Prop
  stabilizerMassGeneratedMicroscopically : Prop
  commonThroatMetricDerived : Prop
  bundleAndMassSeparationProved : Prop
  noDeterminantDoubleCountingProved : Prop
  fullEffectiveActionStable : Prop
  bulkBoundaryChargeCompatibilityDerived : Prop
  absoluteScaleDerivedNoFit : Prop


def separatedTwoSectorPhysicalClosure
    (s : SeparatedTwoSectorPhysicalStatus) : Prop :=
  s.centralPinDiracSectorConstructed /\
  s.centralEtaAndChargeLawDerived /\
  s.independentInternalBosonicZ4Constructed /\
  s.internalBosonicDeterminantDerived /\
  s.stabilizerMassGeneratedMicroscopically /\
  s.commonThroatMetricDerived /\
  s.bundleAndMassSeparationProved /\
  s.noDeterminantDoubleCountingProved /\
  s.fullEffectiveActionStable /\
  s.bulkBoundaryChargeCompatibilityDerived /\
  s.absoluteScaleDerivedNoFit

end P0EFTJanusSeparatedChargeStabilizerSynthesis
end JanusFormal
