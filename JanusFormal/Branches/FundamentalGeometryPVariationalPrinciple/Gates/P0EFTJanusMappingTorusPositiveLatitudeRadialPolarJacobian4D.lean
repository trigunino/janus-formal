import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceFinalReduction4D

/-!
# Positive latitude: radial--polar Euclidean coordinates

This gate closes the cone calculation by a concrete volume-preserving
coordinate split.  The four-dimensional volume is first split
as the volume of the three tail coordinates times the first coordinate; the
tail is then decomposed into its spherical direction and radius.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
open P0EFTJanusMappingTorusPositiveLatitudeEuclideanConeJacobian4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceFinalReduction4D

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev StandardEquatorialSphere := Metric.sphere (0 : EuclideanR3) 1

/-- The canonical coordinate split: the last three coordinates, followed by
the zeroth coordinate. -/
def splitEuclideanCoordinates : EuclideanR4 ≃ᵐ EuclideanR3 × Real :=
  (MeasurableEquiv.toLp 2 (Fin 4 → Real)).symm |>.trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : Option (Fin 3) => Real) (finSuccEquiv 3)).trans
      ((MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin 3) => Real)).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.toLp 2 (Fin 3 → Real))
          (MeasurableEquiv.refl Real))))

theorem splitEuclideanCoordinates_apply_fst
    (point : EuclideanR4) (index : Fin 3) :
    (EuclideanSpace.equiv (Fin 3) Real
      (splitEuclideanCoordinates point).1) index =
        (EuclideanSpace.equiv (Fin 4) Real point) index.succ := by
  rfl

theorem splitEuclideanCoordinates_apply_snd (point : EuclideanR4) :
    (splitEuclideanCoordinates point).2 =
      (EuclideanSpace.equiv (Fin 4) Real point) 0 := by
  rfl

/-- Splitting orthonormal coordinates does not change Lebesgue volume. -/
theorem splitEuclideanCoordinates_measurePreserving :
    MeasurePreserving splitEuclideanCoordinates
      (volume : Measure EuclideanR4)
      (volume : Measure (EuclideanR3 × Real)) := by
  have hOptionInv : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin 3) => Real)).symm
      (volume : Measure ((Fin 3 → Real) × Real))
      (volume : Measure (Option (Fin 3) → Real)) := by
    refine ⟨(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin 3) => Real)).symm.measurable, ?_⟩
    simpa only [Measure.volume_eq_prod, volume_pi] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin 3) => (volume : Measure Real)))
  have hId : MeasurePreserving (MeasurableEquiv.refl Real)
      (volume : Measure Real) (volume : Measure Real) := by
    change MeasurePreserving (fun x : Real => x)
      (volume : Measure Real) (volume : Measure Real)
    exact MeasurePreserving.id (volume : Measure Real)
  exact
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).trans
      ((volume_measurePreserving_piCongrLeft
        (fun _ : Option (Fin 3) => Real) (finSuccEquiv 3)).trans
        (hOptionInv.symm.trans
          (MeasurePreserving.prod
            (PiLp.volume_preserving_toLp (Fin 3))
            hId)))

private abbrev equatorialSphereMeasure :
    Measure StandardEquatorialSphere :=
  (volume : Measure EuclideanR3).toSphere

/-- Plane integrand obtained after decomposing the three-dimensional tail
into direction and (positive) radius. -/
def tailRadialPlaneIntegrand
    (f : EuclideanR3 × Real → ENNReal)
    (direction : StandardEquatorialSphere) (point : Real × Real) : ENNReal :=
  (Set.Ioi (0 : Real) ×ˢ Set.univ).indicator
    (fun q => ENNReal.ofReal (q.1 ^ 2) *
      f (q.1 • direction.1, q.2)) point

theorem tailRadialPlaneIntegrand_measurable
    {f : EuclideanR3 × Real → ENNReal} (hF : Measurable f)
    (direction : StandardEquatorialSphere) :
    Measurable (tailRadialPlaneIntegrand f direction) := by
  unfold tailRadialPlaneIntegrand
  apply Measurable.indicator
  · exact ((measurable_fst.pow_const 2).ennreal_ofReal.mul
      (hF.comp ((measurable_fst.smul measurable_const).prodMk
        measurable_snd)))
  · exact measurableSet_Ioi.prod MeasurableSet.univ

/-- The only non-linear Jacobian in the four-dimensional latitude chart is
the ordinary two-dimensional polar Jacobian.  The factor `rho^2` is the
three-dimensional radial density, so after the polar substitution the exact
density is `r * (r*cos n)^2`. -/
theorem tailRadialIntegral_eq_polar
    (f : EuclideanR3 × Real → ENNReal) (hF : Measurable f)
    (direction : StandardEquatorialSphere) :
    (∫⁻ radius in Set.Ioi (0 : Real),
      ENNReal.ofReal (radius ^ 2) *
        ∫⁻ height : Real, f (radius • direction.1, height)) =
      ∫⁻ polar in polarCoord.target,
        ENNReal.ofReal polar.1 *
          tailRadialPlaneIntegrand f direction
            (polarCoord.symm polar) := by
  calc
    _ = ∫⁻ point : Real × Real,
        tailRadialPlaneIntegrand f direction point := by
      rw [Measure.volume_eq_prod, lintegral_prod _
        (tailRadialPlaneIntegrand_measurable hF direction).aemeasurable]
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro radius
      by_cases hRadius : radius ∈ Set.Ioi (0 : Real)
      · simp only [Set.indicator_of_mem hRadius]
        simp only [tailRadialPlaneIntegrand, Set.indicator_apply,
          Set.mem_prod, hRadius, Set.mem_univ, and_true, ↓reduceIte]
        symm
        exact lintegral_const_mul _
          (hF.comp (measurable_const.prodMk measurable_id))
      · simp [tailRadialPlaneIntegrand, hRadius]
    _ = _ := by
      simpa [smul_eq_mul] using
        (lintegral_comp_polarCoord_symm
          (tailRadialPlaneIntegrand f direction)).symm

/-- Exact polar disintegration of three-dimensional Euclidean volume, in the
normalization used by `Measure.toSphere`. -/
theorem lintegral_euclideanR3_eq_sphericalRadial
    (g : EuclideanR3 → ENNReal) (hG : Measurable g) :
    (∫⁻ point : EuclideanR3, g point) =
      ∫⁻ direction : StandardEquatorialSphere,
        ∫⁻ radius in Set.Ioi (0 : Real),
          ENNReal.ofReal (radius ^ 2) *
            g (radius • direction.1)
        ∂(volume : Measure Real)
      ∂equatorialSphereMeasure := by
  let nonzero : Set EuclideanR3 := ({0} : Set EuclideanR3)ᶜ
  have hNonzero : MeasurableSet nonzero :=
    (measurableSet_singleton (0 : EuclideanR3)).compl
  calc
    (∫⁻ point : EuclideanR3, g point) =
        ∫⁻ point : EuclideanR3, g point
          ∂(volume : Measure EuclideanR3).restrict nonzero := by
      rw [restrict_compl_singleton]
    _ = ∫⁻ point : nonzero, g point
          ∂((volume : Measure EuclideanR3).comap (↑)) := by
      exact (lintegral_subtype_comap hNonzero g).symm
    _ = ∫⁻ parameter : StandardEquatorialSphere × Set.Ioi (0 : Real),
          g (parameter.2.1 • parameter.1.1)
          ∂(equatorialSphereMeasure.prod (Measure.volumeIoiPow 2)) := by
      have hMap :=
        (volume : Measure EuclideanR3).measurePreserving_homeomorphUnitSphereProd
      have hIntegral := hMap.lintegral_comp_emb
        (homeomorphUnitSphereProd EuclideanR3).measurableEmbedding
        (fun parameter =>
          g ((homeomorphUnitSphereProd EuclideanR3).symm parameter).1)
      simpa [nonzero, equatorialSphereMeasure] using hIntegral
    _ = ∫⁻ direction : StandardEquatorialSphere,
          ∫⁻ radius : Set.Ioi (0 : Real),
            g (radius.1 • direction.1)
            ∂(Measure.volumeIoiPow 2)
          ∂equatorialSphereMeasure := by
      rw [lintegral_prod]
      exact (hG.comp
        ((measurable_subtype_coe.comp measurable_snd).smul
          (measurable_subtype_coe.comp measurable_fst))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro direction
      rw [Measure.volumeIoiPow]
      calc
        (∫⁻ radius : Set.Ioi (0 : Real),
            g (radius.1 • direction.1)
              ∂((volume : Measure Real).comap (↑)).withDensity
                (fun r => ENNReal.ofReal (r.1 ^ 2))) =
            ∫⁻ radius : Set.Ioi (0 : Real),
              ENNReal.ofReal (radius.1 ^ 2) *
                g (radius.1 • direction.1)
              ∂((volume : Measure Real).comap (↑)) := by
          exact lintegral_withDensity_eq_lintegral_mul _
            (by fun_prop)
            (hG.comp (measurable_subtype_coe.smul measurable_const))
        _ = _ := by
          simpa only [equatorialSphereMeasure] using
            (lintegral_subtype_comap (μ := (volume : Measure Real))
              measurableSet_Ioi
              (fun radius : Real => ENNReal.ofReal (radius ^ 2) *
                g (radius • direction.1)))

/-- Full `R^3 × R` radial--polar formula.  The right side uses only the
standard two-dimensional polar chart and Mathlib's normalized round measure
on `S^2`. -/
theorem lintegral_euclideanR3ProdReal_eq_radialPolar
    (f : EuclideanR3 × Real → ENNReal) (hF : Measurable f) :
    (∫⁻ point : EuclideanR3 × Real, f point) =
      ∫⁻ direction : StandardEquatorialSphere,
        ∫⁻ polar in polarCoord.target,
          ENNReal.ofReal polar.1 *
            tailRadialPlaneIntegrand f direction
              (polarCoord.symm polar)
        ∂(volume : Measure (Real × Real))
      ∂equatorialSphereMeasure := by
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
  rw [lintegral_euclideanR3_eq_sphericalRadial
    (fun point : EuclideanR3 => ∫⁻ height : Real, f (point, height))
    hF.lintegral_prod_right']
  apply lintegral_congr
  intro direction
  exact tailRadialIntegral_eq_polar f hF direction

/-- Coordinate-free four-dimensional version, obtained by the exact
volume-preserving orthonormal split above. -/
theorem lintegral_euclideanR4_eq_radialPolar
    (f : EuclideanR4 → ENNReal) (hF : Measurable f) :
    (∫⁻ point : EuclideanR4, f point) =
      ∫⁻ direction : StandardEquatorialSphere,
        ∫⁻ polar in polarCoord.target,
          ENNReal.ofReal polar.1 *
            tailRadialPlaneIntegrand
              (fun point => f (splitEuclideanCoordinates.symm point))
              direction (polarCoord.symm polar)
        ∂(volume : Measure (Real × Real))
      ∂equatorialSphereMeasure := by
  calc
    (∫⁻ point : EuclideanR4, f point) =
        ∫⁻ point : EuclideanR3 × Real,
          f (splitEuclideanCoordinates.symm point) := by
      have hIntegral := splitEuclideanCoordinates_measurePreserving.lintegral_comp_emb
        splitEuclideanCoordinates.measurableEmbedding
        (fun point => f (splitEuclideanCoordinates.symm point))
      simpa using hIntegral
    _ = _ := lintegral_euclideanR3ProdReal_eq_radialPolar
      (fun point => f (splitEuclideanCoordinates.symm point))
      (hF.comp splitEuclideanCoordinates.symm.measurable)

private theorem radialCone_eq_subtypeImage
    (sphereSet : Set StandardSphere) :
    ((fun point : ({0}ᶜ : Set EuclideanR4) => point.1) ''
      ((homeomorphUnitSphereProd EuclideanR4) ⁻¹'
        (sphereSet ×ˢ Set.Iio
          (⟨(1 : Real), Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : Real))))) =
      Set.Ioo (0 : Real) 1 •
        ((fun point : StandardSphere => point.1) '' sphereSet) := by
  rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm,
    image_image, ← image_subtype_val_Ioi_Iio
      (⟨(1 : Real), Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : Real)),
    image2_image_left,
    image2_swap, ← image_prod]
  rfl

theorem canonicalPositiveLatitudeCone_measurable
    {set : Set StandardSphere} (hSet : MeasurableSet set) :
    MeasurableSet (canonicalPositiveLatitudeCone set) := by
  let sphereSet := set ∩
    (canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain)
  have hSphereSet : MeasurableSet sphereSet :=
    hSet.inter canonicalPositiveLatitudeMap_image_measurable
  have hPreimage : MeasurableSet
      ((homeomorphUnitSphereProd EuclideanR4) ⁻¹'
        (sphereSet ×ˢ Set.Iio
          (⟨(1 : Real), Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : Real)))) :=
    (hSphereSet.prod measurableSet_Iio).preimage
      (homeomorphUnitSphereProd EuclideanR4).measurable
  rw [canonicalPositiveLatitudeCone, ← radialCone_eq_subtypeImage sphereSet]
  exact (MeasurableEmbedding.subtype_coe
    (measurableSet_singleton (0 : EuclideanR4)).compl).measurableSet_image'
      hPreimage

/-- Radial latitude coordinates in the split Euclidean model. -/
def radialLatitudePoint (direction : StandardEquatorialSphere)
    (radius normal : Real) : EuclideanR4 :=
  splitEuclideanCoordinates.symm
    ((radius * Real.cos normal) • direction.1,
      radius * Real.sin normal)

theorem split_smul_canonicalPositiveLatitudeMap
    (direction : StandardEquatorialSphere) (radius normal : Real) :
    splitEuclideanCoordinates
        (radius • (canonicalPositiveLatitudeMap (direction, normal)).1) =
      ((radius * Real.cos normal) • direction.1,
        radius * Real.sin normal) := by
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin 3) Real).injective
    funext index
    rw [splitEuclideanCoordinates_apply_fst]
    simp only [map_smul, Pi.smul_apply,
      smul_eq_mul, canonicalPositiveLatitudeMap_tailCoordinate]
    ring
  · rw [splitEuclideanCoordinates_apply_snd]
    simp only [map_smul, Pi.smul_apply,
      smul_eq_mul, canonicalPositiveLatitudeMap_firstCoordinate]

theorem radialLatitudePoint_eq_smul
    (direction : StandardEquatorialSphere) (radius normal : Real) :
    radialLatitudePoint direction radius normal =
      radius • (canonicalPositiveLatitudeMap (direction, normal)).1 := by
  apply splitEuclideanCoordinates.injective
  rw [radialLatitudePoint, MeasurableEquiv.apply_symm_apply,
    split_smul_canonicalPositiveLatitudeMap]

private theorem homeomorphUnitSphereProd_positive_smul
    (point : StandardSphere) {radius : Real} (hRadius : 0 < radius) :
    (homeomorphUnitSphereProd EuclideanR4)
        (⟨radius • point.1, by
          exact smul_ne_zero hRadius.ne'
            (ne_zero_of_mem_sphere one_ne_zero point)⟩ :
          ({0}ᶜ : Set EuclideanR4)) =
      (point, ⟨radius, Set.mem_Ioi.mpr hRadius⟩) := by
  apply (homeomorphUnitSphereProd EuclideanR4).symm.injective
  apply Subtype.ext
  simp [homeomorphUnitSphereProd_symm_apply_coe]

theorem radialLatitudePoint_mem_cone_iff
    (set : Set StandardSphere) (direction : StandardEquatorialSphere)
    {radius normal : Real} (hRadius : 0 < radius) :
    radialLatitudePoint direction radius normal ∈
        canonicalPositiveLatitudeCone set ↔
      canonicalPositiveLatitudeMap (direction, normal) ∈
          set ∩ (canonicalPositiveLatitudeMap ''
            canonicalPositiveLatitudeDomain) ∧
        radius < 1 := by
  let spherePoint := canonicalPositiveLatitudeMap (direction, normal)
  let nonzeroPoint : ({0}ᶜ : Set EuclideanR4) :=
    ⟨radius • spherePoint.1, by
      exact smul_ne_zero hRadius.ne'
        (ne_zero_of_mem_sphere one_ne_zero spherePoint)⟩
  have hRadial : radialLatitudePoint direction radius normal =
      nonzeroPoint.1 := by
    exact radialLatitudePoint_eq_smul direction radius normal
  have hHomeomorph :
      (homeomorphUnitSphereProd EuclideanR4) nonzeroPoint =
        (spherePoint, ⟨radius, Set.mem_Ioi.mpr hRadius⟩) := by
    exact homeomorphUnitSphereProd_positive_smul spherePoint hRadius
  rw [canonicalPositiveLatitudeCone,
    ← radialCone_eq_subtypeImage
      (set ∩ (canonicalPositiveLatitudeMap ''
        canonicalPositiveLatitudeDomain)), hRadial]
  constructor
  · rintro ⟨point, hPoint, hCoe⟩
    have hPointEq : point = nonzeroPoint := by
      exact Subtype.ext hCoe
    subst point
    change (homeomorphUnitSphereProd EuclideanR4) nonzeroPoint ∈
      (set ∩ (canonicalPositiveLatitudeMap ''
        canonicalPositiveLatitudeDomain)) ×ˢ
          Set.Iio (⟨(1 : Real), Set.mem_Ioi.mpr one_pos⟩ :
            Set.Ioi (0 : Real)) at hPoint
    rw [hHomeomorph] at hPoint
    exact ⟨hPoint.1, hPoint.2⟩
  · rintro ⟨hSphere, hRadiusOne⟩
    refine ⟨nonzeroPoint, ?_, rfl⟩
    change (homeomorphUnitSphereProd EuclideanR4) nonzeroPoint ∈
      (set ∩ (canonicalPositiveLatitudeMap ''
        canonicalPositiveLatitudeDomain)) ×ˢ
          Set.Iio (⟨(1 : Real), Set.mem_Ioi.mpr one_pos⟩ :
            Set.Ioi (0 : Real))
    rw [hHomeomorph]
    exact ⟨hSphere, hRadiusOne⟩

/-- On the polar chart with positive tail radius, belonging to the latitude
image is exactly the normal-coordinate restriction used by the source
measure. -/
theorem canonicalPositiveLatitudeMap_mem_image_iff_of_polar
    (direction : StandardEquatorialSphere) {radius normal : Real}
    (hPolar : (radius, normal) ∈ polarCoord.target)
    (hTail : 0 < radius * Real.cos normal) :
    canonicalPositiveLatitudeMap (direction, normal) ∈
        canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain ↔
      normal ∈ Set.Ioc (0 : Real) 1 := by
  constructor
  · rintro ⟨parameter, hParameter, hEqual⟩
    have hRadius : 0 < radius := hPolar.1
    have hCosNormal : 0 < Real.cos normal := by
      rcases (mul_pos_iff.mp hTail) with h | h
      · exact h.2
      · exfalso
        linarith [hRadius, h.1]
    have hCosParameter : 0 < Real.cos parameter.2 := by
      have hAbs : |parameter.2| ≤ 1 := by
        rw [abs_of_pos hParameter.2.1]
        exact hParameter.2.2
      exact Real.cos_pos_of_le_one hAbs
    have hSin : Real.sin normal = Real.sin parameter.2 := by
      simpa only [canonicalPositiveLatitudeMap_firstCoordinate] using
        congrArg
          (fun point : StandardSphere =>
            (EuclideanSpace.equiv (Fin 4) Real point.1) 0) hEqual.symm
    have hTailVector :
        Real.cos normal • direction.1 =
          Real.cos parameter.2 • parameter.1.1 := by
      apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      have hCoordinate := congrArg
          (fun point : StandardSphere =>
          (EuclideanSpace.equiv (Fin 4) Real point.1) index.succ) hEqual.symm
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul,
        canonicalPositiveLatitudeMap_tailCoordinate] using hCoordinate
    have hDirectionNorm : ‖direction.1‖ = 1 :=
      mem_sphere_zero_iff_norm.mp direction.2
    have hParameterNorm : ‖parameter.1.1‖ = 1 :=
      mem_sphere_zero_iff_norm.mp parameter.1.2
    have hCos : Real.cos normal = Real.cos parameter.2 := by
      have hNorm := congrArg norm hTailVector
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hCosNormal,
        abs_of_pos hCosParameter, hDirectionNorm, hParameterNorm, mul_one]
        using hNorm
    have hNormalTarget : ((1 : Real), normal) ∈ polarCoord.target := by
      exact ⟨Set.mem_Ioi.mpr one_pos, hPolar.2⟩
    have hParameterTarget : ((1 : Real), parameter.2) ∈ polarCoord.target := by
      refine ⟨Set.mem_Ioi.mpr one_pos, ?_⟩
      constructor
      · linarith [hParameter.2.1, Real.pi_pos]
      · linarith [hParameter.2.2, Real.pi_gt_three]
    have hPolarImage :
        polarCoord.symm ((1 : Real), normal) =
          polarCoord.symm ((1 : Real), parameter.2) := by
      apply Prod.ext
      · simpa only [polarCoord_symm_apply, one_mul] using hCos
      · simpa only [polarCoord_symm_apply, one_mul] using hSin
    have hPair : ((1 : Real), normal) = ((1 : Real), parameter.2) :=
      polarCoord.symm.injOn hNormalTarget hParameterTarget hPolarImage
    have hNormal : normal = parameter.2 := congrArg Prod.snd hPair
    simpa only [hNormal] using hParameter.2
  · intro hNormal
    exact ⟨(direction, normal), ⟨Set.mem_univ _, hNormal⟩, rfl⟩

private def latitudeSourceIntegrand (set : Set StandardSphere)
    (parameter : StandardEquatorialSphere × Real) : ENNReal :=
  (canonicalPositiveLatitudeMap ⁻¹' set).indicator
    canonicalPositiveLatitudeJacobian parameter

private theorem latitudeSourceIntegrand_measurable
    {set : Set StandardSphere} (hSet : MeasurableSet set) :
    Measurable (latitudeSourceIntegrand set) := by
  exact canonicalPositiveLatitudeJacobian_measurable.indicator
    (hSet.preimage canonicalPositiveLatitudeMap_continuous.measurable)

private def radialPowerDensity (radius : Real) : ENNReal :=
  Set.Ioo (0 : Real) 1 |>.indicator
    (fun r => ENNReal.ofReal (r ^ 3)) radius

private theorem radialPowerDensity_measurable :
    Measurable radialPowerDensity := by
  exact (measurable_id.pow_const 3).ennreal_ofReal.indicator measurableSet_Ioo

private def normalLatitudeDensity (set : Set StandardSphere)
    (direction : StandardEquatorialSphere) (normal : Real) : ENNReal :=
  Set.Ioc (0 : Real) 1 |>.indicator
    (fun n => latitudeSourceIntegrand set (direction, n)) normal

private theorem normalLatitudeDensity_measurable
    {set : Set StandardSphere} (hSet : MeasurableSet set)
    (direction : StandardEquatorialSphere) :
    Measurable (normalLatitudeDensity set direction) := by
  exact ((latitudeSourceIntegrand_measurable hSet).comp
    (measurable_const.prodMk measurable_id)).indicator measurableSet_Ioc

private def radialPolarConeIntegrand (set : Set StandardSphere)
    (direction : StandardEquatorialSphere) (polar : Real × Real) : ENNReal :=
  radialPowerDensity polar.1 *
    normalLatitudeDensity set direction polar.2

private theorem radialPolarConeIntegrand_measurable
    {set : Set StandardSphere} (hSet : MeasurableSet set)
    (direction : StandardEquatorialSphere) :
    Measurable (radialPolarConeIntegrand set direction) := by
  exact (radialPowerDensity_measurable.comp measurable_fst).mul
    ((normalLatitudeDensity_measurable hSet direction).comp measurable_snd)

private theorem positive_cos_of_mem_unitNormal
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    0 < Real.cos normal := by
  apply Real.cos_pos_of_le_one
  rw [abs_of_pos hNormal.1]
  exact hNormal.2

private theorem polarConeIntegrand_eq_radialPolarConeIntegrand
    {set : Set StandardSphere}
    (direction : StandardEquatorialSphere) (polar : Real × Real)
    (hPolar : polar ∈ polarCoord.target) :
    ENNReal.ofReal polar.1 *
        tailRadialPlaneIntegrand
          (fun point => (canonicalPositiveLatitudeCone set).indicator
            (fun _ => (1 : ENNReal))
              (splitEuclideanCoordinates.symm point))
          direction (polarCoord.symm polar) =
      radialPolarConeIntegrand set direction polar := by
  have hRadius : 0 < polar.1 := hPolar.1
  by_cases hTail : 0 < polar.1 * Real.cos polar.2
  · have hImage := canonicalPositiveLatitudeMap_mem_image_iff_of_polar
      direction hPolar hTail
    have hCone := radialLatitudePoint_mem_cone_iff
      (radius := polar.1) (normal := polar.2) set direction hRadius
    have hConeMembership :
        radialLatitudePoint direction polar.1 polar.2 ∈
            canonicalPositiveLatitudeCone set ↔
          canonicalPositiveLatitudeMap (direction, polar.2) ∈ set ∧
            polar.2 ∈ Set.Ioc (0 : Real) 1 ∧ polar.1 < 1 := by
      rw [hCone, Set.mem_inter_iff, hImage]
      tauto
    rw [show polarCoord.symm polar =
      (polar.1 * Real.cos polar.2,
        polar.1 * Real.sin polar.2) from rfl]
    unfold tailRadialPlaneIntegrand
    rw [Set.indicator_of_mem (show
      (polar.1 * Real.cos polar.2,
          polar.1 * Real.sin polar.2) ∈
        Set.Ioi (0 : Real) ×ˢ Set.univ from
          ⟨hTail, Set.mem_univ _⟩)]
    change ENNReal.ofReal polar.1 *
        (ENNReal.ofReal ((polar.1 * Real.cos polar.2) ^ 2) *
          (canonicalPositiveLatitudeCone set).indicator
            (fun _ => (1 : ENNReal))
              (radialLatitudePoint direction polar.1 polar.2)) = _
    by_cases hNormal : polar.2 ∈ Set.Ioc (0 : Real) 1
    · by_cases hRadiusOne : polar.1 < 1
      · by_cases hPoint : canonicalPositiveLatitudeMap
          (direction, polar.2) ∈ set
        · rw [Set.indicator_of_mem
            (hConeMembership.mpr ⟨hPoint, hNormal, hRadiusOne⟩)]
          unfold radialPolarConeIntegrand radialPowerDensity
            normalLatitudeDensity latitudeSourceIntegrand
          rw [Set.indicator_of_mem (show polar.1 ∈ Set.Ioo (0 : Real) 1 from
            ⟨hRadius, hRadiusOne⟩)]
          rw [Set.indicator_of_mem hNormal]
          rw [Set.indicator_of_mem (show
            (direction, polar.2) ∈ canonicalPositiveLatitudeMap ⁻¹' set
              from hPoint)]
          unfold canonicalPositiveLatitudeJacobian
          simp only [mul_one]
          rw [← ENNReal.ofReal_mul hRadius.le]
          rw [← ENNReal.ofReal_mul (pow_nonneg hRadius.le 3)]
          congr 1
          ring
        · rw [Set.indicator_of_notMem
            (fun h => hPoint (hConeMembership.mp h).1)]
          simp [radialPolarConeIntegrand, radialPowerDensity,
            normalLatitudeDensity, latitudeSourceIntegrand, hPoint]
      · rw [Set.indicator_of_notMem
          (fun h => hRadiusOne (hConeMembership.mp h).2.2)]
        simp [radialPolarConeIntegrand, radialPowerDensity, hRadiusOne]
    · rw [Set.indicator_of_notMem
        (fun h => hNormal (hConeMembership.mp h).2.1)]
      simp [radialPolarConeIntegrand, normalLatitudeDensity, hNormal]
  · have hNormal : polar.2 ∉ Set.Ioc (0 : Real) 1 := by
      intro hNormal
      exact hTail (mul_pos hRadius (positive_cos_of_mem_unitNormal hNormal))
    have hNotSupport : polarCoord.symm polar ∉
        Set.Ioi (0 : Real) ×ˢ Set.univ := by
      simpa only [polarCoord_symm_apply, Set.mem_prod, Set.mem_Ioi,
        Set.mem_univ, and_true] using hTail
    unfold tailRadialPlaneIntegrand
    rw [Set.indicator_of_notMem hNotSupport]
    simp [radialPolarConeIntegrand, normalLatitudeDensity, hNormal]

private theorem radialPowerDensity_lintegral :
    (∫⁻ radius : Real, radialPowerDensity radius) = (4 : ENNReal)⁻¹ := by
  have hRadial := Measure.volumeIoiPow_apply_Iio 3
    (⟨(1 : Real), Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : Real))
  rw [Measure.volumeIoiPow, withDensity_apply _ measurableSet_Iio,
    setLIntegral_subtype measurableSet_Ioi _
      (fun radius : Real => ENNReal.ofReal (radius ^ 3)),
    image_subtype_val_Ioi_Iio] at hRadial
  unfold radialPowerDensity
  rw [lintegral_indicator measurableSet_Ioo]
  calc
    _ = ENNReal.ofReal ((1 : Real) / 4) := by
      convert hRadial using 1 <;> norm_num
    _ = (4 : ENNReal)⁻¹ := by
      simpa only [one_div, ENNReal.ofReal_ofNat] using
        (ENNReal.ofReal_inv_of_pos (show 0 < (4 : Real) by norm_num))

private theorem radialPolarConeIntegrand_support
    (set : Set StandardSphere) (direction : StandardEquatorialSphere) :
    (radialPolarConeIntegrand set direction).support ⊆ polarCoord.target := by
  intro polar hSupport
  have hNonzero : radialPowerDensity polar.1 *
      normalLatitudeDensity set direction polar.2 ≠ 0 := hSupport
  have hFactors := mul_ne_zero_iff.mp hNonzero
  have hRadius : polar.1 ∈ Set.Ioo (0 : Real) 1 := by
    by_contra hRadius
    apply hFactors.1
    unfold radialPowerDensity
    exact Set.indicator_of_notMem hRadius _
  have hNormal : polar.2 ∈ Set.Ioc (0 : Real) 1 := by
    by_contra hNormal
    apply hFactors.2
    unfold normalLatitudeDensity
    exact Set.indicator_of_notMem hNormal _
  refine ⟨hRadius.1, ?_⟩
  constructor
  · linarith [hNormal.1, Real.pi_pos]
  · linarith [hNormal.2, Real.pi_gt_three]

private theorem radialPolarConeIntegrand_lintegral
    {set : Set StandardSphere} (hSet : MeasurableSet set)
    (direction : StandardEquatorialSphere) :
    (∫⁻ polar in polarCoord.target,
        radialPolarConeIntegrand set direction polar
        ∂(volume : Measure (Real × Real))) =
      (4 : ENNReal)⁻¹ *
        ∫⁻ normal : Real, normalLatitudeDensity set direction normal := by
  calc
    _ = ∫⁻ polar : Real × Real,
        radialPolarConeIntegrand set direction polar :=
      setLIntegral_eq_of_support_subset
        (radialPolarConeIntegrand_support set direction)
    _ = (∫⁻ radius : Real, radialPowerDensity radius) *
          ∫⁻ normal : Real, normalLatitudeDensity set direction normal := by
      rw [Measure.volume_eq_prod]
      exact lintegral_prod_mul radialPowerDensity_measurable.aemeasurable
        (normalLatitudeDensity_measurable hSet direction).aemeasurable
    _ = _ := by rw [radialPowerDensity_lintegral]

private theorem normalLatitudeDensity_joint_measurable
    {set : Set StandardSphere} (hSet : MeasurableSet set) :
    Measurable (fun parameter : StandardEquatorialSphere × Real =>
      normalLatitudeDensity set parameter.1 parameter.2) := by
  change Measurable ((Prod.snd ⁻¹' Set.Ioc (0 : Real) 1).indicator
    (latitudeSourceIntegrand set))
  exact (latitudeSourceIntegrand_measurable hSet).indicator
    (measurableSet_Ioc.preimage measurable_snd)

private theorem sourceIntegral_eq_angularIntegral
    {set : Set StandardSphere} (hSet : MeasurableSet set) :
    (∫⁻ parameter in canonicalPositiveLatitudeMap ⁻¹' set,
        canonicalPositiveLatitudeJacobian parameter
        ∂(((volume : Measure EuclideanR3).toSphere).prod
          canonicalLatitudeUnitNormalMeasure)) =
      ∫⁻ direction : StandardEquatorialSphere,
        (∫⁻ normal : Real, normalLatitudeDensity set direction normal
          ∂(volume : Measure Real))
        ∂equatorialSphereMeasure := by
  have hPreimage : MeasurableSet
      (canonicalPositiveLatitudeMap ⁻¹' set) :=
    hSet.preimage canonicalPositiveLatitudeMap_continuous.measurable
  rw [← lintegral_indicator hPreimage]
  change (∫⁻ parameter : StandardEquatorialSphere × Real,
      latitudeSourceIntegrand set parameter
      ∂(((volume : Measure EuclideanR3).toSphere).prod
        canonicalLatitudeUnitNormalMeasure)) = _
  rw [lintegral_prod _ (latitudeSourceIntegrand_measurable hSet).aemeasurable]
  apply lintegral_congr
  intro direction
  unfold canonicalLatitudeUnitNormalMeasure normalLatitudeDensity
  exact (lintegral_indicator measurableSet_Ioc
    (fun normal : Real => latitudeSourceIntegrand set (direction, normal))).symm

private theorem cone_volume_eq_quarter_angularIntegral
    {set : Set StandardSphere} (hSet : MeasurableSet set) :
    (volume : Measure EuclideanR4) (canonicalPositiveLatitudeCone set) =
      (4 : ENNReal)⁻¹ *
        ∫⁻ direction : StandardEquatorialSphere,
          (∫⁻ normal : Real, normalLatitudeDensity set direction normal
            ∂(volume : Measure Real))
          ∂equatorialSphereMeasure := by
  have hCone : MeasurableSet (canonicalPositiveLatitudeCone set) :=
    canonicalPositiveLatitudeCone_measurable hSet
  have hIndicator : Measurable
      (fun point : EuclideanR4 =>
        (canonicalPositiveLatitudeCone set).indicator
          (fun _ => (1 : ENNReal)) point) :=
    measurable_const.indicator hCone
  have hAngular : Measurable
      (fun direction : StandardEquatorialSphere =>
        ∫⁻ normal : Real, normalLatitudeDensity set direction normal
          ∂(volume : Measure Real)) :=
    (normalLatitudeDensity_joint_measurable hSet).lintegral_prod_right'
  calc
    (volume : Measure EuclideanR4) (canonicalPositiveLatitudeCone set) =
        ∫⁻ point : EuclideanR4,
          (canonicalPositiveLatitudeCone set).indicator
            (fun _ => (1 : ENNReal)) point :=
      (lintegral_indicator_one hCone).symm
    _ = ∫⁻ direction : StandardEquatorialSphere,
          ∫⁻ polar in polarCoord.target,
            ENNReal.ofReal polar.1 *
              tailRadialPlaneIntegrand
                (fun point => (canonicalPositiveLatitudeCone set).indicator
                  (fun _ => (1 : ENNReal))
                    (splitEuclideanCoordinates.symm point))
                direction (polarCoord.symm polar)
              ∂(volume : Measure (Real × Real))
          ∂equatorialSphereMeasure :=
      lintegral_euclideanR4_eq_radialPolar _ hIndicator
    _ = ∫⁻ direction : StandardEquatorialSphere,
          ∫⁻ polar in polarCoord.target,
            radialPolarConeIntegrand set direction polar
              ∂(volume : Measure (Real × Real))
          ∂equatorialSphereMeasure := by
      apply lintegral_congr
      intro direction
      exact setLIntegral_congr_fun polarCoord.open_target.measurableSet
        (fun polar hPolar =>
          polarConeIntegrand_eq_radialPolarConeIntegrand
            direction polar hPolar)
    _ = ∫⁻ direction : StandardEquatorialSphere,
          (4 : ENNReal)⁻¹ *
            (∫⁻ normal : Real, normalLatitudeDensity set direction normal
              ∂(volume : Measure Real))
          ∂equatorialSphereMeasure := by
      apply lintegral_congr
      intro direction
      exact radialPolarConeIntegrand_lintegral hSet direction
    _ = _ := lintegral_const_mul _ hAngular

/-- The standard radial, spherical and planar-polar formulas close the
Euclidean cone identity without any additional analytic assumption. -/
theorem canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar :
    CanonicalPositiveLatitudeEuclideanConeJacobianFormula := by
  unfold CanonicalPositiveLatitudeEuclideanConeJacobianFormula
  intro set hSet
  change (∫⁻ parameter in canonicalPositiveLatitudeMap ⁻¹' set,
      canonicalPositiveLatitudeJacobian parameter
      ∂(((volume : Measure EuclideanR3).toSphere).prod
        canonicalLatitudeUnitNormalMeasure)) = _
  rw [sourceIntegral_eq_angularIntegral hSet,
    cone_volume_eq_quarter_angularIntegral hSet, ← mul_assoc]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem canonicalPositiveLatitudeWeightedMapFormula_radialPolar :
    CanonicalPositiveLatitudeWeightedMapFormula :=
  canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone
    canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar

theorem canonicalPositiveLatitudeMeasureDomination_radialPolar :
    CanonicalPositiveLatitudeMeasureDomination :=
  canonicalPositiveLatitudeMeasureDomination_of_euclideanCone
    canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar

def canonicalLatitudeCoareaBoundRadialPolar
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfEuclideanCone period hPeriod
    canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar

/-- The canonical physical trace bound is now an unconditional object. -/
def canonicalPhysicalH1TraceBoundRadialPolar
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalPhysicalH1TraceBound period hPeriod :=
  canonicalPhysicalH1TraceBoundOfEuclideanCone period hPeriod
    canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar

/-- The canonical physical trace operator obtained from the closed coarea
chain. -/
def canonicalPhysicalH1TraceRadialPolar
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  canonicalPhysicalH1TraceOfEuclideanCone period hPeriod
    canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar

theorem canonicalPhysicalH1TraceRadialPolar_agrees_on_smooth
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalH1TraceRadialPolar period hPeriod
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field :=
  canonicalPhysicalH1TraceOfWeightedMapFormula_agrees_on_smooth
    period hPeriod canonicalPositiveLatitudeWeightedMapFormula_radialPolar field

theorem canonicalPhysicalH1TraceExists_radialPolar
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  canonicalPhysicalH1TraceExists_of_euclideanCone period hPeriod
    canonicalPositiveLatitudeEuclideanConeJacobianFormula_radialPolar

end

end P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D
end JanusFormal
