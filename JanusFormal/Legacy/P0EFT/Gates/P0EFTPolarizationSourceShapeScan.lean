namespace JanusFormal
namespace P0EFTPolarizationSourceShapeScan

set_option autoImplicit false

structure PolarizationSourceShapeScan where
  sourceShapeHookRun : Prop
  acceptedPointFound : Prop
  sourceShapeGeometricallyDerived : Prop

def polarizationShapeWindowOpen (s : PolarizationSourceShapeScan) : Prop :=
  s.sourceShapeHookRun /\
  s.acceptedPointFound

def polarizationShapeNoFitReady (s : PolarizationSourceShapeScan) : Prop :=
  polarizationShapeWindowOpen s /\
  s.sourceShapeGeometricallyDerived

theorem accepted_source_shape_still_needs_derivation
    (s : PolarizationSourceShapeScan)
    (_hOpen : polarizationShapeWindowOpen s)
    (hMissing : Not s.sourceShapeGeometricallyDerived) :
    Not (polarizationShapeNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTPolarizationSourceShapeScan
end JanusFormal
