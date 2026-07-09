namespace JanusFormal
namespace P0EFTJanusOrbifoldRedshiftMapRulerGate

set_option autoImplicit false

structure OrbifoldRedshiftMapRulerGate where
  redshiftMapDeclared : Prop
  lowRedshiftIdentityLimit : Prop
  highRedshiftLiftToDragDomain : Prop
  mapDerivedFromOrbifoldTransport : Prop
  noPhenomenologicalCompression : Prop
  routeClosed : Prop

def redshiftMapRouteBlocked (g : OrbifoldRedshiftMapRulerGate) : Prop :=
  g.redshiftMapDeclared /\
  g.lowRedshiftIdentityLimit /\
  g.highRedshiftLiftToDragDomain /\
  Not g.mapDerivedFromOrbifoldTransport /\
  g.noPhenomenologicalCompression /\
  Not g.routeClosed

theorem redshift_map_route_needs_derived_transport
    (g : OrbifoldRedshiftMapRulerGate)
    (h : redshiftMapRouteBlocked g) :
    Not g.routeClosed := by
  exact h.2.2.2.2.2

end P0EFTJanusOrbifoldRedshiftMapRulerGate
end JanusFormal
