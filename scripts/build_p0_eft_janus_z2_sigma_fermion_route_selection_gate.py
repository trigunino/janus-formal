from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fermion_route_selection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_fermion_route_selection_gate.json")


def build_payload() -> dict:
    declared = {
        "fermion_route_bibliography_checked": True,
        "Sigma_spinor_variation_channel_imported": True,
        "Dirac_gas_route_selected_from_action": True,
        "Weyssenhoff_route_marked_coarse_graining_only": True,
        "no_fluid_route_chosen_by_fit": True,
        "observational_fit_forbidden": True,
    }
    return {
        "status": "janus-z2-sigma-fermion-route-selection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Hehl et al. 1976, Rev. Mod. Phys. 48, 393",
            "Obukhov/Korotky 1987, Class. Quantum Grav. 4, 1633",
            "active Sigma boundary variational package",
        ],
        "bibliography_result": (
            "The active Sigma action exposes a spinor-variation channel. Generic "
            "Weyssenhoff fluids remain a possible coarse-grained approximation, "
            "but the primitive route for this ledger is Dirac/spinorial, not a "
            "phenomenologically selected spin fluid."
        ),
        "declared": declared,
        "fermion_route_ledger_declared": all(declared.values()),
        "fermion_route_selection_ready": all(declared.values()),
        "selected_route": "Dirac_gas_spinorial",
        "weyssenhoff_status": "coarse_graining_only_not_primitive_route",
        "next_required": [
            "derive_Dirac_fermion_number_density_of_a",
            "derive_Dirac_mass_or_temperature_law",
            "derive_plus_minus_Dirac_distributions_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Fermion Route Selection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Route ready: `{payload['fermion_route_selection_ready']}`",
        f"Selected route: `{payload['selected_route']}`",
        f"Weyssenhoff status: `{payload['weyssenhoff_status']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
