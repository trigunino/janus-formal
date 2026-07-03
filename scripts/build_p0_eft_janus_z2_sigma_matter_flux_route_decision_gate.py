from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_route_decision_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_matter_flux_route_decision_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_flux_conservation_bibliography_checked": True,
        "transparency_route_declared": True,
        "active_projection_route_declared": True,
        "route_exhaustive_for_radial_block": True,
        "route_choice_by_fit_forbidden": True,
    }
    closure = {
        "transparency_derived": False,
        "active_flux_projection_ready": False,
        "matter_flux_route_decided": False,
        "matter_flux_radial_reduction_allowed": False,
    }
    return {
        "status": "janus-z2-sigma-matter-flux-route-decision-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel surface conservation identity",
            "Poisson-Visser thin-shell momentum-flux conservation",
            "dynamic thin-shell wormhole flux terms",
        ],
        "bibliography_result": (
            "Thin-shell literature supplies the surface conservation flux channel. "
            "For Janus Z2/Sigma, the radial block must either prove transparency "
            "or compute the active projected flux; the route cannot be selected by fit."
        ),
        "declared": declared,
        "closure": closure,
        "routes": {
            "transparent": "F_a^Z2Sigma = 0 -> E_matterFlux = 0",
            "active_projection": "F_a^Z2Sigma(a) = [T_munu e_a^mu n^nu]_Z2 -> reduce E_matterFlux(a)",
        },
        "matter_flux_route_ledger_declared": all(declared.values()),
        "matter_flux_route_decision_ready": all(declared.values())
        and (closure["transparency_derived"] or closure["active_flux_projection_ready"])
        and closure["matter_flux_route_decided"]
        and closure["matter_flux_radial_reduction_allowed"],
        "next_required": [
            "derive_or_reject_active_sigma_transparency",
            "if_not_transparent_pass_matter_flux_active_projection_gate",
            "choose_route_from_derivation_not_observational_fit",
            "feed_decided_route_to_matter_flux_radial_block_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Matter-Flux Route Decision Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['matter_flux_route_ledger_declared']}`",
        f"Route ready: `{payload['matter_flux_route_decision_ready']}`",
        "",
        "## Routes",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["routes"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
