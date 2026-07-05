from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_block_gate import (
    build_payload as build_counterterm_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_radial_block_gate import (
    build_payload as build_holst_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_holst_nieh_yan_radial_term_from_active_inputs_gate import (
    build_payload as build_holst_radial_term_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_transparency_gate import (
    build_payload as build_matter_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_active_projection_gate import (
    build_payload as build_matter_flux_active_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate import (
    build_payload as build_counterterm_density_variation_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_non_cartan_rsigma_radial_terms_status_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_non_cartan_rsigma_radial_terms_status_gate.json")


def _frontier(payload: dict) -> list[str]:
    if payload.get("current_frontier"):
        return list(payload["current_frontier"])
    blocker = payload.get("primary_blocker")
    if blocker and blocker != "none":
        return [str(blocker)]
    return []


def _required_for_missing(missing: list[str]) -> list[str]:
    required_by_term = {
        "E_HolstNiehYan": "derive_E_HolstNiehYan_radial_term_manifest",
        "E_matterFlux": "derive_E_matterFlux_radial_term_manifest",
        "E_counterterm": "derive_E_counterterm_radial_term_manifest",
    }
    required = [required_by_term[name] for name in missing]
    if missing:
        required.append("rerun_R_Sigma_isotropic_balance_solver")
    return required


def build_payload(
    *,
    holst_payload: dict | None = None,
    holst_radial_term_payload: dict | None = None,
    matter_flux_payload: dict | None = None,
    matter_flux_active_projection_payload: dict | None = None,
    counterterm_payload: dict | None = None,
    counterterm_density_variation_payload: dict | None = None,
) -> dict:
    holst = holst_payload or build_holst_payload()
    holst_radial = holst_radial_term_payload or build_holst_radial_term_payload()
    matter_flux = matter_flux_payload or build_matter_flux_payload()
    matter_flux_active = matter_flux_active_projection_payload or build_matter_flux_active_projection_payload()
    counterterm = counterterm_payload or build_counterterm_payload()
    counterterm_density_variation = (
        counterterm_density_variation_payload or build_counterterm_density_variation_payload()
    )
    matter_flux_ready = bool(matter_flux.get("E_matterFlux_zero_from_transparency_written")) or bool(
        matter_flux_active.get("E_matterFlux_from_active_projection_written")
    )
    terms = {
        "E_HolstNiehYan": {
            "ready": bool(holst_radial.get("E_HolstNiehYan_from_active_inputs_written")),
            "primary_blocker": (
                "none"
                if bool(holst_radial.get("E_HolstNiehYan_from_active_inputs_written"))
                else holst_radial.get("primary_blocker", "active_holst_nieh_yan_radial_inputs")
            ),
            "frontier": [] if bool(holst_radial.get("E_HolstNiehYan_from_active_inputs_written")) else _frontier(holst) + _frontier(holst_radial),
            "routes": {
                "structural_block_ready": bool(holst.get("holst_nieh_yan_radial_block_of_a_ready")),
                "active_inputs_manifest_ready": bool(
                    holst_radial.get("E_HolstNiehYan_from_active_inputs_written")
                ),
            },
        },
        "E_matterFlux": {
            "ready": matter_flux_ready,
            "primary_blocker": "none" if matter_flux_ready else "matter_flux_transparency_or_active_projection",
            "frontier": [] if matter_flux_ready else _frontier(matter_flux) + _frontier(matter_flux_active),
            "routes": {
                "transparency_ready": bool(matter_flux.get("E_matterFlux_zero_from_transparency_written")),
                "active_projection_ready": bool(
                    matter_flux_active.get("E_matterFlux_from_active_projection_written")
                ),
            },
        },
        "E_counterterm": {
            "ready": bool(counterterm.get("counterterm_radial_block_of_a_ready")) or bool(
                counterterm_density_variation.get("E_counterterm_from_density_variation_written")
            ),
            "primary_blocker": (
                "none"
                if bool(counterterm.get("counterterm_radial_block_of_a_ready"))
                or bool(counterterm_density_variation.get("E_counterterm_from_density_variation_written"))
                else counterterm_density_variation.get(
                    "primary_blocker",
                    counterterm.get("primary_blocker", "counterterm_radial_block"),
                )
            ),
            "frontier": []
            if bool(counterterm.get("counterterm_radial_block_of_a_ready"))
            or bool(counterterm_density_variation.get("E_counterterm_from_density_variation_written"))
            else _frontier(counterterm_density_variation) + _frontier(counterterm),
            "routes": {
                "density_variation_ready": bool(
                    counterterm_density_variation.get("E_counterterm_from_density_variation_written")
                ),
                "legacy_radial_block_ready": bool(counterterm.get("counterterm_radial_block_of_a_ready")),
            },
        },
    }
    missing = [name for name, data in terms.items() if not data["ready"]]
    ready = not missing
    return {
        "status": "janus-z2-sigma-non-cartan-rsigma-radial-terms-status-gate",
        "active_core": "Z2_tunnel_Sigma",
        "terms": terms,
        "missing_non_cartan_terms": missing,
        "non_cartan_rsigma_radial_terms_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none" if ready else terms[missing[0]]["primary_blocker"],
        "current_frontier": [
            f"{name}: {item}"
            for name, data in terms.items()
            if not data["ready"]
            for item in data["frontier"]
        ],
        "next_required": [] if ready else _required_for_missing(missing),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Non-Cartan R_Sigma Radial Terms Status Gate",
        "",
        f"Ready: `{payload['non_cartan_rsigma_radial_terms_ready']}`",
        f"Missing: `{payload['missing_non_cartan_terms']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
