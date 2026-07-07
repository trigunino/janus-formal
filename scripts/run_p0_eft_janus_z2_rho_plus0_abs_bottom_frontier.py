from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_rho_plus0_abs_symbolic_closure_gate import (
    build_payload as build_rho_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_area_occupation_selection_gate import (
    build_payload as build_area_occupation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate import (
    build_payload as build_radius_payload,
)
from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload as build_global_energy_payload,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_state_sector_gate import (
    build_payload as build_alpha_state_sector_payload,
)
from scripts.build_p0_eft_janus_z2_published_exact_solution_scale_frontier_gate import (
    build_payload as build_exact_solution_scale_payload,
)
from scripts.build_p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate import (
    build_payload as build_alpha_to_energy_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_noether_occupation_degeneracy import (
    build_payload as build_noether_occupation_payload,
)


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_rho_plus0_abs_bottom_frontier.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_rho_plus0_abs_bottom_frontier.md")


def _blocked(payload: dict[str, Any]) -> list[str]:
    value = (
        payload.get("blocked_by")
        or payload.get("validation_errors")
        or payload.get("primary_blocker")
        or []
    )
    return value if isinstance(value, list) else [str(value)]


def build_payload() -> dict[str, Any]:
    rho = build_rho_payload(write_output=True)
    noether = build_noether_occupation_payload()
    occupation = build_area_occupation_payload()
    radius = build_radius_payload()
    global_energy = build_global_energy_payload(write_output=True)
    alpha_state = build_alpha_state_sector_payload(write_output=True)
    exact_scale = build_exact_solution_scale_payload()
    alpha_to_energy = build_alpha_to_energy_payload(write_output=True)
    blockers = {
        "rho_plus0_abs": _blocked(rho),
        "noether_occupation": _blocked(noether),
        "area_occupation_selector": _blocked(occupation),
        "curvature_radius": _blocked(radius),
        "published_global_energy_constant": _blocked(global_energy),
        "exact_solution_alpha_state_sector": _blocked(alpha_state),
        "published_exact_solution_scale": _blocked(exact_scale),
        "exact_solution_alpha_to_global_energy": _blocked(alpha_to_energy),
    }
    n_occ_closed = bool(noether["topology_selects_unique_occupation"]) or bool(
        occupation["occupation_selector_ready"]
    )
    r_curv_closed = bool(radius["background_curvature_radius_input_written"])
    return {
        "status": "janus-z2-rho-plus0-abs-bottom-frontier",
        "active_core": "Z2_tunnel_Sigma",
        "rho_plus0_abs_formula_closed": True,
        "rho_plus0_abs_ready": rho["rho_plus0_abs_ready"],
        "N_occ_Z2Sigma_ready": n_occ_closed,
        "R_curv_Z2Sigma_ready": r_curv_closed,
        "published_global_energy_constant_route_ready": global_energy[
            "global_energy_constant_route_ready"
        ],
        "alpha_state_sector_ready": alpha_state["alpha_state_sector_ready"],
        "published_exact_solution_scale_ready": exact_scale["scale_ready"],
        "alpha_to_global_energy_ready": alpha_to_energy[
            "alpha_to_global_energy_ready"
        ],
        "first_physical_blockers": [
            key
            for key, ready in {
                "N_occ_Z2Sigma": n_occ_closed,
                "R_curv_Z2Sigma": r_curv_closed,
            }.items()
            if not ready
        ],
        "bottom_statement": (
            "Z2 topology and Noether conservation define projection algebra, but "
            "do not select an occupation number. Projective/throat topology defines "
            "the closed volume law, but not a dimensional curvature radius. Thus "
            "rho_plus0_abs is closed as a formula, not as a number."
        ),
        "upstream_blockers": blockers,
        "forbidden_shortcuts": [
            "choose_N_occ_by_observation",
            "choose_R_curv_by_observation",
            "use_LCDM_or_Planck_density",
            "collapse_two_sector_bulk_into_rho_eff_shortcut",
            "reuse_legacy_Z4",
        ],
        "allowed_non_rustine_exits": [
            "derive_N_occ_from_state_selection_or_flux_lock",
            "derive_R_curv_from_active_RSigma_embedding_certificate",
            "derive_both_from_a_single_global_bimetric_state_solution",
            "derive_published_global_energy_constant_E_and_present_bimetric_weights",
            "derive_exact_solution_alpha_or_H0_from_non_observational_clock",
            "derive_alpha_m_then_use_E_mass_equals_minus_alpha_c2_over_2piG",
            "provide_alpha_as_exact_solution_integration_constant_state_sector",
        ],
        "gate_passed": False,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 rho_plus0_abs Bottom Frontier",
        "",
        f"Formula closed: `{payload['rho_plus0_abs_formula_closed']}`",
        f"rho_plus0_abs ready: `{payload['rho_plus0_abs_ready']}`",
        f"First physical blockers: `{payload['first_physical_blockers']}`",
        "",
        payload["bottom_statement"],
        "",
        "## Allowed Non-Rustine Exits",
    ]
    lines.extend(f"- `{item}`" for item in payload["allowed_non_rustine_exits"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
