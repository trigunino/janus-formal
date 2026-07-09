from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.models import JanusExpansion


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_early_time_orbifold_ruler_closure_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_early_time_orbifold_ruler_closure_gate.md"

PUBLISHED_Q0 = -0.087
FIDUCIAL_DRAG_MARKER = 1059.0


def _zmax_from_q0(q0: float) -> float:
    return float(JanusExpansion.from_q0(q0).z_max)


def _route(
    route_id: str,
    title: str,
    conceptual_move: str,
    current_result: str,
    missing: list[str],
    status: str,
    next_test: str,
    can_unlock_bao_if_derived: bool = True,
) -> dict[str, Any]:
    return {
        "id": route_id,
        "title": title,
        "conceptual_move": conceptual_move,
        "can_unlock_bao_if_derived": can_unlock_bao_if_derived,
        "current_result": current_result,
        "missing_non_rustine_inputs": missing,
        "status": status,
        "next_test": next_test,
    }


def build_payload() -> dict[str, Any]:
    published_zmax = _zmax_from_q0(PUBLISHED_Q0)
    q0_drag_ceiling = -1.0 / (2.0 * FIDUCIAL_DRAG_MARKER)
    late_branch_reaches_drag = published_zmax >= FIDUCIAL_DRAG_MARKER

    routes = [
        _route(
            "orbifold_redshift_map",
            "Orbifold redshift map",
            "Let observed redshift be a projection of a global Janus/orbifold evolution parameter.",
            (
                "Conceptually can bypass finite late-branch z_max, but only if the map is derived "
                "from null-geodesic energy transport or orbifold boundary transport."
            ),
            [
                "derive z_obs = F_orbifold(z_global) from geometry/transport",
                "prove low-z identity limit",
                "prove high-z lift reaches z_d without arbitrary compression",
            ],
            "blocked_requires_derived_orbifold_transport_map",
            "derive the redshift generator from photon energy transport across the Z2/Sigma projection",
        ),
        _route(
            "early_time_sister_branch",
            "Early-time sister branch",
            "Treat the SN branch as the late-time visible branch and derive a distinct pre-drag branch matched by Janus/Z2 data.",
            (
                "Best conceptual route for keeping the late-time paper branch intact; still needs a "
                "matching condition and H_J(z) before drag."
            ),
            [
                "derive late-to-early matching condition",
                "derive pre-drag H_J(z)",
                "prove the early branch reaches z_d for interior q0",
            ],
            "blocked_requires_branch_matching_and_predrag_hubble",
            "derive a Janus/Z2 matching condition at the transition surface or throat projection",
        ),
        _route(
            "topological_spectrum_ruler",
            "Topological spectrum ruler",
            "Make the BAO ruler an eigenlength/period of Sigma/orbifold geometry rather than a Lambda-CDM sound horizon.",
            (
                "Can produce a geometric ruler in principle, but does not yet supply an absolute scale "
                "or a coupling to photon-baryon acoustic physics."
            ),
            [
                "derive a closed-cycle/eigenvalue problem on Sigma/orbifold",
                "derive absolute scale, not just dimensionless eigenvalue",
                "derive coupling of this eigenlength to photon-baryon drag/acoustic modes",
            ],
            "blocked_requires_absolute_scale_and_plasma_coupling",
            "derive the Sigma/orbifold eigenproblem and its physical coupling to the plasma sector",
        ),
        _route(
            "projected_photon_baryon_plasma",
            "Projected photon-baryon plasma",
            "Project the global Janus two-sector matter/radiation content to visible photon-baryon primitives.",
            (
                "Most concrete calculational route: if c_s^J, Gamma_drag^J, z_d^J and H_J are derived, "
                "r_d^J follows directly by integration."
            ),
            [
                "derive c_s^J from active rho_b^J and rho_gamma^J",
                "derive Gamma_drag^J from n_e^J, sigma_T^J and baryon loading",
                "solve Gamma_drag^J(z_d^J)=H_J(z_d^J)",
                "derive H_J in the pre-drag domain",
            ],
            "blocked_requires_active_plasma_primitives",
            "start from projected rho_b/rho_gamma/n_e and derive c_s^J plus Gamma_drag^J",
        ),
    ]

    return {
        "status": "janus-early-time-orbifold-ruler-closure-gate",
        "native_bao_problem": {
            "observable_vector": ["D_M^J/r_d^J", "D_H^J/r_d^J", "D_V^J/r_d^J"],
            "native_ruler_formula": "r_d^J = integral c_s^J(z)/H_J(z) dz up to z_d^J",
            "forbidden": [
                "Planck/Lambda-CDM r_d reuse",
                "alpha fit as BAO repair",
                "post-hoc anisotropic ruler patch",
            ],
        },
        "late_branch_domain": {
            "q0": PUBLISHED_Q0,
            "z_max": published_zmax,
            "fiducial_drag_redshift_marker": FIDUCIAL_DRAG_MARKER,
            "q0_required_to_reach_drag_marker": q0_drag_ceiling,
            "late_branch_reaches_drag_marker": late_branch_reaches_drag,
        },
        "orbifold_relevance": (
            "Orbifold/Z2 helps only if it supplies a derived redshift map, a branch matching law, "
            "a spectral ruler with scale, or a projection law for photon-baryon primitives. "
            "Topology alone does not produce r_d^J."
        ),
        "routes": routes,
        "route_count": len(routes),
        "closed_route_ids": [route["id"] for route in routes if route["status"] == "closed"],
        "blocked_route_ids": [route["id"] for route in routes if route["status"].startswith("blocked")],
        "best_next_route": "projected_photon_baryon_plasma",
        "second_next_route": "early_time_sister_branch",
        "native_early_time_ruler_ready": False,
        "all_routes_pushed_to_current_bottom": True,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    domain = payload["late_branch_domain"]
    lines = [
        "# Janus Early-Time Orbifold Ruler Closure Gate",
        "",
        "## Domain obstruction",
        "",
        f"- q0: `{domain['q0']}`",
        f"- z_max: `{domain['z_max']:.6g}`",
        f"- drag marker: `{domain['fiducial_drag_redshift_marker']}`",
        f"- q0 required to reach drag marker: `{domain['q0_required_to_reach_drag_marker']:.6g}`",
        f"- late branch reaches drag marker: `{domain['late_branch_reaches_drag_marker']}`",
        "",
        "## Orbifold relevance",
        "",
        payload["orbifold_relevance"],
        "",
        "## Routes",
        "",
    ]
    for route in payload["routes"]:
        lines.extend(
            [
                f"### {route['title']}",
                "",
                f"- status: `{route['status']}`",
                f"- move: {route['conceptual_move']}",
                f"- current result: {route['current_result']}",
                "- missing:",
                *[f"  - `{item}`" for item in route["missing_non_rustine_inputs"]],
                f"- next test: `{route['next_test']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Ranking",
            "",
            f"- best next route: `{payload['best_next_route']}`",
            f"- second next route: `{payload['second_next_route']}`",
            f"- native early-time ruler ready: `{payload['native_early_time_ruler_ready']}`",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
