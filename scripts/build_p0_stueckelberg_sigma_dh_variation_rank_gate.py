from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_same_phi_l_cuu_bridge import build_payload as build_cuu_bridge
from scripts.build_p0_sigma_dh_equivalence_gate import build_payload as build_sigma_gate
from scripts.build_p0_stueckelberg_explicit_action_test import (
    build_payload as build_explicit_action,
)
from scripts.build_p0_stueckelberg_map_constraint_counting import (
    build_payload as build_constraint_counting,
)
from scripts.build_p0_stueckelberg_two_diffeo_route import (
    build_payload as build_two_diffeo,
)


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sigma_dh_variation_rank_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sigma_dh_variation_rank_gate.json")


def build_payload() -> dict:
    sigma = build_sigma_gate()
    two_diffeo = build_two_diffeo()
    action = build_explicit_action()
    counting = build_constraint_counting()
    cuu = build_cuu_bridge()
    dimension = 4
    lorentz_rank = dimension * (dimension - 1) // 2
    symmetric_rank = dimension * (dimension + 1) // 2
    gl_rank = dimension * dimension
    return {
        "description": "Rank gate for whether the current Stueckelberg L variation can select Sigma_alpha/D_alpha H.",
        "status": "stueckelberg-lorentz-variation-does-not-select-sigma-dh",
        "depends_on": [
            "p0_sigma_dh_equivalence_gate",
            "p0_stueckelberg_two_diffeo_route",
            "p0_stueckelberg_explicit_action_test",
            "p0_stueckelberg_map_constraint_counting",
            "p0_same_phi_l_cuu_bridge",
        ],
        "dimension": dimension,
        "rank_count": {
            "lorentz_tangent_antisymmetric": lorentz_rank,
            "eta_symmetric_strain_sigma": symmetric_rank,
            "raw_gl_lgeom": gl_rank,
            "sigma_rank_hit_by_lorentz_variation": 0,
        },
        "linearized_variation_identity": (
            "if delta L = A L and A^dagger_eta=-A, then "
            "delta H = eta^{-1} deltaL^T eta L + eta^{-1} L^T eta deltaL = 0"
        ),
        "stueckelberg_route_status": two_diffeo["status"],
        "explicit_action_status": action["status"],
        "constraint_count_status": counting["status"],
        "cuu_bridge_status": cuu["status"],
        "sigma_equivalence_status": sigma["status"],
        "current_l_field": "Lorentz/tetrad map L with L^T eta L=eta",
        "sigma_target_field": "eta-symmetric raw strain Sigma_alpha or equivalently D_alpha H",
        "projection_result": (
            "current E_L lives in the Lorentz tangent channel; it can constrain Omega/L "
            "orientation but has zero direct rank on Sigma_alpha/D_alpha H"
        ),
        "routes_left": [
            "extend the Stueckelberg field to raw L_geom in GL(4) and derive H/Sigma equations",
            "introduce H=eta^{-1}L_geom^T eta L_geom as an explicit variational field",
            "derive Sigma/DH from a relative nonmetricity equation instead of Lorentz E_L",
        ],
        "guardrails": [
            "do not reinterpret Lorentz E_L equations as trace-free strain equations",
            "do not add GL/raw L_geom strain without source action and ghost/stability gate",
            "do not use dust Cuu bridge as dynamic Sigma selection",
            "do not recover only determinant/B4vol trace and claim full Q_TF closure",
        ],
        "stueckelberg_selects_sigma_dh": False,
        "gl_extension_required_for_sigma": True,
        "same_phi_l_cuu_bridge_still_valid_conditionally": cuu["same_phi_l_bridge_closed"],
        "overconstraint_risk_increases_if_gl_added": True,
        "ghost_gate_required_if_gl_added": True,
        "prediction_ready": False,
        "notable_improvement": (
            "The Stueckelberg route is no longer vaguely conditional for Sigma: the "
            "current Lorentz-only L variation has zero direct rank on D_alpha H."
        ),
        "remaining_lock": (
            "Build or reject a source-derived GL/H/nonmetricity extension; the current "
            "Lorentz Stueckelberg action cannot by itself select the strain channel."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Sigma/DH Variation Rank Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Current L field: `{payload['current_l_field']}`",
        f"Sigma target field: `{payload['sigma_target_field']}`",
        f"Stueckelberg selects Sigma/DH: {payload['stueckelberg_selects_sigma_dh']}",
        f"GL extension required for Sigma: {payload['gl_extension_required_for_sigma']}",
        f"Overconstraint risk increases if GL added: {payload['overconstraint_risk_increases_if_gl_added']}",
        f"Ghost gate required if GL added: {payload['ghost_gate_required_if_gl_added']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rank Count",
        "",
    ]
    for key, value in payload["rank_count"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Linearized Identity",
            "",
            f"`{payload['linearized_variation_identity']}`",
            "",
            "## Projection Result",
            "",
            payload["projection_result"],
            "",
            "## Routes Left",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["routes_left"])
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
    lines.extend(["", "## Result", "", payload["notable_improvement"], ""])
    lines.extend([f"Remaining lock: {payload['remaining_lock']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
