from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_and_residual_counterterm_bibliography_gate import (
    build_payload as build_bibliography_route,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_metric_f_pm_route_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bulk_metric_f_pm_route_gate.json")


def build_payload() -> dict:
    bibliography = build_bibliography_route()
    routes = {
        "static_areal_f_pm_route": {
            "formula": "ds_pm^2 = -f_pm(R)dT_pm^2 + f_pm(R)^-1 dR^2 + R^2 dOmega^2",
            "requires": [
                "active_static_areal_bulk_chart_pm",
                "R_Sigma(a) in that chart",
                "proper-time shell gauge",
                "f_pm(R) and partial_R f_pm derived from Janus/Z2 bulk equations",
            ],
            "ready": False,
            "diagnostic_only_until_chart_derived": True,
        },
        "active_embedding_second_form_route": {
            "formula": "K_ab^pm = -n_mu^pm(partial_a partial_b X_pm^mu + Gamma^mu_pm alpha beta e_a^alpha e_b^beta)",
            "requires": [
                "R_Sigma_solution_certificate",
                "X_plus_minus(a,xi)",
                "tangent frames",
                "second embedding derivatives",
                "Christoffels and unit normals",
            ],
            "ready": False,
            "active_default_route": True,
        },
    }
    return {
        "status": "janus-z2-sigma-bulk-metric-f-pm-route-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_route": {
            "gate": bibliography["status"],
            "checked": bibliography["bibliography_checked"],
            "DeltaK_route": bibliography["route_decision"]["DeltaK_route"],
            "non_GHY_counterterm_closes_for_free": bibliography[
                "non_GHY_counterterm_closes_for_free"
            ],
        },
        "routes": routes,
        "forbidden_substitutions": [
            "Schwarzschild f_pm without Janus/Z2 static areal chart",
            "FLRW f_pm shortcut without deriving equivalence to the active embedding route",
            "Planck/LambdaCDM-derived background parameters",
            "archived Z4 geometry",
        ],
        "static_f_pm_formula_declared": True,
        "static_f_pm_values_ready": False,
        "active_embedding_second_form_route_declared": True,
        "active_embedding_second_form_route_preferred": True,
        "DeltaK_value_route_ready": False,
        "primary_blocker": "R_Sigma_solution_certificate_and_active_embedding_manifest",
        "next_required": [
            "solve R_Sigma(a) from the active Sigma radial equation",
            "derive active X_plus/X_minus and the unit normal/tangent/second-form stencil",
            "compute K_s/tau from embedding second form",
            "derive static areal f_pm only if an active Janus/Z2 bulk chart is later proven",
        ],
        "verdict": (
            "The dynamic-shell f_pm formulas are valid only after deriving an active static "
            "areal bulk chart. For the current Z2/Sigma tunnel model, the mathematically safe "
            "route is the embedding second-form computation of K_ab. No f_pm value is accepted "
            "as an input shortcut."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Bulk Metric f_pm Route Gate",
        "",
        f"Static f_pm values ready: `{payload['static_f_pm_values_ready']}`",
        f"Embedding route preferred: `{payload['active_embedding_second_form_route_preferred']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Forbidden substitutions",
    ]
    lines.extend(f"- {item}" for item in payload["forbidden_substitutions"])
    lines.extend(["", "## Next required"])
    lines.extend(f"- {item}" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
