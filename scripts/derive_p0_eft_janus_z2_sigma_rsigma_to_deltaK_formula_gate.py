from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_deltaK_dynamic_shell_bibliography_gate import (
    build_payload as build_biblio,
)
from scripts.derive_p0_eft_janus_z2_sigma_bulk_metric_f_pm_route_gate import (
    build_payload as build_f_pm_route,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_to_deltaK_formula_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_to_deltaK_formula_gate.json")


def build_payload() -> dict:
    biblio = build_biblio()
    f_pm_route = build_f_pm_route()
    formulas = {
        "K_s_pm": "K_s^pm = epsilon_pm * sqrt(Rdot^2 + f_pm(R)) / R",
        "K_tau_pm": "K_tau^pm = epsilon_pm * (Rddot + 0.5 f_pm'(R)) / sqrt(Rdot^2 + f_pm(R))",
        "DeltaK_s": "DeltaK_s = K_s_plus + eps_Z2 K_s_minus",
        "DeltaK_tau": "DeltaK_tau = K_tau_plus + eps_Z2 K_tau_minus",
        "embedding_equivalent": "K_ab^pm = -n_mu^pm(partial_a partial_b X_pm^mu + Gamma^mu_pm alpha beta partial_a X_pm^alpha partial_b X_pm^beta)",
    }
    inputs = {
        "dynamic_shell_bibliography_ready": bool(biblio["gate_passed"]),
        "R_Sigma_of_a_ready": False,
        "proper_time_gauge_ready": False,
        "Rdot_Rddot_ready": False,
        "f_plus_f_minus_ready": False,
        "df_plus_df_minus_ready": False,
        "orientation_epsilons_ready": True,
        "active_bulk_metric_route_decision_ready": True,
    }
    formula_ready = inputs["dynamic_shell_bibliography_ready"] and inputs["orientation_epsilons_ready"]
    values_ready = all(inputs.values())
    return {
        "status": "janus-z2-sigma-rsigma-to-deltaK-formula-gate",
        "active_core": "Z2_tunnel_Sigma",
        "formulas": formulas,
        "inputs": inputs,
        "bulk_metric_route": {
            "gate": f_pm_route["status"],
            "static_f_pm_values_ready": f_pm_route["static_f_pm_values_ready"],
            "embedding_second_form_route_preferred": f_pm_route[
                "active_embedding_second_form_route_preferred"
            ],
            "forbidden_substitutions": f_pm_route["forbidden_substitutions"],
            "primary_blocker": f_pm_route["primary_blocker"],
        },
        "formula_ready": formula_ready,
        "values_ready": values_ready,
        "gate_passed": formula_ready,
        "primary_blocker": (
            "none"
            if values_ready
            else "R_Sigma_solution_certificate_and_active_embedding_manifest"
        ),
        "next_required": [
            "derive R_Sigma(a) and shell proper-time gauge",
            "derive active embedding second-form manifest for K_ab, or derive a Janus/Z2 static areal chart before using f_pm",
            "derive Rdot/Rddot and f'_plus/f'_minus only on the static areal chart route",
            "evaluate K_s/tau plus/minus and DeltaK_s/tau",
        ],
        "verdict": (
            "The standard dynamic-shell map from R_Sigma to DeltaK_s/tau is now explicit. "
            "It is formula-ready but not value-ready until either the active embedding "
            "second-form manifest is supplied, or an active static areal Janus/Z2 bulk "
            "chart derives f_pm(R) and the shell kinematics."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma R_Sigma to DeltaK Formula Gate",
        "",
        f"Formula ready: `{payload['formula_ready']}`",
        f"Values ready: `{payload['values_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
