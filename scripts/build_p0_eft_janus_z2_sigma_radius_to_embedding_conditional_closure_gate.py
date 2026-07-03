from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_radius_to_embedding_conditional_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_radius_to_embedding_conditional_closure_gate.json")


def build_payload() -> dict:
    declared = {
        "thin_shell_embedding_bibliography_checked": True,
        "radius_gauge_transport_imported": True,
        "embedding_gauge_equation_imported": True,
        "R_Sigma_input_declared": True,
        "proper_time_gauge_integral_declared": True,
        "radial_embedding_insertion_declared": True,
        "X_plus_minus_conditional_map_declared": True,
        "observational_radius_fit_forbidden": True,
    }
    conditional = {
        "embedding_gauge_equations_ready": True,
        "proper_time_gauge_integrated_conditionally": True,
        "radial_embedding_inserted_conditionally": True,
        "X_plus_minus_conditionally_derived": True,
    }
    closure = {
        "R_Sigma_of_a_ready": False,
        "X_plus_minus_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-radius-to-embedding-conditional-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Darmois-Israel thin-shell hypersurface embedding",
            "Poisson-Visser thin-shell throat proper-time kinematics",
            "dynamic shell induced-metric normalization",
        ],
        "source_links": [
            "https://link.aps.org/doi/10.1103/PhysRevD.52.7318",
            "https://arxiv.org/pdf/gr-qc/9510052",
        ],
        "bibliography_result": (
            "Standard thin-shell kinematics fixes the time embedding from the induced "
            "proper-time normalization once R_Sigma(a) is supplied. It does not derive "
            "the active Janus throat-radius law."
        ),
        "declared": declared,
        "conditional": conditional,
        "closure": closure,
        "formulas": {
            "embedding_ansatz": "X_pm^mu(a,xi) = (T_pm(a), R_Sigma(a), xi)",
            "time_integral": "T_pm(a) = integral sqrt((1+G_pm(R_Sigma)(dR_Sigma/dtau)^2)/F_pm(R_Sigma)) d tau",
            "radial_insert": "r_pm(a) = R_Sigma(a)",
            "conditional_transport": "R_Sigma(a) + gauge equations => X_+/-^mu(a,xi)",
        },
        "conditional_embedding_ledger_declared": all(declared.values()),
        "radius_to_embedding_conditional_ready": all(declared.values()) and all(conditional.values()),
        "radius_to_embedding_unconditional_ready": all(declared.values())
        and all(conditional.values())
        and all(closure.values()),
        "next_required": [
            "solve_R_Sigma_of_a_from_throat_radius_variational_equation",
            "instantiate_conditional_embedding_map_with_R_Sigma_of_a",
            "feed_X_plus_minus_of_a_to_tangent_normal_and_pullback_gates",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Radius To Embedding Conditional Closure Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Conditional ready: `{payload['radius_to_embedding_conditional_ready']}`",
        f"Unconditional ready: `{payload['radius_to_embedding_unconditional_ready']}`",
        "",
        "## Bibliography",
        payload["bibliography_result"],
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
