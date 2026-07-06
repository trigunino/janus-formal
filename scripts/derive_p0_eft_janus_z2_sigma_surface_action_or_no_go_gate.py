from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_p0_eft_janus_z2_sigma_counterterm_chain import build_payload as counterterm_chain
from scripts.write_p0_eft_janus_z2_sigma_mpla_schwarzschild_throat_local_model import (
    build_payload as mpla_model,
)
from scripts.derive_p0_eft_janus_z2_sigma_souriau_boundary_hamiltonian_attempt import (
    build_payload as souriau_hamiltonian,
)
from scripts.write_p0_eft_janus_z2_sigma_rsigma_over_ell_collar_from_projective_stereographic import (
    build_payload as projective_ratio,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_surface_action_or_no_go_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_surface_action_or_no_go_gate.json")


def build_payload() -> dict:
    counterterm = counterterm_chain()
    mpla = mpla_model()
    souriau = souriau_hamiltonian()
    ratio = projective_ratio()
    no_extension_inputs = {
        "mpla_local_throat": mpla["minimal_throat_ready"],
        "projective_ratio": ratio["ratio_solution_ready"],
        "souriau_global_charge": souriau["moment_map_charge_Q_sigma_declared"],
        "souriau_local_density": souriau["local_density_from_charge_available"],
        "counterterm_chain_passed": counterterm["chain_passed"],
        "surface_hk_coefficients_available": "surface_hk_active_density_coefficients"
        not in counterterm["independent_missing_inputs"],
        "counterterm_trace_inputs_available": "counterterm_trace_residual_inputs"
        not in counterterm["independent_missing_inputs"],
    }
    no_unique_surface_action = (
        no_extension_inputs["mpla_local_throat"]
        and no_extension_inputs["projective_ratio"]
        and no_extension_inputs["souriau_global_charge"]
        and not no_extension_inputs["souriau_local_density"]
        and not no_extension_inputs["counterterm_chain_passed"]
    )
    return {
        "status": "janus-z2-sigma-surface-action-or-no-go-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "no_extension_surface_action_decision",
        "no_extension_inputs": no_extension_inputs,
        "no_unique_surface_action_from_current_inputs": no_unique_surface_action,
        "E_counterterm_closed": False,
        "sigma_alpha_h_closed": False,
        "full_no_fit_prediction_ready": False,
        "accepted_positive_results": {
            "MPLA_regular_throat_ratio": "R_Sigma/R_s = 1",
            "projective_collar_ratio": "R_Sigma/ell = 1",
            "Souriau_charge_reduction": "Q_Sigma = N_occ",
            "matter_flux": "local Sigma flux zero",
            "Holst_Nieh_Yan": "torsionless radial zero",
        },
        "missing_for_closure": [
            "active local Sigma surface density L_Sigma(h,K,...)",
            "or alpha_h/alpha_K from a boundary Hamiltonian variation",
            "or counterterm_trace_residual_inputs with R_h_trace/R_K_trace",
            "or explicit allowed surface-action extension",
        ],
        "forbidden_shortcuts": [
            "set E_counterterm = 0 by assumption",
            "differentiate Souriau global charge as local density",
            "use MPLA R_s as observed BAO scale",
            "fit a0..a3 observationally",
            "reuse archived Z4 coefficients",
        ],
        "decision": "no_extension_surface_action_underselected",
        "recommended_next": (
            "Either allow an explicit Sigma surface-action extension, or keep the "
            "pure model open and restrict claims to topology/local flux identities."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface Action Or No-Go Gate",
        "",
        f"No unique surface action from current inputs: `{payload['no_unique_surface_action_from_current_inputs']}`",
        f"E_counterterm closed: `{payload['E_counterterm_closed']}`",
        f"Sigma alpha_h closed: `{payload['sigma_alpha_h_closed']}`",
        f"Decision: `{payload['decision']}`",
        "",
        "## Accepted Positive Results",
    ]
    lines.extend(f"- `{k}`: `{v}`" for k, v in payload["accepted_positive_results"].items())
    lines.extend(["", "## Missing For Closure"])
    lines.extend(f"- `{item}`" for item in payload["missing_for_closure"])
    lines.extend(["", "## Forbidden Shortcuts"])
    lines.extend(f"- `{item}`" for item in payload["forbidden_shortcuts"])
    lines.extend(["", f"Recommended next: {payload['recommended_next']}"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
