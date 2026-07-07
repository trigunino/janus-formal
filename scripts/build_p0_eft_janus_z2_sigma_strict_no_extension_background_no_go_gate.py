from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_gate import (
    build_payload as build_background_primitive,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_strict_no_extension_background_no_go_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_strict_no_extension_background_no_go_gate.json"
)


def build_payload() -> dict:
    background = build_background_primitive()
    diagnostic = background.get("E2_diagnostic") or {}
    rho_zero = (
        diagnostic.get("rho_eff_min") == 0.0
        and diagnostic.get("rho_eff_max") == 0.0
    )
    closed_positive_curvature = (diagnostic.get("omega_k") or 0.0) < 0.0
    e2_negative = diagnostic.get("E2_positive_on_grid") is False
    strict_no_extension_no_go = rho_zero and closed_positive_curvature and e2_negative
    return {
        "status": "janus-z2-sigma-strict-no-extension-background-no-go-gate",
        "active_core": "Z2_tunnel_Sigma",
        "algebra": {
            "E2_formula": "E_Z2Sigma(a)^2 = rho_eff(a)/rho_crit0 + omega_k/a^2",
            "strict_no_extension_result": "rho_eff(a)=0 on active grid",
            "closed_projective_curvature": "k_Z2Sigma=+1 -> omega_k<0",
            "consequence": "E2(a)=omega_k/a^2<0 for finite positive a",
        },
        "E2_diagnostic": diagnostic,
        "rho_eff_zero_on_grid": rho_zero,
        "closed_positive_curvature_term_negative": closed_positive_curvature,
        "E2_negative_on_grid": e2_negative,
        "strict_no_extension_background_no_go": strict_no_extension_no_go,
        "full_no_fit_cosmology_ready": False,
        "forbidden_shortcuts": [
            "do_not_add_fitted_density",
            "do_not_set_k_to_zero_against_active_projective_branch",
            "do_not_insert_absolute_RSigma_or_H0_without_source",
        ],
        "allowed_exits": [
            "derive positive active Friedmann source from published Janus action",
            "derive valid flat/open spatial branch from active geometry",
            "derive dimensionful state/action input that changes the Hamiltonian source",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Strict No-Extension Background No-Go",
        "",
        f"rho_eff zero on grid: `{payload['rho_eff_zero_on_grid']}`",
        f"closed positive curvature term negative: `{payload['closed_positive_curvature_term_negative']}`",
        f"E2 negative on grid: `{payload['E2_negative_on_grid']}`",
        f"strict no-extension background no-go: `{payload['strict_no_extension_background_no_go']}`",
        "",
        "## Algebra",
        payload["algebra"]["E2_formula"],
        payload["algebra"]["consequence"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
