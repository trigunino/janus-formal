from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.models import JanusExpansion
from scripts.build_p0_eft_janus_z2_alpha_observational_fit_gate import (
    build_payload as build_alpha_fit_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_minimal_contract_gate import (
    build_payload as build_scale_free_contract_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_sound_ruler_gate import (
    build_payload as build_sound_ruler_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_native_bao_ruler_contract_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_native_bao_ruler_contract_gate.md"


def _zmax_from_q0(q0: float) -> float:
    return JanusExpansion.from_q0(q0).z_max


def build_payload() -> dict[str, Any]:
    fit = build_alpha_fit_payload()
    scale_free = build_scale_free_contract_payload()
    sound = build_sound_ruler_payload()

    q0_published = -0.087
    q0_sn_full_bao = float(fit["best_fit"]["SN_full_cov_plus_BAO"]["q0"])
    fiducial_drag_redshift_marker = 1059.0
    q0_drag_ceiling = -1.0 / (2.0 * fiducial_drag_redshift_marker)
    published_zmax = _zmax_from_q0(q0_published)
    selected_zmax = _zmax_from_q0(q0_sn_full_bao)

    primitives_available = bool(scale_free["primitive_physical_inputs_available"])
    sound_evaluated = bool(sound["bao_sound_ruler_evaluated"])
    proxy_rejected = fit["janus_bao_status"] == "rejected_in_current_background_proxy"
    return {
        "status": "janus-native-bao-ruler-contract-gate",
        "native_contract": {
            "DM_J": "D_M^J(z) from visible-sector null geodesics and curvature S_k",
            "DH_J": "D_H^J(z)=c/H_J(z)",
            "DV_J": "D_V^J=(z D_M^2 D_H)^(1/3)",
            "rd_J": "r_d^J = integral_{z_d^J}^{z_max or infinity} c_s^J(z)/H_J(z) dz",
            "drag_condition": "Gamma_drag^J(z_d^J)=H_J(z_d^J)",
            "observable_vector": "{D_M^J/r_d^J, D_H^J/r_d^J, D_V^J/r_d^J}",
        },
        "strict_primitives_required": [
            "E_Z2Sigma(z)=H_J/H0",
            "c_s^J/c from active photon-baryon plasma",
            "Gamma_drag^J/H0 from active n_e, rho_b, rho_gamma, sigma_T",
            "omega_k^J from active curvature convention",
            "redshift domain reaching z_d^J",
        ],
        "current_assets": {
            "scale_free_primitives_available": primitives_available,
            "sound_ruler_formula_ready": sound["bao_sound_ruler_formula_ready"],
            "sound_ruler_evaluated": sound_evaluated,
            "current_background_proxy_bao_status": fit["janus_bao_status"],
        },
        "redshift_domain_audit": {
            "formula": "z_max(q0) = -1/(2 q0) for q0 < 0",
            "fiducial_drag_redshift_marker": fiducial_drag_redshift_marker,
            "q0_required_to_reach_marker": f"q0 >= {q0_drag_ceiling:.6g}",
            "published_q0": q0_published,
            "published_q0_zmax": published_zmax,
            "published_q0_reaches_marker": published_zmax > fiducial_drag_redshift_marker,
            "sn_bao_selected_q0": q0_sn_full_bao,
            "sn_bao_selected_zmax": selected_zmax,
            "sn_bao_selected_reaches_marker": selected_zmax > fiducial_drag_redshift_marker,
        },
        "deep_verdict": (
            "A native Janus BAO contract is formulated but not evaluable. "
            "For an interior published-like q0, the normalized exact branch does "
            "not reach a high-redshift drag epoch. The q0->0 boundary selected by "
            "SN+BAO is precisely the regime where a pre-drag domain reappears. "
            "Thus BAO cannot be rescued by fitting alpha alone; it needs either "
            "a native early-time branch/redshift map or a derived drag/ruler sector."
        ),
        "native_bao_contract_formulated": True,
        "native_bao_contract_evaluable": False,
        "current_proxy_rejected": proxy_rejected,
        "next_non_rustine_options": [
            "derive a Janus early-time branch that reaches z_d^J for interior q0",
            "derive a modified Janus redshift map for pre-drag physics",
            "derive active photon-baryon plasma primitives and z_d^J",
            "then rerun DESI BAO without fitted Planck/LCDM r_d",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    audit = payload["redshift_domain_audit"]
    lines = [
        "# Janus Native BAO/Ruler Contract Gate",
        "",
        "## Contract",
        "",
        *[f"- `{key}`: {value}" for key, value in payload["native_contract"].items()],
        "",
        "## Redshift Domain Audit",
        "",
        f"- Formula: `{audit['formula']}`",
        f"- Drag marker: `{audit['fiducial_drag_redshift_marker']}`",
        f"- q0 required to reach marker: `{audit['q0_required_to_reach_marker']}`",
        f"- Published-like q0: `{audit['published_q0']}`, zmax `{audit['published_q0_zmax']:.6g}`",
        f"- SN+BAO selected q0: `{audit['sn_bao_selected_q0']}`, zmax `{audit['sn_bao_selected_zmax']:.6g}`",
        "",
        "## Verdict",
        "",
        payload["deep_verdict"],
        "",
        "## Next Non-Rustine Options",
        "",
        *[f"- {item}" for item in payload["next_non_rustine_options"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
