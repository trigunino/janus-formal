from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.constants import SPEED_OF_LIGHT_KM_S
from janus_lab.models import janus_u0_from_q0


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_unimodular_four_form_sector_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_unimodular_four_form_sector_gate.md"

H0_KM_S_MPC = 70.0
MPC_KM = 3.0856775814913673e19


def _alpha_m_from_q0_h0(q0: float, h0_km_s_mpc: float = H0_KM_S_MPC) -> float:
    h0_s = h0_km_s_mpc / MPC_KM
    u0 = janus_u0_from_q0(q0)
    h_shape = math.sinh(2.0 * u0) / math.cosh(u0) ** 4
    return (h_shape / h0_s) * (SPEED_OF_LIGHT_KM_S * 1000.0)


def build_payload() -> dict[str, Any]:
    paper_q0 = -0.087
    alpha_m = _alpha_m_from_q0_h0(paper_q0)
    h0_s = H0_KM_S_MPC / MPC_KM
    lambda_eff_if_h0 = 3.0 * h0_s**2

    variants = [
        {
            "id": "HT_unimodular_continuous",
            "action": "S_Janus + int Lambda (dA3 - sqrt|g| d4x)",
            "equation": "d Lambda = 0",
            "does": "promotes Lambda/alpha-like scale to global integration constant",
            "closes_no_fit_alpha": False,
            "blocker": "constant is not selected without boundary/state condition",
        },
        {
            "id": "four_form_flux_quantized",
            "action": "S_Janus - 1/2 int F4 wedge *F4 + membrane/flux sector",
            "equation": "F4 = f vol4, Lambda_eff = Lambda_bare + kappa f^2/2",
            "does": "can discretize vacuum energy if int F4 = N q",
            "closes_no_fit_alpha": False,
            "blocker": "Janus does not yet derive q, compact 4-cycle volume, or primitive N",
        },
        {
            "id": "janus_boundary_four_form",
            "action": "S_Janus + boundary-paired A3 on PT/Sigma",
            "equation": "boundary flux could act as M_bridge/alpha charge",
            "does": "best conceptual match to throat/bridge",
            "closes_no_fit_alpha": False,
            "blocker": "needs active PT/Sigma 3-cycle, orientation law, and boundary charge normalization",
        },
    ]

    return {
        "status": "janus-unimodular-four-form-sector-gate",
        "bibliography_anchors": [
            "Henneaux-Teitelboim unimodular gravity",
            "Brown-Teitelboim four-form flux",
            "four-form flux quantization / membrane charge",
        ],
        "candidate_variants": variants,
        "equations_closed": {
            "four_form_constant": True,
            "lambda_as_integration_constant": True,
            "alpha_map_if_lambda_or_H0_given": True,
            "flux_quantization_formal": True,
        },
        "numeric_anchor_diagnostic": {
            "paper_q0": paper_q0,
            "assumed_H0_km_s_Mpc": H0_KM_S_MPC,
            "alpha_m_if_paper_q0_and_H0_supplied": alpha_m,
            "lambda_eff_if_H0_supplied_s_inv_2": lambda_eff_if_h0,
            "diagnostic_only": True,
        },
        "missing_for_no_fit": [
            "Janus-derived A3/F4 sector, not imported by hand",
            "compact cycle or boundary on which flux is defined",
            "charge unit q_F derived from Janus/PT/Sigma",
            "primitive sector law selecting N",
            "map from Lambda_eff or flux energy to the published Janus alpha branch",
        ],
        "deep_verdict": "conditional_open_not_closed",
        "world_interpretation_if_completed": (
            "alpha would be a global vacuum-energy/flux sector, analogous to a conserved "
            "integration constant or quantized four-form charge."
        ),
        "no_fit_alpha_generated": False,
        "next_concrete_test": "derive_or_reject_Janus_A3_F4_boundary_sector_on_PT_Sigma",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Unimodular / Four-Form Sector Gate",
        "",
        f"Deep verdict: `{payload['deep_verdict']}`",
        f"No-fit alpha generated: `{payload['no_fit_alpha_generated']}`",
        "",
        "## Variants",
        "",
        "| Variant | Closes alpha | Blocker |",
        "|---|---:|---|",
        *[
            f"| `{row['id']}` | `{row['closes_no_fit_alpha']}` | {row['blocker']} |"
            for row in payload["candidate_variants"]
        ],
        "",
        "## Diagnostic Anchor",
        "",
        f"- paper q0: `{payload['numeric_anchor_diagnostic']['paper_q0']}`",
        f"- alpha_m if q0 and H0 are supplied: `{payload['numeric_anchor_diagnostic']['alpha_m_if_paper_q0_and_H0_supplied']:.6e}` m",
        "",
        "## Missing For No-Fit",
        "",
        *[f"- {item}" for item in payload["missing_for_no_fit"]],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
