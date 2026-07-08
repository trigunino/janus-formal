from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_pt_boundary_chi_stationarity_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_pt_boundary_chi_stationarity_gate.md"


def build_payload() -> dict[str, Any]:
    candidates = [
        {
            "id": "pure_PT_even_functional",
            "form": "B_PT(chi)=B_PT(-chi), e.g. c2 chi^2 + c4 chi^4 + ...",
            "stationarity": "dB/dchi = 2 c2 chi + 4 c4 chi^3 + ... = 0",
            "selects_nonzero_chi": False,
            "reason": "PT parity alone makes the functional even; it gives chi=0 unless extra coefficients create nonzero extrema.",
        },
        {
            "id": "fixed_norm_constraint",
            "form": "B_PT + lambda(chi^2-chi0^2)",
            "stationarity": "chi^2=chi0^2",
            "selects_nonzero_chi": False,
            "reason": "nonzero value is chi0, an external scale/charge unless derived elsewhere.",
        },
        {
            "id": "boundary_charge_pairing",
            "form": "B_PT = chi Q_PT + V(chi)",
            "stationarity": "Q_PT + V'(chi)=0",
            "selects_nonzero_chi": False,
            "reason": "requires a nonzero PT boundary charge Q_PT or potential scale.",
        },
        {
            "id": "flux_locked_stationarity",
            "form": "chi proportional to n q_LL / A_Sigma",
            "stationarity": "flux sector fixes chi after q_LL and A_Sigma are derived",
            "selects_nonzero_chi": False,
            "reason": "reduces to LL auxiliary flux route; q_LL/A_Sigma still missing.",
        },
    ]
    return {
        "status": "janus-pt-boundary-chi-stationarity-gate",
        "question": "Can PT boundary stationarity alone select nonzero chi_LL?",
        "candidate_functionals": candidates,
        "pt_symmetry_result": {
            "PT_requires_even_or_paired_chi_sector": True,
            "PT_alone_selects_chi_sign_pair": True,
            "PT_alone_selects_nonzero_magnitude": False,
            "chi_zero_is_stationary_for_even_functional": True,
            "chi_zero_rejected_if_bridge_source_required": True,
        },
        "minimal_nonzero_chi_requires_one_of": [
            "derived boundary charge Q_PT",
            "derived flux unit q_LL on compact worldvolume cycle",
            "derived scale chi0 from LL gauge action",
            "derived potential V(chi) with nonzero minimum",
        ],
        "chi_LL_selected_no_fit": False,
        "best_next_after_this": "LL_auxiliary_flux_quantizes_chi",
        "why": (
            "PT symmetry constrains sign/orientation and can pair sectors, but it does "
            "not set a nonzero magnitude. To get magnitude without observation, the "
            "next hard object must be a charge/flux/action scale."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus PT Boundary chi_LL Stationarity Gate",
        "",
        f"Question: {payload['question']}",
        f"chi_LL selected no-fit: `{payload['chi_LL_selected_no_fit']}`",
        f"Best next: `{payload['best_next_after_this']}`",
        "",
        "## Candidate Functionals",
        "",
        "| Candidate | Selects nonzero chi | Reason |",
        "|---|---:|---|",
        *[
            f"| `{row['id']}` | `{row['selects_nonzero_chi']}` | {row['reason']} |"
            for row in payload["candidate_functionals"]
        ],
        "",
        "## Minimal Nonzero chi Requires",
        "",
        *[f"- {item}" for item in payload["minimal_nonzero_chi_requires_one_of"]],
        "",
        payload["why"],
    ]
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
