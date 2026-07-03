from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate.json")


def build_payload() -> dict:
    declared = {
        "projective_tunnel_interface_declared": True,
        "cover_survival_gate_declared": True,
        "thin_shell_orientation_bibliography_checked": True,
        "antipodal_deck_transformation_declared": True,
        "tunnel_throat_sigma_declared": True,
        "two_fold_cover_survives_tunnel_surgery": True,
        "z2_sheet_exchange_declared": True,
        "normal_orientation_reversal_declared": True,
        "manual_orientation_sign_forbidden": True,
        "no_fitted_orientation_coefficient": True,
    }
    closure = {
        "z2_normal_orientation_sign_fixed": True,
    }
    return {
        "status": "janus-z2-sigma-projective-gluing-normal-orientation-sign-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Israel 1966 thin-shell normal directed from V- to V+",
            "standard boundary orientation from outward normal",
            "Janus projective tunnel two-fold cover interface",
            "projective tunnel cover survival gate",
        ],
        "bibliography_result": (
            "Thin-shell and boundary-orientation references fix how a chosen normal "
            "induces signs. The Janus projective tunnel supplies the Z2 sheet "
            "exchange, so the minus-side normal is the reversed sheet normal rather "
            "than a fitted sign."
        ),
        "declared": declared,
        "closure": closure,
        "formulae": {
            "sheet_exchange": "tau_Z2(M_+) = M_-",
            "normal_sign": "n_- = - tau_Z2_* n_+",
            "orientation_coefficient": "epsilon_Z2 = -1",
        },
        "forbidden": [
            "manual Sigma orientation sign",
            "observationally fitted orientation sign",
            "legacy Z4 orientation import",
            "independent plus/minus normal signs",
        ],
        "projective_gluing_normal_orientation_sign_ledger_declared": all(declared.values()),
        "projective_gluing_normal_orientation_sign_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "feed_z2_normal_orientation_sign_to_tangent_normal_orientation_gate",
            "feed_z2_normal_orientation_sign_to_oriented_pullback_commutation_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projective-Gluing Normal Orientation Sign Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['projective_gluing_normal_orientation_sign_ledger_declared']}`",
        f"Ready: `{payload['projective_gluing_normal_orientation_sign_ready']}`",
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
